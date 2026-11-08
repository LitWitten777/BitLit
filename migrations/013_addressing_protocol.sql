-- ============================================================================
-- Categorical Ledger — Migration 013: Addressing Protocol (AddressV2)
-- ============================================================================
-- AddressV2 extends AddressV1 with path_signature, multi-scale coords, trust
-- hints and routing hints.  The schema is the payload that
-- qbx.path.signature.PathSignature.build hashes (qbx.addressing.address):
--   {"version": 2, "universe_id": uuid text, "artifact_id": null | uuid text,
--    "path_signature": non-empty hex text, "coords": hex text,
--    "coords_scale": uint, "semantic_tags": [hex text],
--    "trust_hint": {"trust_score": float in [0, 1], "verification_depth": uint},
--    "routing_hint": null | {text: text}, "timestamp": uint,
--    "nonce": 32 hex digits}
-- encoded as deterministic CBOR (qbx.core.canonical.canonical_cbor) and hashed
-- with qbx.core.hashing.pq_hash (hash_algo SHA3-256 by default; SHA3-512,
-- SHA-256, PQ-HASH-1).  "hex text" is lowercase with an even number of digits.
--
-- Recording.
--   address_registry  one row per address: its hash, its CBOR bytes, the hash
--                     algorithm, pointers (a JSON array of distinct non-empty
--                     locator strings).  trust_score / verification_depth
--                     repeat the address's trust hint (filled from it when
--                     omitted).  The address itself (hash, CBOR, algorithm,
--                     owner) never changes once written.
--   address_cache     resolutions learnt from elsewhere: pointers valid for
--                     ttl seconds from cached_at.
--   gateway_mapping   an IP endpoint ("a.b.c.d", "a.b.c.d:port", an IPv6
--                     address, or "[v6]:port") serving a registered address
--                     over a protocol (tcp, udp, quic, http, https, ws, wss).
--   dht_node          a DHT node: a 256-bit (32-byte) node id.
--   discovery_log     a k-nearest discovery query and its results.
--   address_violation the violation table (subject_table, subject_id,
--                     address_hash, reason, details).
--
-- Checks.  Every check logs to address_violation and raises only when
-- qbx.enforcement_mode = 'strict'.  Rows are checked when written (triggers)
-- and in batch (check_address, check_addressing, run_all_batch_checks).
--   address_registry (addr_registry_problems, check_address)
--     address_hash_format   hash_algo is not a supported algorithm, or the hash
--                           is not a digest of that algorithm (details: algo)
--     address_hash_mismatch the hash is not pq_hash(address_cbor, hash_algo)
--                           (details: algo) — recomputed here, SHA3 included
--     cbor_malformed        the bytes are not one deterministic-CBOR item of
--                           the supported subset; decoding stops (details:
--                           offset, error ∈ truncated, reserved_info,
--                           indefinite_length, invalid_utf8, unsupported_tag,
--                           unsupported_simple, trailing_bytes, non_text_key,
--                           duplicate_key, too_deep)
--     cbor_non_canonical    one per departure from the deterministic encoding
--                           (details: offset, error ∈ non_minimal_head,
--                           unsorted_keys, non_shortest_float, non_nfc_text)
--     address_schema        one per schema violation (details: field, error ∈
--                           not_a_map, missing, unknown, type, value, format,
--                           range, element)
--     trust_mismatch        trust_score / verification_depth differ from a valid
--                           trust hint (details: column)
--     pointer_typing        pointers is not an array of distinct non-empty
--                           strings (details: error ∈ not_array, element,
--                           duplicate)
--   address_cache   cache_typing (details: error ∈ hash_format, ttl, pointers)
--   gateway_mapping gateway_typing (details: error ∈ endpoint, protocol),
--                   gateway_unregistered (no registry row for the hash)
--   dht_node        dht_typing (details: error = node_id)
--   discovery_log   discovery_typing (details: error ∈ k, latency, results)
--
-- Resolution and routing.
--   resolve_address(hash, at)   the registry's pointers if the address is
--                               registered, else the newest cache entry valid
--                               at `at` (cached_at <= at < cached_at + ttl),
--                               else NULL.
--   purge_expired_cache(at)     deletes the entries no longer valid at `at`.
--   addr_xor, addr_bucket       XOR distance of equal-length ids and its bucket
--                               (index of the highest differing bit; NULL for
--                               equal ids).
--   address_dht_key(hash)       SHA3-256 of the hash text: the DHT key.
--   dht_closest_nodes(key, k)   the k nodes closest to key, nearest first.
--
-- Formal backing (Formal/Addressing.lean): the XOR distance is a metric
-- (xorDist_triangle) in which each distance from a point is attained once
-- (xorDist_unidirectional), the bucket index is an ultrametric
-- (bucket_ultrametric), the k closest nodes exist and are unique
-- (kClosest_exists, kClosest_unique), and comparing bytewise XORs as BYTEA
-- compares XOR distances (bytea_xor_order) — so ORDER BY addr_xor(...) is the
-- XOR-distance order and dht_closest_nodes does not depend on tie-breaking.
--
-- Phase 1 sprint 10 rewrite.  Running the original on PostgreSQL 16 showed:
--   * register_address on an existing hash replaced its pointers (dropping the
--     old ones), trust score and verification depth, silently ignored the new
--     CBOR, and never checked that the hash is the hash of the CBOR or that
--     the CBOR is an AddressV2 (a hash 'h' over the byte 00 was accepted);
--   * trust scores and verification depths of any value (e.g. -7) were
--     accepted, and nothing compared them with the address's own trust hint;
--   * a cache entry with ttl <= 0 and pointers of any shape for a string that
--     is not a hash was accepted, and nothing resolved an address (a cache
--     entry was never read);
--   * gateways were accepted for unregistered addresses and with any text as
--     the endpoint and protocol;
--   * DHT node ids of any length were accepted, and nothing computed XOR
--     distances, buckets or closest nodes;
--   * nothing was checked, logged, or part of run_all_batch_checks.
-- ============================================================================

CREATE TABLE IF NOT EXISTS address_registry (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  address_hash TEXT NOT NULL UNIQUE,
  address_cbor BYTEA NOT NULL,
  owner_pubkey BYTEA,
  pointers JSONB DEFAULT '[]'::jsonb,
  trust_score DOUBLE PRECISION,
  verification_depth INT,
  created_at TIMESTAMPTZ DEFAULT now(),
  metadata JSONB DEFAULT '{}'::jsonb
);
ALTER TABLE address_registry ADD COLUMN IF NOT EXISTS hash_algo TEXT NOT NULL DEFAULT 'SHA3-256';
ALTER TABLE address_registry ALTER COLUMN trust_score DROP DEFAULT;
ALTER TABLE address_registry ALTER COLUMN verification_depth DROP DEFAULT;

CREATE INDEX IF NOT EXISTS idx_address_registry_trust
  ON address_registry (trust_score DESC);

CREATE TABLE IF NOT EXISTS dht_node (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  node_id BYTEA NOT NULL UNIQUE,
  endpoint TEXT,
  capacity JSONB DEFAULT '{}'::jsonb,
  last_seen TIMESTAMPTZ DEFAULT now()
);
ALTER TABLE dht_node ADD COLUMN IF NOT EXISTS created_at TIMESTAMPTZ DEFAULT now();

CREATE TABLE IF NOT EXISTS address_cache (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  address_hash TEXT NOT NULL,
  pointers JSONB NOT NULL,
  ttl INT NOT NULL,
  cached_at TIMESTAMPTZ DEFAULT now(),
  source TEXT
);
ALTER TABLE address_cache ADD COLUMN IF NOT EXISTS created_at TIMESTAMPTZ DEFAULT now();

CREATE INDEX IF NOT EXISTS idx_address_cache_hash
  ON address_cache (address_hash, cached_at DESC);

CREATE TABLE IF NOT EXISTS gateway_mapping (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  address_hash TEXT NOT NULL,
  ip_endpoint TEXT,
  protocol TEXT,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_gateway_mapping_hash
  ON gateway_mapping (address_hash);

CREATE TABLE IF NOT EXISTS discovery_log (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  query_vector vector(1536),
  k INT,
  results JSONB,
  latency_ms INT,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS address_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  subject_table TEXT NOT NULL,
  subject_id UUID,
  address_hash TEXT,
  reason TEXT NOT NULL,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_address_violation_subject
  ON address_violation (subject_table, subject_id, detected_at DESC);

-- The original writer had another signature; drop it so calls are not ambiguous.
DROP FUNCTION IF EXISTS register_address(TEXT, BYTEA, BYTEA, JSONB, DOUBLE PRECISION, INT);

-- ---------------------------------------------------------------------------
-- Hashing: SHA3-256 / SHA3-512 (FIPS 202) in PL/pgSQL, so that the database
-- can recompute qbx.core.hashing.pq_hash without pgcrypto.  Lanes are BIGINT
-- (two's complement); every shift is masked so that it acts on 64 bits.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION addr_rotl64(x BIGINT, n INT) RETURNS BIGINT AS $$
  SELECT CASE WHEN n = 0 THEN x
              ELSE (x << n) | ((x >> (64 - n)) & ~((-1)::bigint << n)) END
$$ LANGUAGE sql IMMUTABLE STRICT;

CREATE OR REPLACE FUNCTION addr_keccak_f(st BIGINT[]) RETURNS BIGINT[] AS $$
DECLARE
  rc CONSTANT BIGINT[] := ARRAY[
    1, 32898, -9223372036854742902, -9223372034707259392, 32907, 2147483649,
    -9223372034707259263, -9223372036854743031, 138, 136, 2147516425, 2147483658,
    2147516555, -9223372036854775669, -9223372036854742903, -9223372036854743037,
    -9223372036854743038, -9223372036854775680, 32778, -9223372034707292150,
    -9223372034707259263, -9223372036854742912, 2147483649, -9223372034707259384]::bigint[];
  -- rotation offset of lane x + 5y (1-based arrays: index x + 5y + 1)
  rot CONSTANT INT[] := ARRAY[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
                              41, 45, 15, 21, 8, 18, 2, 61, 56, 14];
  a BIGINT[] := st;
  b BIGINT[] := array_fill(0::bigint, ARRAY[25]);
  c BIGINT[] := array_fill(0::bigint, ARRAY[5]);
  d BIGINT[] := array_fill(0::bigint, ARRAY[5]);
  r INT; x INT; y INT;
BEGIN
  FOR r IN 1..24 LOOP
    -- theta
    FOR x IN 0..4 LOOP
      c[x + 1] := a[x + 1] # a[x + 6] # a[x + 11] # a[x + 16] # a[x + 21];
    END LOOP;
    FOR x IN 0..4 LOOP
      d[x + 1] := c[(x + 4) % 5 + 1] # addr_rotl64(c[(x + 1) % 5 + 1], 1);
    END LOOP;
    FOR x IN 0..4 LOOP
      FOR y IN 0..4 LOOP
        a[x + 5 * y + 1] := a[x + 5 * y + 1] # d[x + 1];
      END LOOP;
    END LOOP;
    -- rho and pi: B[y, 2x + 3y] = rot(A[x, y], r[x, y])
    FOR x IN 0..4 LOOP
      FOR y IN 0..4 LOOP
        b[y + 5 * ((2 * x + 3 * y) % 5) + 1] := addr_rotl64(a[x + 5 * y + 1], rot[x + 5 * y + 1]);
      END LOOP;
    END LOOP;
    -- chi
    FOR x IN 0..4 LOOP
      FOR y IN 0..4 LOOP
        a[x + 5 * y + 1] := b[x + 5 * y + 1]
                            # ((~b[(x + 1) % 5 + 5 * y + 1]) & b[(x + 2) % 5 + 5 * y + 1]);
      END LOOP;
    END LOOP;
    -- iota
    a[1] := a[1] # rc[r];
  END LOOP;
  RETURN a;
END;
$$ LANGUAGE plpgsql IMMUTABLE STRICT;

-- SHA3 with output length p_bits (256 or 512).
CREATE OR REPLACE FUNCTION addr_sha3(p_data BYTEA, p_bits INT) RETURNS BYTEA AS $$
DECLARE
  rate INT := 200 - 2 * (p_bits / 8);
  msg BYTEA;
  st BIGINT[] := array_fill(0::bigint, ARRAY[25]);
  n INT;
  blk INT; i INT; j INT;
  lane BIGINT;
  out BYTEA := ''::bytea;
BEGIN
  IF p_bits NOT IN (256, 512) THEN
    RAISE EXCEPTION 'addr_sha3: unsupported output length %', p_bits;
  END IF;
  -- pad10*1 with the SHA3 domain bits 01
  n := rate - (octet_length(p_data) % rate);
  msg := p_data || '\x06'::bytea || decode(repeat('00', n - 1), 'hex');
  msg := set_byte(msg, octet_length(msg) - 1, get_byte(msg, octet_length(msg) - 1) | 128);
  FOR blk IN 0..(octet_length(msg) / rate) - 1 LOOP
    FOR i IN 0..(rate / 8) - 1 LOOP
      lane := 0;
      FOR j IN 0..7 LOOP
        lane := lane | (get_byte(msg, blk * rate + 8 * i + j)::bigint << (8 * j));
      END LOOP;
      st[i + 1] := st[i + 1] # lane;
    END LOOP;
    st := addr_keccak_f(st);
  END LOOP;
  FOR i IN 0..(p_bits / 64) - 1 LOOP
    FOR j IN 0..7 LOOP
      out := out || set_byte('\x00'::bytea, 0, ((st[i + 1] >> (8 * j)) & 255)::int);
    END LOOP;
  END LOOP;
  RETURN out;
END;
$$ LANGUAGE plpgsql IMMUTABLE STRICT;

-- qbx.core.hashing.pq_hash: the hex digest for algo, NULL for an unknown algo.
CREATE OR REPLACE FUNCTION addr_pq_hash(p_data BYTEA, p_algo TEXT) RETURNS TEXT AS $$
  SELECT CASE upper(p_algo)
           WHEN 'SHA3-256' THEN encode(addr_sha3(p_data, 256), 'hex')
           WHEN 'SHA3-512' THEN encode(addr_sha3(p_data, 512), 'hex')
           WHEN 'SHA-256' THEN encode(sha256(p_data), 'hex')
           WHEN 'PQ-HASH-1' THEN 'PQ1:' || encode(addr_sha3(p_data, 512), 'hex')
         END
$$ LANGUAGE sql IMMUTABLE STRICT;

-- ---------------------------------------------------------------------------
-- Strict deterministic-CBOR decoder (the subset qbx.core.canonical.canonical_cbor
-- produces).  The decoded value is JSONB, tagged so that nothing is lost:
--   unsigned / negative integer  JSON number
--   text string                  JSON string
--   byte string                  {"$bytes": "<hex>"}
--   float (half/single/double)   {"$float": "<float8 text>"} (e.g. "0.5", "-0", "NaN",
--                                "Infinity"; cast with ::double precision)
--   array                        JSON array
--   map (text keys only)         {"$map": {key: value, ...}}
--   false / true / null          JSON false / true / null
-- A malformed input stops the decoder (one 'cbor_malformed' problem); every
-- departure from the deterministic encoding is collected ('cbor_non_canonical').
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION addr_cbor_fail(p_offset INT, p_error TEXT) RETURNS VOID AS $$
BEGIN
  RAISE EXCEPTION USING ERRCODE = 'QXCBR', MESSAGE = p_error, DETAIL = p_offset::text;
END;
$$ LANGUAGE plpgsql;

-- Can the finite float m·2^e (m > 0) be written exactly with p significant
-- bits, minimum normal exponent emin and maximum exponent emax?
CREATE OR REPLACE FUNCTION addr_float_fits(p_m NUMERIC, p_e INT, p_p INT, p_emin INT, p_emax INT)
RETURNS BOOLEAN AS $$
DECLARE
  m NUMERIC := p_m;
  e INT := p_e;
  bl INT := 0;
  t NUMERIC;
BEGIN
  WHILE mod(m, 2) = 0 LOOP
    m := div(m, 2); e := e + 1;
  END LOOP;
  t := m;
  WHILE t > 0 LOOP
    t := div(t, 2); bl := bl + 1;
  END LOOP;
  RETURN bl <= p_p AND e >= p_emin - p_p + 1 AND e + bl - 1 <= p_emax;
END;
$$ LANGUAGE plpgsql IMMUTABLE STRICT;

-- Decode a float of width 16 / 32 / 64 from its bits; returns
-- {"v": tagged value, "canonical": bool} (canonical: no narrower width holds it).
CREATE OR REPLACE FUNCTION addr_cbor_float(p_bits NUMERIC, p_width INT) RETURNS JSONB AS $$
DECLARE
  eb INT; fb INT; bias INT;
  sgn INT; ex INT; fr NUMERIC;
  m NUMERIC; e INT;
  v DOUBLE PRECISION;
  canon BOOLEAN;
BEGIN
  eb := CASE p_width WHEN 16 THEN 5 WHEN 32 THEN 8 ELSE 11 END;
  fb := CASE p_width WHEN 16 THEN 10 WHEN 32 THEN 23 ELSE 52 END;
  bias := (2::numeric ^ (eb - 1))::int - 1;
  sgn := div(p_bits, 2::numeric ^ (p_width - 1))::int;
  ex := mod(div(p_bits, 2::numeric ^ fb), 2::numeric ^ eb)::int;
  fr := mod(p_bits, 2::numeric ^ fb);
  IF ex = (2::numeric ^ eb)::int - 1 THEN
    RETURN jsonb_build_object('v', jsonb_build_object('$float',
             CASE WHEN fr <> 0 THEN 'NaN' WHEN sgn = 1 THEN '-Infinity' ELSE 'Infinity' END),
           'canonical', p_width = 16);
  END IF;
  IF ex = 0 THEN
    m := fr; e := 1 - bias - fb;
  ELSE
    m := fr + 2::numeric ^ fb; e := ex - bias - fb;
  END IF;
  IF m = 0 THEN
    v := 0;
    canon := p_width = 16;
  ELSE
    v := m::double precision * power(2::double precision, e);
    canon := p_width = 16
             OR (p_width = 32 AND NOT addr_float_fits(m, e, 11, -14, 15))
             OR (p_width = 64 AND NOT addr_float_fits(m, e, 11, -14, 15)
                              AND NOT addr_float_fits(m, e, 24, -126, 127));
  END IF;
  IF sgn = 1 THEN v := -v; END IF;
  RETURN jsonb_build_object('v', jsonb_build_object('$float', v::text), 'canonical', canon);
END;
$$ LANGUAGE plpgsql IMMUTABLE STRICT;

-- Decode the item at p_pos (0-based).  Returns {"v": value, "pos": next
-- position, "nc": [non-canonical findings]}; raises QXCBR when malformed.
CREATE OR REPLACE FUNCTION addr_cbor_item(p_data BYTEA, p_pos INT, p_depth INT)
RETURNS JSONB AS $$
DECLARE
  n INT := octet_length(p_data);
  o INT := p_pos;
  pos INT := p_pos;
  ib INT; mt INT; ai INT;
  arg NUMERIC := 0;
  k INT; i NUMERIC;
  nc JSONB := '[]'::jsonb;
  sub JSONB;
  fl JSONB;
  items JSONB;
  txt TEXT;
  ko INT;
  kraw BYTEA;
  prev BYTEA;
  obj JSONB;
BEGIN
  IF p_depth > 16 THEN PERFORM addr_cbor_fail(o, 'too_deep'); END IF;
  IF pos >= n THEN PERFORM addr_cbor_fail(o, 'truncated'); END IF;
  ib := get_byte(p_data, pos);
  mt := ib >> 5;
  ai := ib & 31;
  pos := pos + 1;
  IF ai BETWEEN 28 AND 30 THEN PERFORM addr_cbor_fail(o, 'reserved_info'); END IF;
  IF ai = 31 THEN PERFORM addr_cbor_fail(o, 'indefinite_length'); END IF;
  IF ai < 24 THEN
    arg := ai;
  ELSE
    k := CASE ai WHEN 24 THEN 1 WHEN 25 THEN 2 WHEN 26 THEN 4 ELSE 8 END;
    IF pos + k > n THEN PERFORM addr_cbor_fail(o, 'truncated'); END IF;
    FOR j IN 0..k - 1 LOOP
      arg := arg * 256 + get_byte(p_data, pos + j);
    END LOOP;
    pos := pos + k;
  END IF;

  IF mt = 7 THEN
    IF ai = 20 THEN RETURN jsonb_build_object('v', false, 'pos', pos, 'nc', nc); END IF;
    IF ai = 21 THEN RETURN jsonb_build_object('v', true, 'pos', pos, 'nc', nc); END IF;
    IF ai = 22 THEN RETURN jsonb_build_object('v', 'null'::jsonb, 'pos', pos, 'nc', nc); END IF;
    IF ai IN (25, 26, 27) THEN
      fl := addr_cbor_float(arg, CASE ai WHEN 25 THEN 16 WHEN 26 THEN 32 ELSE 64 END);
      IF NOT (fl ->> 'canonical')::boolean THEN
        nc := nc || jsonb_build_object('offset', o, 'error', 'non_shortest_float');
      END IF;
      RETURN jsonb_build_object('v', fl -> 'v', 'pos', pos, 'nc', nc);
    END IF;
    PERFORM addr_cbor_fail(o, 'unsupported_simple');
  END IF;

  IF (ai = 24 AND arg < 24) OR (ai = 25 AND arg < 256) OR (ai = 26 AND arg < 65536)
     OR (ai = 27 AND arg < 4294967296) THEN
    nc := nc || jsonb_build_object('offset', o, 'error', 'non_minimal_head');
  END IF;

  IF mt = 6 THEN PERFORM addr_cbor_fail(o, 'unsupported_tag'); END IF;
  IF mt = 0 THEN RETURN jsonb_build_object('v', to_jsonb(arg), 'pos', pos, 'nc', nc); END IF;
  IF mt = 1 THEN RETURN jsonb_build_object('v', to_jsonb(-1 - arg), 'pos', pos, 'nc', nc); END IF;

  IF mt IN (2, 3) THEN
    IF arg > n - pos THEN PERFORM addr_cbor_fail(o, 'truncated'); END IF;
    kraw := substring(p_data FROM pos + 1 FOR arg::int);
    pos := pos + arg::int;
    IF mt = 2 THEN
      RETURN jsonb_build_object('v', jsonb_build_object('$bytes', encode(kraw, 'hex')),
                                'pos', pos, 'nc', nc);
    END IF;
    BEGIN
      txt := convert_from(kraw, 'UTF8');
    EXCEPTION WHEN OTHERS THEN
      txt := NULL;
    END;
    IF txt IS NULL THEN PERFORM addr_cbor_fail(o, 'invalid_utf8'); END IF;
    IF NOT (txt IS NFC NORMALIZED) THEN
      nc := nc || jsonb_build_object('offset', o, 'error', 'non_nfc_text');
    END IF;
    RETURN jsonb_build_object('v', to_jsonb(txt), 'pos', pos, 'nc', nc);
  END IF;

  IF mt = 4 THEN
    IF arg > n - pos THEN PERFORM addr_cbor_fail(o, 'truncated'); END IF;
    items := '[]'::jsonb;
    i := 0;
    WHILE i < arg LOOP
      sub := addr_cbor_item(p_data, pos, p_depth + 1);
      items := items || jsonb_build_array(sub -> 'v');
      nc := nc || (sub -> 'nc');
      pos := (sub ->> 'pos')::int;
      i := i + 1;
    END LOOP;
    RETURN jsonb_build_object('v', items, 'pos', pos, 'nc', nc);
  END IF;

  -- mt = 5: a map
  IF 2 * arg > n - pos THEN PERFORM addr_cbor_fail(o, 'truncated'); END IF;
  obj := '{}'::jsonb;
  prev := NULL;
  i := 0;
  WHILE i < arg LOOP
    ko := pos;
    sub := addr_cbor_item(p_data, pos, p_depth + 1);
    nc := nc || (sub -> 'nc');
    pos := (sub ->> 'pos')::int;
    IF jsonb_typeof(sub -> 'v') <> 'string' THEN PERFORM addr_cbor_fail(ko, 'non_text_key'); END IF;
    txt := sub ->> 'v';
    IF obj ? txt THEN PERFORM addr_cbor_fail(ko, 'duplicate_key'); END IF;
    kraw := substring(p_data FROM ko + 1 FOR pos - ko);
    IF prev IS NOT NULL AND (octet_length(kraw) < octet_length(prev)
                             OR (octet_length(kraw) = octet_length(prev) AND kraw < prev)) THEN
      nc := nc || jsonb_build_object('offset', ko, 'error', 'unsorted_keys');
    END IF;
    prev := kraw;
    sub := addr_cbor_item(p_data, pos, p_depth + 1);
    nc := nc || (sub -> 'nc');
    pos := (sub ->> 'pos')::int;
    obj := obj || jsonb_build_object(txt, sub -> 'v');
    i := i + 1;
  END LOOP;
  RETURN jsonb_build_object('v', jsonb_build_object('$map', obj), 'pos', pos, 'nc', nc);
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- Decode a whole input: {"value": v | null, "malformed": {"offset", "error"} | null,
-- "non_canonical": [{"offset", "error"}, ...]}.
CREATE OR REPLACE FUNCTION addr_cbor_decode(p_data BYTEA) RETURNS JSONB AS $$
DECLARE
  r JSONB;
  msg TEXT;
  det TEXT;
BEGIN
  IF p_data IS NULL THEN
    RETURN jsonb_build_object('value', NULL, 'non_canonical', '[]'::jsonb,
                              'malformed', jsonb_build_object('offset', 0, 'error', 'truncated'));
  END IF;
  BEGIN
    r := addr_cbor_item(p_data, 0, 0);
    IF (r ->> 'pos')::int < octet_length(p_data) THEN
      PERFORM addr_cbor_fail((r ->> 'pos')::int, 'trailing_bytes');
    END IF;
  EXCEPTION WHEN SQLSTATE 'QXCBR' THEN
    GET STACKED DIAGNOSTICS msg = MESSAGE_TEXT, det = PG_EXCEPTION_DETAIL;
    RETURN jsonb_build_object('value', NULL, 'non_canonical', '[]'::jsonb,
                              'malformed', jsonb_build_object('offset', det::int, 'error', msg));
  END;
  RETURN jsonb_build_object('value', r -> 'v', 'non_canonical', r -> 'nc', 'malformed', NULL);
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- AddressV2 schema (qbx.addressing.address.schema_problems)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION addr_is_int(j JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(j) = 'number', false)
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_is_text(j JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(j) = 'string', false)
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_is_map(j JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(j) = 'object' AND j ? '$map', false)
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_is_float(j JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(j) = 'object' AND j ? '$float', false)
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_is_null(j JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(j) = 'null', false)
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_matches(j JSONB, p_re TEXT) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(j) = 'string' AND (j #>> '{}') ~ p_re, false)
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_trust_score_ok(j JSONB) RETURNS BOOLEAN AS $$
  SELECT addr_is_float(j) AND (j ->> '$float')::double precision BETWEEN 0 AND 1
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_depth_ok(j JSONB) RETURNS BOOLEAN AS $$
  SELECT addr_is_int(j) AND (j #>> '{}')::numeric >= 0
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_schema_problems(p_value JSONB)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  fields CONSTANT TEXT[] := ARRAY['version', 'universe_id', 'artifact_id', 'path_signature',
                                  'coords', 'coords_scale', 'semantic_tags', 'trust_hint',
                                  'routing_hint', 'timestamp', 'nonce'];
  uuid_re CONSTANT TEXT := '^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$';
  hex_re CONSTANT TEXT := '^([0-9a-f]{2})*$';
  m JSONB;
  t JSONB;
  k TEXT;
  f JSONB;
BEGIN
  reason := 'address_schema';
  IF NOT addr_is_map(p_value) THEN
    details := jsonb_build_object('field', '', 'error', 'not_a_map'); RETURN NEXT;
    RETURN;
  END IF;
  m := p_value -> '$map';
  FOREACH k IN ARRAY fields LOOP
    IF NOT m ? k THEN
      details := jsonb_build_object('field', k, 'error', 'missing'); RETURN NEXT;
    END IF;
  END LOOP;
  FOR k IN SELECT jsonb_object_keys(m) LOOP
    IF NOT k = ANY (fields) THEN
      details := jsonb_build_object('field', k, 'error', 'unknown'); RETURN NEXT;
    END IF;
  END LOOP;

  -- (field, type ok, value ok, value error)
  FOR k, details IN
    SELECT x.fname,
           CASE WHEN NOT x.type_ok THEN jsonb_build_object('field', x.fname, 'error', 'type')
                WHEN NOT x.value_ok THEN jsonb_build_object('field', x.fname, 'error', x.verr)
           END
      FROM (VALUES
        ('version', addr_is_int(m -> 'version'),
                    addr_is_int(m -> 'version') AND (m ->> 'version')::numeric = 2, 'value'),
        ('universe_id', addr_is_text(m -> 'universe_id'),
                        addr_matches(m -> 'universe_id', uuid_re), 'format'),
        ('artifact_id', addr_is_null(m -> 'artifact_id') OR addr_is_text(m -> 'artifact_id'),
                        addr_is_null(m -> 'artifact_id') OR addr_matches(m -> 'artifact_id', uuid_re),
                        'format'),
        ('path_signature', addr_is_text(m -> 'path_signature'),
                           addr_matches(m -> 'path_signature', '^([0-9a-f]{2})+$'), 'format'),
        ('coords', addr_is_text(m -> 'coords'), addr_matches(m -> 'coords', hex_re), 'format'),
        ('coords_scale', addr_is_int(m -> 'coords_scale'), addr_depth_ok(m -> 'coords_scale'),
                         'range'),
        ('semantic_tags', coalesce(jsonb_typeof(m -> 'semantic_tags') = 'array', false),
                          coalesce(jsonb_typeof(m -> 'semantic_tags') = 'array', false)
                          AND NOT EXISTS (
                            SELECT 1 FROM jsonb_array_elements(
                                     CASE WHEN jsonb_typeof(m -> 'semantic_tags') = 'array'
                                          THEN m -> 'semantic_tags' ELSE '[]'::jsonb END) e
                             WHERE NOT addr_matches(e, hex_re)), 'element'),
        ('routing_hint', addr_is_null(m -> 'routing_hint') OR addr_is_map(m -> 'routing_hint'),
                         addr_is_null(m -> 'routing_hint')
                         OR (addr_is_map(m -> 'routing_hint') AND NOT EXISTS (
                               SELECT 1 FROM jsonb_each(m -> 'routing_hint' -> '$map') e
                                WHERE NOT addr_is_text(e.value))), 'element'),
        ('timestamp', addr_is_int(m -> 'timestamp'), addr_depth_ok(m -> 'timestamp'), 'range'),
        ('nonce', addr_is_text(m -> 'nonce'), addr_matches(m -> 'nonce', '^[0-9a-f]{32}$'),
                  'format')
      ) AS x(fname, type_ok, value_ok, verr)
     WHERE m ? x.fname
  LOOP
    IF details IS NOT NULL THEN RETURN NEXT; END IF;
  END LOOP;

  IF m ? 'trust_hint' THEN
    t := m -> 'trust_hint';
    IF NOT addr_is_map(t) THEN
      details := jsonb_build_object('field', 'trust_hint', 'error', 'type'); RETURN NEXT;
    ELSE
      t := t -> '$map';
      FOREACH k IN ARRAY ARRAY['trust_score', 'verification_depth'] LOOP
        IF NOT t ? k THEN
          details := jsonb_build_object('field', 'trust_hint.' || k, 'error', 'missing');
          RETURN NEXT;
        END IF;
      END LOOP;
      FOR k IN SELECT jsonb_object_keys(t) LOOP
        IF k NOT IN ('trust_score', 'verification_depth') THEN
          details := jsonb_build_object('field', 'trust_hint.' || k, 'error', 'unknown');
          RETURN NEXT;
        END IF;
      END LOOP;
      IF t ? 'trust_score' THEN
        f := t -> 'trust_score';
        IF NOT addr_is_float(f) THEN
          details := jsonb_build_object('field', 'trust_hint.trust_score', 'error', 'type');
          RETURN NEXT;
        ELSIF NOT addr_trust_score_ok(f) THEN
          details := jsonb_build_object('field', 'trust_hint.trust_score', 'error', 'range');
          RETURN NEXT;
        END IF;
      END IF;
      IF t ? 'verification_depth' THEN
        f := t -> 'verification_depth';
        IF NOT addr_is_int(f) THEN
          details := jsonb_build_object('field', 'trust_hint.verification_depth', 'error', 'type');
          RETURN NEXT;
        ELSIF NOT addr_depth_ok(f) THEN
          details := jsonb_build_object('field', 'trust_hint.verification_depth', 'error', 'range');
          RETURN NEXT;
        END IF;
      END IF;
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- The valid trust hint of a decoded value: {"trust_score": float8 | null,
-- "verification_depth": int | null}.
CREATE OR REPLACE FUNCTION addr_trust_hint(p_value JSONB) RETURNS JSONB AS $$
DECLARE
  t JSONB;
BEGIN
  IF NOT addr_is_map(p_value) OR NOT addr_is_map(p_value -> '$map' -> 'trust_hint') THEN
    RETURN jsonb_build_object('trust_score', NULL, 'verification_depth', NULL);
  END IF;
  t := p_value -> '$map' -> 'trust_hint' -> '$map';
  RETURN jsonb_build_object(
    'trust_score', CASE WHEN addr_trust_score_ok(t -> 'trust_score')
                        THEN t -> 'trust_score' -> '$float' END,
    'verification_depth', CASE WHEN addr_depth_ok(t -> 'verification_depth')
                               THEN t -> 'verification_depth' END);
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- Hash format for an algorithm.
CREATE OR REPLACE FUNCTION addr_hash_format_ok(p_hash TEXT, p_algo TEXT) RETURNS BOOLEAN AS $$
  SELECT coalesce(CASE p_algo
           WHEN 'SHA3-256' THEN p_hash ~ '^[0-9a-f]{64}$'
           WHEN 'SHA-256' THEN p_hash ~ '^[0-9a-f]{64}$'
           WHEN 'SHA3-512' THEN p_hash ~ '^[0-9a-f]{128}$'
           WHEN 'PQ-HASH-1' THEN p_hash ~ '^PQ1:[0-9a-f]{128}$'
         END, false)
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_is_address_hash(p_hash TEXT) RETURNS BOOLEAN AS $$
  SELECT addr_hash_format_ok(p_hash, 'SHA3-256') OR addr_hash_format_ok(p_hash, 'SHA3-512')
      OR addr_hash_format_ok(p_hash, 'PQ-HASH-1')
$$ LANGUAGE sql IMMUTABLE;

-- Every problem of an address (qbx.addressing.address.address_problems).
CREATE OR REPLACE FUNCTION addr_address_problems(
  p_cbor BYTEA, p_hash TEXT, p_algo TEXT,
  p_trust DOUBLE PRECISION, p_depth INT, p_check_trust BOOLEAN DEFAULT TRUE
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  d JSONB;
  th JSONB;
  e JSONB;
BEGIN
  IF NOT addr_hash_format_ok(p_hash, p_algo) THEN
    reason := 'address_hash_format'; details := jsonb_build_object('algo', p_algo); RETURN NEXT;
  ELSIF p_cbor IS NULL OR addr_pq_hash(p_cbor, p_algo) IS DISTINCT FROM p_hash THEN
    reason := 'address_hash_mismatch'; details := jsonb_build_object('algo', p_algo); RETURN NEXT;
  END IF;
  d := addr_cbor_decode(p_cbor);
  IF d -> 'malformed' <> 'null'::jsonb THEN
    reason := 'cbor_malformed'; details := d -> 'malformed'; RETURN NEXT;
    RETURN;
  END IF;
  FOR e IN SELECT * FROM jsonb_array_elements(d -> 'non_canonical') LOOP
    reason := 'cbor_non_canonical'; details := e; RETURN NEXT;
  END LOOP;
  RETURN QUERY SELECT * FROM addr_schema_problems(d -> 'value');
  IF p_check_trust THEN
    th := addr_trust_hint(d -> 'value');
    IF th -> 'trust_score' <> 'null'::jsonb
       AND p_trust IS DISTINCT FROM (th ->> 'trust_score')::double precision THEN
      reason := 'trust_mismatch'; details := jsonb_build_object('column', 'trust_score');
      RETURN NEXT;
    END IF;
    IF th -> 'verification_depth' <> 'null'::jsonb
       AND p_depth::numeric IS DISTINCT FROM (th ->> 'verification_depth')::numeric THEN
      reason := 'trust_mismatch'; details := jsonb_build_object('column', 'verification_depth');
      RETURN NEXT;
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Problems of the rows of each table
-- ---------------------------------------------------------------------------
-- pointers: a JSON array of distinct non-empty strings.
CREATE OR REPLACE FUNCTION addr_pointer_problems(p_pointers JSONB)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  reason := 'pointer_typing';
  IF p_pointers IS NULL OR jsonb_typeof(p_pointers) <> 'array' THEN
    details := jsonb_build_object('error', 'not_array'); RETURN NEXT;
  ELSIF EXISTS (SELECT 1 FROM jsonb_array_elements(p_pointers) e
                 WHERE jsonb_typeof(e) <> 'string' OR e = '""'::jsonb) THEN
    details := jsonb_build_object('error', 'element'); RETURN NEXT;
  ELSIF (SELECT count(DISTINCT e) <> count(*) FROM jsonb_array_elements(p_pointers) e) THEN
    details := jsonb_build_object('error', 'duplicate'); RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_registry_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT a.* INTO r FROM address_registry a WHERE a.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM addr_address_problems(r.address_cbor, r.address_hash, r.hash_algo,
                                                   r.trust_score, r.verification_depth);
  RETURN QUERY SELECT * FROM addr_pointer_problems(r.pointers);
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION addr_cache_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT c.* INTO r FROM address_cache c WHERE c.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  reason := 'cache_typing';
  IF NOT addr_is_address_hash(r.address_hash) THEN
    details := jsonb_build_object('error', 'hash_format'); RETURN NEXT;
  END IF;
  IF r.ttl IS NULL OR r.ttl <= 0 THEN
    details := jsonb_build_object('error', 'ttl'); RETURN NEXT;
  END IF;
  IF EXISTS (SELECT 1 FROM addr_pointer_problems(r.pointers)) THEN
    details := jsonb_build_object('error', 'pointers'); RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- An IP endpoint: "a.b.c.d", "a.b.c.d:port", an IPv6 address, or "[v6]:port".
CREATE OR REPLACE FUNCTION addr_endpoint_ok(p_endpoint TEXT) RETURNS BOOLEAN AS $$
DECLARE
  m TEXT[];
  host TEXT;
  port TEXT;
  fam INT;
  v INET;
BEGIN
  IF p_endpoint IS NULL OR p_endpoint ~ '[%/[:space:]]' THEN RETURN FALSE; END IF;
  m := regexp_match(p_endpoint, '^\[([^]]*)\]:([0-9]+)$');
  IF m IS NOT NULL THEN
    host := m[1]; port := m[2]; fam := 6;
  ELSE
    m := regexp_match(p_endpoint, '^([0-9.]+):([0-9]+)$');
    IF m IS NOT NULL THEN
      host := m[1]; port := m[2]; fam := 4;
    ELSE
      host := p_endpoint;
    END IF;
  END IF;
  IF port IS NOT NULL AND NOT (port ~ '^[1-9][0-9]{0,4}$' AND port::int <= 65535) THEN
    RETURN FALSE;
  END IF;
  IF position(':' IN host) = 0
     AND host !~ '^(0|[1-9][0-9]{0,2})(\.(0|[1-9][0-9]{0,2})){3}$' THEN
    RETURN FALSE;
  END IF;
  BEGIN
    v := host::inet;
  EXCEPTION WHEN OTHERS THEN
    RETURN FALSE;
  END;
  RETURN fam IS NULL OR family(v) = fam;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION addr_gateway_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT g.* INTO r FROM gateway_mapping g WHERE g.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  IF NOT addr_endpoint_ok(r.ip_endpoint) THEN
    reason := 'gateway_typing'; details := jsonb_build_object('error', 'endpoint'); RETURN NEXT;
  END IF;
  IF r.protocol IS NULL OR r.protocol NOT IN ('tcp', 'udp', 'quic', 'http', 'https', 'ws', 'wss')
  THEN
    reason := 'gateway_typing'; details := jsonb_build_object('error', 'protocol'); RETURN NEXT;
  END IF;
  IF NOT EXISTS (SELECT 1 FROM address_registry a WHERE a.address_hash = r.address_hash) THEN
    reason := 'gateway_unregistered'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION addr_dht_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT d.* INTO r FROM dht_node d WHERE d.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  IF octet_length(r.node_id) <> 32 THEN
    reason := 'dht_typing'; details := jsonb_build_object('error', 'node_id'); RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION addr_discovery_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT d.* INTO r FROM discovery_log d WHERE d.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  reason := 'discovery_typing';
  IF r.k IS NULL OR r.k <= 0 THEN
    details := jsonb_build_object('error', 'k'); RETURN NEXT;
  END IF;
  IF r.latency_ms < 0 THEN
    details := jsonb_build_object('error', 'latency'); RETURN NEXT;
  END IF;
  IF r.results IS NULL OR jsonb_typeof(r.results) <> 'array'
     OR (r.k IS NOT NULL AND jsonb_array_length(r.results) > greatest(r.k, 0)) THEN
    details := jsonb_build_object('error', 'results'); RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION addr_record(p_table TEXT, p_id UUID, p_hash TEXT, p_reason TEXT,
                                       p_details JSONB)
RETURNS VOID AS $$
BEGIN
  INSERT INTO address_violation (subject_table, subject_id, address_hash, reason, details)
  VALUES (p_table, p_id, p_hash, p_reason, coalesce(p_details, '{}'::jsonb));
END;
$$ LANGUAGE plpgsql;

-- The problems function and the hash column of each checked table.
CREATE OR REPLACE FUNCTION addr_problems_of(p_table TEXT, p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  RETURN QUERY EXECUTE format('SELECT * FROM %I($1)',
    CASE p_table
      WHEN 'address_registry' THEN 'addr_registry_problems'
      WHEN 'address_cache' THEN 'addr_cache_problems'
      WHEN 'gateway_mapping' THEN 'addr_gateway_problems'
      WHEN 'dht_node' THEN 'addr_dht_problems'
      WHEN 'discovery_log' THEN 'addr_discovery_problems'
    END) USING p_id;
END;
$$ LANGUAGE plpgsql STABLE;

-- Check one row: log every problem; returns the number of problems.
CREATE OR REPLACE FUNCTION addr_check_row(p_table TEXT, p_id UUID) RETURNS INT AS $$
DECLARE
  pr RECORD;
  v_hash TEXT;
  n INT := 0;
BEGIN
  IF p_table IN ('address_registry', 'address_cache', 'gateway_mapping') THEN
    EXECUTE format('SELECT address_hash FROM %I WHERE id = $1', p_table) INTO v_hash USING p_id;
  END IF;
  FOR pr IN SELECT * FROM addr_problems_of(p_table, p_id) LOOP
    PERFORM addr_record(p_table, p_id, v_hash, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- All checks of one registered address; logs, raises in strict mode.
CREATE OR REPLACE FUNCTION check_address(p_id UUID) RETURNS BOOLEAN AS $$
DECLARE
  n INT;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM address_registry a WHERE a.id = p_id) THEN
    RAISE EXCEPTION 'check_address: address % not found', p_id;
  END IF;
  n := addr_check_row('address_registry', p_id);
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Address % is not a valid AddressV2 registration (% problem(s))', p_id, n;
  END IF;
  RETURN n = 0;
END;
$$ LANGUAGE plpgsql;

-- Every row of every addressing table; logs, raises in strict mode.  Returns
-- the number of problems found.
CREATE OR REPLACE FUNCTION check_addressing() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT := 0;
BEGIN
  FOR t IN SELECT 'address_registry' AS tb, id FROM address_registry
           UNION ALL SELECT 'address_cache', id FROM address_cache
           UNION ALL SELECT 'gateway_mapping', id FROM gateway_mapping
           UNION ALL SELECT 'dht_node', id FROM dht_node
           UNION ALL SELECT 'discovery_log', id FROM discovery_log LOOP
    n := n + addr_check_row(t.tb, t.id);
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Addressing tables have % problem(s)', n;
  END IF;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
-- New registrations: pointers default to [], trust columns to the trust hint.
CREATE OR REPLACE FUNCTION trg_address_fill() RETURNS trigger AS $$
DECLARE
  th JSONB;
BEGIN
  IF NEW.pointers IS NULL THEN NEW.pointers := '[]'::jsonb; END IF;
  IF NEW.trust_score IS NULL OR NEW.verification_depth IS NULL THEN
    th := addr_trust_hint((addr_cbor_decode(NEW.address_cbor)) -> 'value');
    IF NEW.trust_score IS NULL AND th -> 'trust_score' <> 'null'::jsonb THEN
      NEW.trust_score := (th ->> 'trust_score')::double precision;
    END IF;
    IF NEW.verification_depth IS NULL AND th -> 'verification_depth' <> 'null'::jsonb
       AND (th ->> 'verification_depth')::numeric <= 2147483647 THEN
      NEW.verification_depth := (th ->> 'verification_depth')::int;
    END IF;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_address_fill ON address_registry;
CREATE TRIGGER trg_address_fill
BEFORE INSERT ON address_registry
FOR EACH ROW EXECUTE FUNCTION trg_address_fill();

-- An address never changes: its hash, bytes, algorithm and owner are final.
CREATE OR REPLACE FUNCTION trg_address_immutable() RETURNS trigger AS $$
BEGIN
  IF NEW.address_hash IS DISTINCT FROM OLD.address_hash
     OR NEW.address_cbor IS DISTINCT FROM OLD.address_cbor
     OR NEW.hash_algo IS DISTINCT FROM OLD.hash_algo
     OR NEW.owner_pubkey IS DISTINCT FROM OLD.owner_pubkey THEN
    RAISE EXCEPTION 'address % is immutable (hash, CBOR, algorithm and owner cannot change)',
      OLD.address_hash;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_address_immutable ON address_registry;
CREATE TRIGGER trg_address_immutable
BEFORE UPDATE ON address_registry
FOR EACH ROW EXECUTE FUNCTION trg_address_immutable();

-- Generic row check: log, and raise in strict mode.
CREATE OR REPLACE FUNCTION trg_check_address_row() RETURNS trigger AS $$
DECLARE
  n INT;
BEGIN
  n := addr_check_row(TG_TABLE_NAME, NEW.id);
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '% row % is not well formed (% problem(s))', TG_TABLE_NAME, NEW.id, n;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_address_row ON address_registry;
CREATE TRIGGER trg_check_address_row AFTER INSERT OR UPDATE ON address_registry
FOR EACH ROW EXECUTE FUNCTION trg_check_address_row();
DROP TRIGGER IF EXISTS trg_check_address_row ON address_cache;
CREATE TRIGGER trg_check_address_row AFTER INSERT OR UPDATE ON address_cache
FOR EACH ROW EXECUTE FUNCTION trg_check_address_row();
DROP TRIGGER IF EXISTS trg_check_address_row ON gateway_mapping;
CREATE TRIGGER trg_check_address_row AFTER INSERT OR UPDATE ON gateway_mapping
FOR EACH ROW EXECUTE FUNCTION trg_check_address_row();
DROP TRIGGER IF EXISTS trg_check_address_row ON dht_node;
CREATE TRIGGER trg_check_address_row AFTER INSERT OR UPDATE ON dht_node
FOR EACH ROW EXECUTE FUNCTION trg_check_address_row();
DROP TRIGGER IF EXISTS trg_check_address_row ON discovery_log;
CREATE TRIGGER trg_check_address_row AFTER INSERT OR UPDATE ON discovery_log
FOR EACH ROW EXECUTE FUNCTION trg_check_address_row();

-- ---------------------------------------------------------------------------
-- DHT: XOR distance, buckets, closest nodes
-- ---------------------------------------------------------------------------
-- Bytewise XOR of two ids of the same length (NULL otherwise).
CREATE OR REPLACE FUNCTION addr_xor(a BYTEA, b BYTEA) RETURNS BYTEA AS $$
DECLARE
  r BYTEA;
BEGIN
  IF octet_length(a) <> octet_length(b) THEN RETURN NULL; END IF;
  r := a;
  FOR i IN 0..octet_length(a) - 1 LOOP
    r := set_byte(r, i, get_byte(a, i) # get_byte(b, i));
  END LOOP;
  RETURN r;
END;
$$ LANGUAGE plpgsql IMMUTABLE STRICT;

-- Index of the highest bit in which a and b differ (0 = last bit); NULL when
-- they are equal or of different lengths.
CREATE OR REPLACE FUNCTION addr_bucket(a BYTEA, b BYTEA) RETURNS INT AS $$
DECLARE
  d BYTEA := addr_xor(a, b);
  n INT;
  x INT;
BEGIN
  IF d IS NULL THEN RETURN NULL; END IF;
  n := octet_length(d);
  FOR i IN 0..n - 1 LOOP
    x := get_byte(d, i);
    IF x <> 0 THEN
      RETURN 8 * (n - 1 - i) + floor(log(2, x))::int;
    END IF;
  END LOOP;
  RETURN NULL;
END;
$$ LANGUAGE plpgsql IMMUTABLE STRICT;

-- The DHT key of an address: SHA3-256 of its hash text.
CREATE OR REPLACE FUNCTION address_dht_key(p_hash TEXT) RETURNS BYTEA AS $$
  SELECT addr_sha3(convert_to(p_hash, 'UTF8'), 256)
$$ LANGUAGE sql IMMUTABLE STRICT;

-- The k well-formed nodes closest to key (32 bytes), nearest first.  By
-- bytea_xor_order the BYTEA order of the XORs is the XOR-distance order, and
-- by xorDist_unidirectional no two nodes tie.
CREATE OR REPLACE FUNCTION dht_closest_nodes(p_key BYTEA, p_k INT)
RETURNS TABLE(node_id BYTEA, endpoint TEXT, distance BYTEA, bucket INT) AS $$
BEGIN
  IF octet_length(p_key) <> 32 THEN
    RAISE EXCEPTION 'dht_closest_nodes: the key must be 32 bytes, got %', octet_length(p_key);
  END IF;
  IF p_k IS NULL OR p_k < 0 THEN
    RAISE EXCEPTION 'dht_closest_nodes: k must be a non-negative integer';
  END IF;
  RETURN QUERY
    SELECT d.node_id, d.endpoint, addr_xor(d.node_id, p_key), addr_bucket(d.node_id, p_key)
      FROM dht_node d
     WHERE octet_length(d.node_id) = 32
     ORDER BY addr_xor(d.node_id, p_key)
     LIMIT p_k;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION dht_closest_to_address(p_hash TEXT, p_k INT)
RETURNS TABLE(node_id BYTEA, endpoint TEXT, distance BYTEA, bucket INT) AS $$
  SELECT * FROM dht_closest_nodes(address_dht_key(p_hash), p_k)
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Resolution
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION addr_cache_valid_at(p_cached_at TIMESTAMPTZ, p_ttl INT,
                                               p_at TIMESTAMPTZ)
RETURNS BOOLEAN AS $$
  SELECT p_ttl > 0 AND p_cached_at <= p_at AND p_at < p_cached_at + make_interval(secs => p_ttl)
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION resolve_address(p_hash TEXT, p_at TIMESTAMPTZ DEFAULT now())
RETURNS JSONB AS $$
DECLARE
  v JSONB;
BEGIN
  SELECT a.pointers INTO v FROM address_registry a WHERE a.address_hash = p_hash;
  IF FOUND THEN RETURN v; END IF;
  SELECT c.pointers INTO v FROM address_cache c
   WHERE c.address_hash = p_hash AND addr_cache_valid_at(c.cached_at, c.ttl, p_at)
     AND NOT EXISTS (SELECT 1 FROM addr_pointer_problems(c.pointers))
   ORDER BY c.cached_at DESC, c.id
   LIMIT 1;
  RETURN v;
END;
$$ LANGUAGE plpgsql STABLE;

-- Delete the cache entries that are not valid at p_at (expired, or with a
-- non-positive ttl).  Entries cached after p_at are kept.
CREATE OR REPLACE FUNCTION purge_expired_cache(p_at TIMESTAMPTZ DEFAULT now()) RETURNS INT AS $$
DECLARE
  deleted INT;
BEGIN
  DELETE FROM address_cache
   WHERE ttl IS NULL OR ttl <= 0 OR cached_at + make_interval(secs => ttl) <= p_at;
  GET DIAGNOSTICS deleted = ROW_COUNT;
  RETURN deleted;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Writers.  Each refuses, in every mode, input it cannot build a well-formed
-- row from, and never replaces an existing row by a different one.  Rows
-- inserted directly are checked by the triggers and in batch.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION addr_refuse(p_what TEXT, p_problems JSONB) RETURNS VOID AS $$
BEGIN
  IF p_problems IS NOT NULL AND jsonb_array_length(p_problems) > 0 THEN
    RAISE EXCEPTION '%: % (%)', p_what, p_problems -> 0 ->> 'reason', p_problems -> 0 -> 'details';
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Register an address.  The hash must be pq_hash(cbor, algo), the bytes a
-- canonical AddressV2, and p_trust / p_depth (when given) its trust hint.
-- Registering an address again returns the existing row, adding any new
-- pointers; nothing else about a registered address ever changes.
CREATE OR REPLACE FUNCTION register_address(
  p_address_hash TEXT, p_address_cbor BYTEA,
  p_owner BYTEA DEFAULT NULL,
  p_pointers JSONB DEFAULT '[]'::jsonb,
  p_trust DOUBLE PRECISION DEFAULT NULL,
  p_depth INT DEFAULT NULL,
  p_algo TEXT DEFAULT 'SHA3-256'
) RETURNS UUID AS $$
DECLARE
  th JSONB;
  v_trust DOUBLE PRECISION;
  v_depth INT;
  ex RECORD;
  v_id UUID;
BEGIN
  th := addr_trust_hint((addr_cbor_decode(p_address_cbor)) -> 'value');
  v_trust := coalesce(p_trust, (th ->> 'trust_score')::double precision);
  v_depth := coalesce(p_depth, CASE WHEN (th ->> 'verification_depth')::numeric <= 2147483647
                                    THEN (th ->> 'verification_depth')::int END);
  PERFORM addr_refuse('register_address', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM (SELECT * FROM addr_address_problems(p_address_cbor, p_address_hash, p_algo,
                                                v_trust, v_depth)
            UNION ALL SELECT * FROM addr_pointer_problems(p_pointers)) x));
  SELECT a.* INTO ex FROM address_registry a WHERE a.address_hash = p_address_hash;
  IF ex.id IS NOT NULL THEN
    IF ex.address_cbor <> p_address_cbor OR ex.hash_algo <> p_algo THEN
      RAISE EXCEPTION 'register_address: % is registered with other content', p_address_hash;
    END IF;
    IF p_owner IS NOT NULL AND ex.owner_pubkey IS DISTINCT FROM p_owner THEN
      RAISE EXCEPTION 'register_address: % is registered to another owner', p_address_hash;
    END IF;
    UPDATE address_registry a
       SET pointers = a.pointers || coalesce((
             SELECT jsonb_agg(e ORDER BY o) FROM jsonb_array_elements(p_pointers)
                                             WITH ORDINALITY AS x(e, o)
              WHERE NOT a.pointers @> jsonb_build_array(e)), '[]'::jsonb)
     WHERE a.id = ex.id;
    RETURN ex.id;
  END IF;
  INSERT INTO address_registry
    (address_hash, address_cbor, owner_pubkey, pointers, trust_score, verification_depth,
     hash_algo)
  VALUES
    (p_address_hash, p_address_cbor, p_owner, p_pointers, v_trust, v_depth, p_algo)
  RETURNING id INTO v_id;
  RETURN v_id;
END;
$$ LANGUAGE plpgsql;

-- Cache a resolution result learnt elsewhere.
CREATE OR REPLACE FUNCTION cache_address_resolution(
  p_address_hash TEXT, p_pointers JSONB, p_ttl INT, p_source TEXT
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  IF NOT addr_is_address_hash(p_address_hash) THEN
    RAISE EXCEPTION 'cache_address_resolution: % is not an address hash', p_address_hash;
  END IF;
  IF p_ttl IS NULL OR p_ttl <= 0 THEN
    RAISE EXCEPTION 'cache_address_resolution: ttl must be positive, got %', p_ttl;
  END IF;
  IF EXISTS (SELECT 1 FROM addr_pointer_problems(p_pointers)) THEN
    RAISE EXCEPTION 'cache_address_resolution: pointers must be distinct non-empty strings';
  END IF;
  INSERT INTO address_cache (address_hash, pointers, ttl, source)
  VALUES (p_address_hash, p_pointers, p_ttl, p_source)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register a gateway mapping (IP ↔ AddressV2) for a registered address.
CREATE OR REPLACE FUNCTION register_gateway(
  p_address_hash TEXT, p_ip TEXT, p_protocol TEXT
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM address_registry a WHERE a.address_hash = p_address_hash) THEN
    RAISE EXCEPTION 'register_gateway: % is not a registered address', p_address_hash;
  END IF;
  IF NOT addr_endpoint_ok(p_ip) THEN
    RAISE EXCEPTION 'register_gateway: % is not an IP endpoint', p_ip;
  END IF;
  IF p_protocol IS NULL OR p_protocol NOT IN ('tcp', 'udp', 'quic', 'http', 'https', 'ws', 'wss')
  THEN
    RAISE EXCEPTION 'register_gateway: unsupported protocol %', p_protocol;
  END IF;
  SELECT g.id INTO new_id FROM gateway_mapping g
   WHERE g.address_hash = p_address_hash AND g.ip_endpoint = p_ip AND g.protocol = p_protocol;
  IF new_id IS NOT NULL THEN RETURN new_id; END IF;
  INSERT INTO gateway_mapping (address_hash, ip_endpoint, protocol)
  VALUES (p_address_hash, p_ip, p_protocol)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register a DHT node (32-byte id).  Registering it again refreshes last_seen;
-- its endpoint, once set, does not change.
CREATE OR REPLACE FUNCTION register_dht_node(p_node_id BYTEA, p_endpoint TEXT DEFAULT NULL)
RETURNS UUID AS $$
DECLARE
  ex RECORD;
  new_id UUID;
BEGIN
  IF p_node_id IS NULL OR octet_length(p_node_id) <> 32 THEN
    RAISE EXCEPTION 'register_dht_node: a node id is 32 bytes, got %', octet_length(p_node_id);
  END IF;
  SELECT d.* INTO ex FROM dht_node d WHERE d.node_id = p_node_id;
  IF ex.id IS NOT NULL THEN
    IF p_endpoint IS NOT NULL AND ex.endpoint IS NOT NULL AND ex.endpoint <> p_endpoint THEN
      RAISE EXCEPTION 'register_dht_node: node is registered at another endpoint';
    END IF;
    UPDATE dht_node SET last_seen = now(), endpoint = coalesce(endpoint, p_endpoint)
     WHERE id = ex.id;
    RETURN ex.id;
  END IF;
  INSERT INTO dht_node (node_id, endpoint) VALUES (p_node_id, p_endpoint)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Record a discovery query.
CREATE OR REPLACE FUNCTION record_discovery(
  p_query vector, p_k INT, p_results JSONB, p_latency_ms INT
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  IF p_k IS NULL OR p_k <= 0 THEN
    RAISE EXCEPTION 'record_discovery: k must be positive, got %', p_k;
  END IF;
  IF p_latency_ms < 0 THEN
    RAISE EXCEPTION 'record_discovery: negative latency %', p_latency_ms;
  END IF;
  IF p_results IS NULL OR jsonb_typeof(p_results) <> 'array'
     OR jsonb_array_length(p_results) > p_k THEN
    RAISE EXCEPTION 'record_discovery: results must be an array of at most k entries';
  END IF;
  INSERT INTO discovery_log (query_vector, k, results, latency_ms)
  VALUES (p_query, p_k, p_results, p_latency_ms)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;
