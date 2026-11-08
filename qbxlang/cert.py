"""IR digests and signed certificates (`.qbxir` -> `.qbxcert`).

The IR digest is SHA-256 over canonical JSON (sorted keys, no whitespace). A certificate binds
the digest of the `.qbx` source and of its IR to an Ed25519 signature. `verify` recompiles the
source, recomputes both digests and checks the signature, so a certificate can be checked by
anyone holding the source and the public key, without trusting the issuer's run.
"""
import base64
import datetime
import hashlib
import json

try:
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import (Ed25519PrivateKey,
                                                                   Ed25519PublicKey)
    HAVE_CRYPTO = True
except ImportError:  # pragma: no cover
    HAVE_CRYPTO = False

BEGIN, END = "-----BEGIN QBX CERTIFICATE-----", "-----END QBX CERTIFICATE-----"
SIGNED_FIELDS = ("program", "source_sha256", "ir_sha256", "result", "kernel_claims", "issued")


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def sha256(b):
    return "sha256:" + hashlib.sha256(b).hexdigest()


def ir_digest(ir):
    return sha256(canonical(ir))


def _need_crypto():
    if not HAVE_CRYPTO:
        raise RuntimeError("signing needs the 'cryptography' package (pip install cryptography)")


def keygen(path):
    _need_crypto()
    k = Ed25519PrivateKey.generate()
    with open(path, "wb") as f:
        f.write(k.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
                                serialization.NoEncryption()))
    pub = k.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
    with open(path + ".pub", "w") as f:
        f.write(base64.b64encode(pub).decode() + "\n")
    return path + ".pub"


def _payload(fields):
    return canonical({k: fields[k] for k in SIGNED_FIELDS})


def make(source_bytes, ir, key_path=None):
    s = ir["summary"]
    result = "FAIL" if s["fail"] else ("PASS" if not s["undecided"] else "PASS-WITH-UNDECIDED")
    fields = {
        "program": ir["program"],
        "source_sha256": sha256(source_bytes),
        "ir_sha256": ir_digest(ir),
        "result": result,
        "kernel_claims": s["kernel_claims"],
        "issued": datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat(),
    }
    if key_path:
        _need_crypto()
        with open(key_path, "rb") as f:
            k = serialization.load_pem_private_key(f.read(), password=None)
        fields["public_key"] = base64.b64encode(k.public_key().public_bytes(
            serialization.Encoding.Raw, serialization.PublicFormat.Raw)).decode()
        fields["signature"] = base64.b64encode(k.sign(_payload(fields))).decode()
    else:
        fields["public_key"] = fields["signature"] = "unsigned"
    body = "\n".join(f"{k}: {v}" for k, v in fields.items())
    return f"{BEGIN}\n{body}\n{END}\n"


def parse(text):
    lines = text.strip().splitlines()
    if not lines or lines[0] != BEGIN or lines[-1] != END:
        raise ValueError("not a QBX certificate")
    fields = {}
    for ln in lines[1:-1]:
        k, _, v = ln.partition(": ")
        fields[k] = v
    fields["kernel_claims"] = int(fields["kernel_claims"])
    return fields


def verify(cert_text, source_bytes, ir, pubkey_b64=None):
    """Returns a list of (check, ok, detail)."""
    f = parse(cert_text)
    out = [("source digest", f["source_sha256"] == sha256(source_bytes), f["source_sha256"]),
           ("IR digest (recompiled)", f["ir_sha256"] == ir_digest(ir), f["ir_sha256"])]
    if f["signature"] == "unsigned":
        out.append(("signature", False, "certificate is unsigned"))
    else:
        _need_crypto()
        pk = pubkey_b64 or f["public_key"]
        if pubkey_b64 and pubkey_b64 != f["public_key"]:
            out.append(("public key", False, "certificate key differs from the trusted key"))
        try:
            Ed25519PublicKey.from_public_bytes(base64.b64decode(pk)).verify(
                base64.b64decode(f["signature"]), _payload(f))
            out.append(("signature", True, "Ed25519"))
        except Exception as e:  # noqa: BLE001
            out.append(("signature", False, f"invalid: {type(e).__name__}"))
    return out
