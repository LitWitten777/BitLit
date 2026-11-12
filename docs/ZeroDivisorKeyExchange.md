# Zero-divisor key exchange on the associator centralizer H(a, b)

Lean files:
- `Sovereign/Graph/ZeroDivisorKeyExchange.lean`: the sedenion protocol (`S_16`)
- `Sovereign/Algebra/TrigintaduonionKeyExchange.lean`: one instance in `T_32`
- `Sovereign/Quantum/PeriodFindingSampling.lean`: the sampling step of Shor's period-finding algorithm

## Protocol
The public data are an annihilating pair `a b = 0` of the 168 zero divisors `±e_i ± e_{8+j}` and a base `g` in
`H(a, b) = {x | (a x) b = a (x b)}`. Alice publishes `g^x` and Bob publishes `g^y`. The shared key is
`(g^y)^x = (g^x)^y`. Powers are left-nested in the sedenions.

## What was proved (0 sorry)
| Claim | Status |
|---|---|
| Both parties get the same key (`keyExchange_correct`) | proved |
| Every bracketing of a public word equals `g^length` (`evalWord_eq_spow`) | proved |
| Public words commute (`spow_comm`) | proved |
| A ZD-DLP solver gives the shared key (`sharedKey_of_dlog`, `dlog_recovers_key`) | proved |
| ZD-DLP has the same solutions as the quaternion DLP `u^x = v` in ℍ (`zdDLP_solutions_eq`) | proved |
| A shared-key solver gives a ZD-DLP solver (the converse direction) | **not proved** (open in general for Diffie–Hellman-type problems) |
| "Shor fails because of non-abelian, non-associative phase randomization" | **refuted**, see below |

## Why the Shor claim is refuted
- `exactPeriod_of_orderOf`: if the base has finite order `r`, then `x ↦ g^x` has exact period `r`.
- `outcomeProb_eq`: for any function with exact period `r` and `N = rM`, the QFT outcome `k` has probability
  `1/r` when `M ∣ k` and `0` otherwise, which is the textbook distribution. `outcomeProb_sum`: the probabilities sum to 1.
- `shor_succeeds_example`: take `a = e1 + e10`, `b = e4 − e15` and `g = (1 + e5 + e8 + e13)/2`, which has order 6.
  Each multiple of `N/6` is observed with probability exactly `1/6`.
- `dlog_hidden_period`: Shor's discrete-log function `F(x, y) = g^x h^y` with `h = g^s` has the hidden period `(s, r − 1)`.
- `T_32` (`t32_shor_sampling`): take `a = e1 + e18`, `b = e4 − e23` and `g = e5`. The period is 4 and the same sampling law holds.

The public words all lie in `H(a, b)`, which is isomorphic to ℍ. Along any single base they even lie in a commutative
subalgebra. So neither non-associativity nor non-commutativity reaches the protocol.

## T_32 caveat
`centralBasisCounts`: across the annihilating pairs of cross-half zero divisors in `T_32`, the number of basis vectors
`e_c` that satisfy `(a e_c) b = a (e_c b)` takes the values 4, 6, 12 and 20. So in `T_32` the centralizer is not
uniformly 4-dimensional.
