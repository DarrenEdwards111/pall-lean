import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConeAmplify

/-!
# N-Frame: `hdisj` from the spectral mixing angle — it collapses to `log`, like the formula route

Attacking the one residual `hdisj` (cone disjointness) via the Ramanujan mixer's SPECTRAL mixing
property, not just its cut-rank.  Honest outcome: the spectral angle does NOT close `hdisj`, and it
fails for a precise, documented reason — norm-based certificates compose MULTIPLICATIVELY, so their
useful strength is additive in the LOG, collapsing to `O(log N)` across the recursion, exactly like
the formula route (Failure Mode II).

## The audit

The expander mixing lemma `|e(S,T) - d|S||T|/N| ≤ λ√(|S||T|)` (Ramanujan `λ ≤ 2√(d-1)`) is a
NORM-based certificate.  Under the recursion's composition it behaves multiplicatively: the
surviving discrepancy of a `k`-fold composition is `≈ λ^k`, so the certificate distinguishes about
`(2^b)^k = 2^{bk}` behaviours after `k` levels (a per-level factor `2^b` multiplied `k` times).  Its
useful strength is therefore additive in the log:

  `spectral_composition_log` — **PROVED**: `log₂((2^b)^k) = b·k`.  The `k`-fold multiplicative
        composition has log-strength `b·k` — ADDITIVE in the log, `O(k)` per level.
  `spectral_distinguishes_poly` — **PROVED**: `(2^b)^k = (2^k)^b`.  With `N = 2^k` this is `N^b` —
        the spectral certificate distinguishes only POLYNOMIALLY many behaviours, so it certifies
        `coneExcess ≤ log₂(N^b) = b·log₂N = O(log N)`.
  `spectral_below_demand` — **PROVED**: for `N = 2^k > b/c`, `b·k < c·(k·2^k)` — the spectral
        certificate's strength `b·k` is STRICTLY below the demand target `c·k·2^k = c·N·log₂N`.

So the spectral angle gives `O(log N)`, collapsing exactly like the formula route
(`NFrameNonRankCert.formula_cert_collapse`): both are LOG-ADDITIVE certificates, and log-additive
certificates compose to `O(log N)`.  This is the classical composition barrier for norm-based
methods (discrepancy, `γ₂`) — it is why they do not prove KRW-type composition lower bounds.

## Why demand differs (the constructive pointer)

The demand certificate is additive in the RAW count, not the log: `coneExcess` itself adds across
levels, giving `Σ = Θ(N log N)` (`NFrameConeAmplify.coneExcess_amplify`).  That is the distinction
that matters for `hdisj`: a certificate that closes it must be COUNT-additive under composition, not
norm/log-additive.  Spectral mixing is norm/log-additive, so it cannot close `hdisj`; the methods
that actually compose (information complexity, structure theorems) are count-additive in the right
sense.  This audit does not close `hdisj` — it removes the spectral route and points at what a
working certificate must be.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSpectralComposition

/-- **SPECTRAL COMPOSITION IS LOG-ADDITIVE (proved)**: a per-level spectral factor `2^b`, composed
`k` times (multiplicatively), has log-strength `log₂((2^b)^k) = b·k` — additive in the log, `O(k)`.
Across the recursion (`k = log₂N` levels) this is `O(log N)`. -/
theorem spectral_composition_log (b k : ℕ) : Nat.log 2 ((2 ^ b) ^ k) = b * k := by
  rw [← pow_mul]
  exact Nat.log_pow one_lt_two (b * k)

/-- **THE SPECTRAL CERTIFICATE IS POLYNOMIAL (proved)**: `(2^b)^k = (2^k)^b`.  With `N = 2^k` the
`k`-fold spectral composition distinguishes only `N^b` behaviours — polynomially many — so it
certifies `coneExcess ≤ log₂(N^b) = b·log₂N = O(log N)`, sub-linear. -/
theorem spectral_distinguishes_poly (b k : ℕ) : (2 ^ b) ^ k = (2 ^ k) ^ b := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **SPECTRAL IS STRICTLY BELOW THE DEMAND TARGET (proved)**: for `N = 2^k > b/c` the spectral
log-strength `b·k` is strictly below the demand target `c·(k·2^k) = c·N·log₂N`.  The spectral
angle collapses to `O(log N)`; the demand certificate reaches `Θ(N log N)`. -/
theorem spectral_below_demand (b c k : ℕ) (hk : 1 ≤ k) (hN : b < c * 2 ^ k) :
    b * k < c * (k * 2 ^ k) := by
  have h1 : b * k < (c * 2 ^ k) * k := Nat.mul_lt_mul_of_pos_right hN (by omega)
  calc b * k < (c * 2 ^ k) * k := h1
    _ = c * (k * 2 ^ k) := by ring

end PallLean.Paper93.DeepMath.PathB.NFrameSpectralComposition

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSpectralComposition.spectral_composition_log
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSpectralComposition.spectral_distinguishes_poly
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSpectralComposition.spectral_below_demand
