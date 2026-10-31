import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWHybrid

/-!
# Socket-2 (IKW): the stretch of the Nisan–Wigderson generator

The Nisan–Wigderson generator maps a seed over the universe `F_q × F_q` (`q²` bits) to one output bit per degree-`<k`
polynomial.  For the generator to be a *pseudorandom generator* it must **stretch** — more outputs than seed bits.  This
file counts both sides: the seed has `q²` bits, and there are `q^k` degree-`<k` polynomials, so the generator stretches
`q² → q^k`, a genuine stretch for `k > 2`.

  `seed_card` — **PROVED**: the universe (seed length) is `|F_q × F_q| = q²`.
  `output_card` — **PROVED**: the number of output coordinates (degree-`<k` polynomials) is `q^k`.
  `nw_stretch` — **PROVED**: for `k > 2` (and `q ≥ 2`), the output count exceeds the seed length — the generator stretches.

## Honest scope — the stretch, not the pseudorandomness

This quantifies that the NW generator genuinely stretches (`q^k > q²` for `k ≥ 3`), the counting prerequisite for it to be
a PRG.  It does **not** establish that the stretched output is *pseudorandom* (fools small circuits when the base function
is hard) — that is the hybrid argument (rung 3's read-`<k` locality is its combinatorial engine, but the probabilistic
next-bit-predictor step is not done) — nor the IKW easy-witness collapse.  Those are the deep `NEXP`-strength content of
socket 2, not established here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NWDesign

open Polynomial

variable {q : ℕ} [Fact q.Prime]

/-- **The seed length (proved)**: the universe `F_q × F_q` has `q²` points, one seed bit each. -/
theorem seed_card : Nat.card (ZMod q × ZMod q) = q ^ 2 := by
  rw [Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  ring

/-- **The output count (proved)**: there are `q^k` degree-`<k` polynomials over `F_q`, one output coordinate each. -/
theorem output_card (k : ℕ) : Nat.card (Polynomial.degreeLT (ZMod q) k) = q ^ k := by
  rw [Nat.card_congr (Polynomial.degreeLTEquiv (ZMod q) k).toEquiv, Nat.card_pi]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- **The generator stretches (proved)**: for `k > 2`, there are more output coordinates (`q^k`) than seed bits (`q²`). -/
theorem nw_stretch (k : ℕ) (hk : 2 < k) :
    Nat.card (ZMod q × ZMod q) < Nat.card (Polynomial.degreeLT (ZMod q) k) := by
  rw [seed_card, output_card]
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  exact Nat.pow_lt_pow_right hq hk

end PallLean.Paper93.DeepMath.PathB.NWDesign

#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.output_card
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nw_stretch
