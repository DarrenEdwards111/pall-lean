import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg

/-!
# α-term coercivity of `S_NF` on `K_n` with sum-zero `Φ`

This file records the coercivity statement for the α-term of the
N-Frame action on the complete graph `K_n` with sum-zero `Φ`:

  `α · n · ‖Φ‖²  ≤  S_NF_alpha α (completeAdj n) Φ`.

In fact, on sum-zero `Φ` the two sides are equal; we phrase the first
theorem as an inequality for direct use in coercivity arguments, and
record the exact equality in the second theorem for the record.

Paper reference: §28.3 pp. 137–138 (action `S_NF[Φ; P]`, α-term).
-/

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS

/-- α-term coercivity: for α > 0 and sum-zero Φ on K_n, `S_NF_α ≥ α · n · ‖Φ‖²`. -/
theorem S_NF_alpha_Kn_ge_scaled_norm_sq (α : ℝ) (n : ℕ)
    (hα : 0 ≤ α) (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0) :
    α * (n : ℝ) * (∑ i, phi i * phi i) ≤ S_NF_alpha α (completeAdj n) phi :=
  le_of_eq (S_NF_alpha_Kn_sumZero α n phi hphi).symm

/-- Exact equality version for the record. -/
theorem S_NF_alpha_Kn_eq_scaled_norm_sq (α : ℝ) (n : ℕ)
    (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0) :
    S_NF_alpha α (completeAdj n) phi = α * (n : ℝ) * (∑ i, phi i * phi i) :=
  S_NF_alpha_Kn_sumZero α n phi hphi

end PallLean.Paper93.DeepMath.NFrame
