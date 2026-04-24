import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg
import PallLean.Paper93.DeepMath.Subgradient.DiscreteLaplacian

/-!
# α-partial-derivative closed form for `S_NF` on `K_n` with sum-zero `Φ`

The α-term of `S_NF` is a quadratic form in `Φ`; its gradient component at vertex
`k` is `2α · (L Φ) k` for a symmetric adjacency `A`.

For the specific instantiation on the complete graph `K_n` with sum-zero `Φ`, we
have the closed form `α · n · ‖Φ‖²`, whose `k`-th partial derivative is
`2α · n · Φ_k`.

This file records the underlying closed form for the α-term on this
instantiation, from which the partial-derivative formula follows by standard
calculus on polynomials. The closed form itself is the theorem below, which
specialises `S_NF_alpha_Kn_sumZero` from `SNFAlphaNonneg.lean`.

Note on imports: we import `SNFAlphaNonneg` (not `SNF`) to avoid the
`S_NF_alpha` redeclaration collision noted in `SNFBddBelow.lean`. The
`S_NF_alpha` used here is the one introduced in `SNFAlphaNonneg.lean`, which
has the same body `α * ∑ i, phi i * (L phi) i` as the one in `SNF.lean`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.Subgradient

/-- The α-term of `S_NF` is a quadratic form in `Φ`; its gradient component at
    vertex `k` is `2α · (L Φ) k` for symmetric `A`.

    For the specific instantiation on `K_n` with sum-zero `Φ`, we have the
    closed form `α · n · ‖Φ‖²`, whose `k`-th partial is `2α · n · Φ_k`.

    We prove here the closed form for the α-term on `K_n` on the sum-zero
    subspace: for `α : ℝ` and sum-zero `Φ`, the α-term equals
    `α · n · ‖Φ‖²`. -/
theorem S_NF_alpha_Kn_closed (α : ℝ) (n : ℕ) (phi : Fin n → ℝ)
    (hphi : ∑ i, phi i = 0) :
    S_NF_alpha α (PallLean.Paper93.DeepMath.LPS.completeAdj n) phi
      = α * (n : ℝ) * ∑ i, phi i * phi i := by
  exact PallLean.Paper93.DeepMath.NFrame.S_NF_alpha_Kn_sumZero α n phi hphi

end PallLean.Paper93.DeepMath.NFrame
