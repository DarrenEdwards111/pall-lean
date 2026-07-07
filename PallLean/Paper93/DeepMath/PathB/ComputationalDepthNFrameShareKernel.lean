import Mathlib

/-!
# N-Frame: the share-gate kernel bound — F₂-linear cancellation-sharing gives no net saving

Step 1 of the horizontal direct-sum closure: `g` mixed (share) gates over `F₂`, gate `i` computing
`ℓ_i(x_L) ⊕ m_i(x_R)`.  Model the left/right parts as linear maps `L, M : F₂^g → (forms)`.  The
pure-left information obtainable by cancelling the right parts is `L(ker M)` (combinations `Σ_{i∈S}`
whose right parts sum to `0`, yielding a pure `x_L`-form `Σ_{i∈S} ℓ_i`).

  `share_kernel_left_dim_bound` — **PROVED**: if the right parts are not all zero (`M ≠ 0`, i.e. the
        gates are genuinely mixed), then `dim(L(ker M)) ≤ g − 1`.  So `g` share-gates produce at most
        `g − 1` independent pure-left forms — strictly fewer than `g` pure `x_L`-gates would.  Linear
        cancellation-sharing gives NO net saving on the left.

  (The sharp two-sided form — the pure-left forms `range Φ ⊓ (A×0)` and pure-right forms
  `range Φ ⊓ (0×B)` are independent inside `range Φ`, so `dim(pure-left) + dim(pure-right) ≤ g` —
  follows by the same rank-nullity argument on `Φ = L.prod M`; the one-sided bound above already
  gives the "no net saving on the left" fact used downstream.)

## Honest scope — this closes LINEAR cancellation, not the full direct sum

This is a statement about `F₂`-LINEAR share-gates (`ℓ ⊕ m`).  It proves the intended fact for that
model: linear cancellation-sharing cannot manufacture pure information for free, so the linear
`CE_share` deficit of `NFrameCrossBranch.single_scale_recurrence_deficit` is controlled.  It does
NOT cover NON-linear sharing: CGate circuits have AND gates, and `F_k` is non-linear, so a
share-gate can be an arbitrary function of both blocks, not a linear `ℓ ⊕ m`.  Non-linear
cancellation-sharing is not bounded by this rank-nullity argument and remains the open residual of
the direct-sum-for-circuits core.  So this closes ONE model (linear circuits / linear sharing) and
sharpens the residual to the non-linear case; it does not by itself close the horizontal
direct-sum for general circuits.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameShareKernel

open Module

/-- **THE SHARE-KERNEL LEFT BOUND (proved)**: `g` linear mixed gates with non-trivial right parts
(`M ≠ 0`) yield at most `g − 1` independent pure-left forms — `dim(L(ker M)) ≤ g − 1`.  Linear
cancellation-sharing gives no net saving on the left. -/
theorem share_kernel_left_dim_bound {g : ℕ} {A B : Type*}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    (L : (Fin g → ZMod 2) →ₗ[ZMod 2] A) (M : (Fin g → ZMod 2) →ₗ[ZMod 2] B)
    (hM : M ≠ 0) :
    finrank (ZMod 2) ((LinearMap.ker M).map L) ≤ g - 1 := by
  have hmap : finrank (ZMod 2) ((LinearMap.ker M).map L)
      ≤ finrank (ZMod 2) (LinearMap.ker M) := Submodule.finrank_map_le L _
  have hproper : LinearMap.ker M < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro h
    exact hM (LinearMap.ker_eq_top.mp h)
  have hkerlt : finrank (ZMod 2) (LinearMap.ker M)
      < finrank (ZMod 2) (Fin g → ZMod 2) := by
    have h := Submodule.finrank_lt_finrank_of_lt hproper
    rwa [finrank_top] at h
  have hg : finrank (ZMod 2) (Fin g → ZMod 2) = g := by
    rw [Module.finrank_pi, Fintype.card_fin]
  rw [hg] at hkerlt
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameShareKernel

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameShareKernel.share_kernel_left_dim_bound
