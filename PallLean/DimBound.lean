/-
  DimBound.lean — Dimension bound for F_SPDP* evaluation subspace

  Paper §8.6: Under the universal restriction ρ*, all SPDP-collapsible
  circuits' evaluation vectors lie in the row space of the canonical
  monomial matrix M. rank(M) ≤ 2^w where w = numLive(ρ*) < n.

  We prove: if all InFSPDP functions' eval vectors lie in a subspace
  of dimension ≤ D, then fspdpEvalSubspace has finrank ≤ D.
  Combined with D = 2^w < 2^n, this gives the dimension bound.
-/
import PallLean.PneqNP_Paper
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace DimBound

open PneqNP_Paper

/-- If the eval vectors of all InFSPDP functions lie in a fixed subspace W,
    then fspdpEvalSubspace ≤ W. -/
theorem fspdp_le_of_contains {n : ℕ}
    (W : Submodule ℚ ((Fin n → Bool) → ℚ))
    (hW : ∀ f : BoolFun n, InFSPDP f → evalVec f ∈ W) :
    fspdpEvalSubspace n ≤ W := by
  unfold fspdpEvalSubspace
  apply Submodule.span_le.mpr
  intro v ⟨f, hf_in, hv_eq⟩
  rw [hv_eq]
  exact hW f hf_in

/-- If fspdpEvalSubspace ≤ W and W has finite rank, then
    finrank(fspdpEvalSubspace) ≤ finrank(W). -/
theorem fspdp_finrank_le_of_le {n : ℕ}
    (W : Submodule ℚ ((Fin n → Bool) → ℚ))
    (hle : fspdpEvalSubspace n ≤ W) :
    Module.finrank ℚ (fspdpEvalSubspace n) ≤ Module.finrank ℚ W := by
  exact Submodule.finrank_mono hle

/-- Combined: if all InFSPDP eval vectors lie in W, then
    finrank(fspdpEvalSubspace) ≤ finrank(W). -/
theorem fspdp_dim_bound_from_container {n : ℕ}
    (W : Submodule ℚ ((Fin n → Bool) → ℚ))
    (hW : ∀ f : BoolFun n, InFSPDP f → evalVec f ∈ W) :
    Module.finrank ℚ (fspdpEvalSubspace n) ≤ Module.finrank ℚ W :=
  fspdp_finrank_le_of_le W (fspdp_le_of_contains W hW)

/-- The dimension bound follows from:
    1. A container subspace W with dim(W) < 2^n
    2. All InFSPDP eval vectors lying in W

    The paper constructs W as the row space of the canonical matrix M
    under the universal restriction ρ*. rank(M) ≤ 2^w where w < n. -/
theorem spdp_dim_bound_from_container {n : ℕ} (hn : n ≥ 2)
    (W : Submodule ℚ ((Fin n → Bool) → ℚ))
    (hW : ∀ f : BoolFun n, InFSPDP f → evalVec f ∈ W)
    (hW_dim : Module.finrank ℚ W < 2 ^ n) :
    Module.finrank ℚ (fspdpEvalSubspace n) < 2 ^ n :=
  lt_of_le_of_lt (fspdp_dim_bound_from_container W hW) hW_dim

end DimBound
