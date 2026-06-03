import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEndStateDecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReadOnceId

/-!
# The falsify-part of the deepest selected set is label-free recoverable

This isolates exactly what the `(2w)^s` label must do.  Under "ρ falsifies nothing", the variables of
the deepest selected set that carry a **false literal** at the end-state are recoverable from the
end-state alone (`decodedSel`), and they are a **subset** of the selected set:

* `deepestEnd_eq_outside` — outside the selected set, the end-state agrees with `ρ` (from the recovery
  `freeOn_deepestEnd`).
* `decodedSel_subset_deepestSel` — `decodedSel cs (deepestEnd cs F ρ) ⊆ deepestSel cs F ρ`: every
  false-literal variable at the end-state is path-selected (it cannot be `ρ`-fixed, else `ρ` would
  falsify that clause).

So the only part of `deepestSel` *not* read off the end-state is `deepestSel \ decodedSel` — the
variables set by **satisfy-steps** (`true`-bits), which carry no false literal.  That difference is
**exactly** what the `(2w)^s` label must encode; when it is empty (the falsify-deepest regime) the
reconstruction is label-free (`reconstruction_of_deepest_eq_replay`).  The label encoding of the
satisfy-part remains the open core, not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Outside the deepest selected set, the end-state agrees with `ρ` (from `freeOn_deepestEnd`). -/
theorem deepestEnd_eq_outside (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool) {v : Fin n}
    (hv : v ∉ deepestSel cs F ρ) : deepestEnd cs F ρ v = ρ v := by
  have h := congrFun (freeOn_deepestEnd cs F ρ) v
  rw [SwitchingCounting.freeOn, if_neg hv] at h
  exact h

/-- **The falsify-part is a subset of the selected set.**  Under "ρ falsifies nothing", every
false-literal variable at the deepest end-state is path-selected. -/
theorem decodedSel_subset_deepestSel {cs : List (Clause n)} {F : ℕ} {ρ : Fin n → Option Bool}
    (hnf : ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false) :
    SwitchingCounting.decodedSel cs (deepestEnd cs F ρ) ⊆ deepestSel cs F ρ := by
  intro v hv
  by_contra hnotsel
  rw [SwitchingCounting.decodedSel, Finset.mem_filter] at hv
  obtain ⟨_, C, hC, _, ℓ, hℓC, hℓv, hℓf⟩ := hv
  have hout : deepestEnd cs F ρ v = ρ v := deepestEnd_eq_outside cs F ρ hnotsel
  have hval : ρ (litVar ℓ) = deepestEnd cs F ρ (litVar ℓ) := by rw [hℓv, hout]
  have hfρ : SwitchingCounting.litFalse ρ ℓ = true := by
    rw [SwitchingCounting.litFalse_eq_of_litVar_val hval]; exact hℓf
  have hcf : SwitchingCounting.termFalsified ρ C = true := by
    rw [SwitchingCounting.termFalsified, List.any_eq_true]; exact ⟨ℓ, hℓC, hfρ⟩
  rw [hnf C hC] at hcf; exact absurd hcf (by simp)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestEnd_eq_outside
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.decodedSel_subset_deepestSel
