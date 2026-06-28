import Mathlib

/-!
# Triangular invertibility over the subset lattice (PROVED) — the Möbius inversions

The representation-unification (`ComputationalDepthRepUnify`) showed the `{-1,+1}` and `{0,1}` monomial bases are
related by a change of basis that is **triangular** in the subset lattice.  Transferring the span across it needs
that triangular system to be **invertible**.  Its mathematical heart is the pair of Möbius inversions:

  `subset_sum_eq_zero` — if every *downset* sum `Σ_{S ⊆ T} c S` vanishes, then `c = 0` (upward Möbius; the core
        already used inside `Multilinear.eval_injective`).
  `superset_sum_eq_zero` — if every *upset* sum `Σ_{S ⊇ T} c S` vanishes, then `c = 0` (downward Möbius).

The Walsh change-of-basis map `(M c) T = (-2)^{|T|} · Σ_{S ⊇ T} c S` is injective precisely by
`superset_sum_eq_zero` together with `(-2)^{|T|} ≠ 0` (i.e. `2` a unit, `char 𝔽 ≠ 2`): `M c = 0` forces every
upset sum to vanish, hence `c = 0`.  Injective + equal cardinality gives the `{-1,+1}` span.  This file proves the
two inversions; the `M`-injectivity / span-transfer assembly (the sum-swap and the `2`-unit factor) is the
remaining wiring.
-/

namespace PallLean.Paper93.DeepMath.PathB.TriangularInv

variable {n : ℕ} {F : Type*} [AddCommGroup F]

/-- **Upward Möbius inversion.**  If every downset sum `Σ_{S ⊆ T} c S` is zero, then `c` is identically zero.
Proved by strong induction over the subset lattice: `c T` is the top sum minus the (already-zero) proper-subset
sums. -/
theorem subset_sum_eq_zero (c : Finset (Fin n) → F)
    (h : ∀ T : Finset (Fin n), ∑ S ∈ T.powerset, c S = 0) (T : Finset (Fin n)) : c T = 0 := by
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    have hmem : T ∈ T.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl T)
    have hT := h T
    rw [← Finset.add_sum_erase _ c hmem] at hT
    have herase : ∑ S ∈ T.powerset.erase T, c S = 0 := by
      refine Finset.sum_eq_zero (fun S hS => ?_)
      rw [Finset.mem_erase, Finset.mem_powerset] at hS
      exact ih S (Finset.ssubset_iff_subset_ne.mpr ⟨hS.2, hS.1⟩)
    rw [herase, add_zero] at hT
    exact hT

/-- **Downward Möbius inversion.**  If every upset sum `Σ_{S ⊇ T} c S` is zero, then `c` is identically zero.
Proved by strong induction on `|Tᶜ|` (largest sets first): `c T` is the upset sum minus the (already-zero)
proper-superset sums. -/
theorem superset_sum_eq_zero (c : Finset (Fin n) → F)
    (h : ∀ T : Finset (Fin n), ∑ S ∈ Finset.univ.filter (fun S => T ⊆ S), c S = 0)
    (T : Finset (Fin n)) : c T = 0 := by
  suffices H : ∀ k, ∀ T : Finset (Fin n), Tᶜ.card = k → c T = 0 from H Tᶜ.card T rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T hTk
    have hmem : T ∈ Finset.univ.filter (fun S => T ⊆ S) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Subset.refl T⟩
    have hT := h T
    rw [← Finset.add_sum_erase _ c hmem] at hT
    have herase : ∑ S ∈ (Finset.univ.filter (fun S => T ⊆ S)).erase T, c S = 0 := by
      refine Finset.sum_eq_zero (fun S hS => ?_)
      rw [Finset.mem_erase, Finset.mem_filter] at hS
      have hss : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hS.2.2, fun e => hS.1 e.symm⟩
      have hlt : Sᶜ.card < k := by
        rw [← hTk]
        exact Finset.card_lt_card (Finset.compl_ssubset_compl.mpr hss)
      exact ih Sᶜ.card hlt S rfl
    rw [herase, add_zero] at hT
    exact hT

end PallLean.Paper93.DeepMath.PathB.TriangularInv

#print axioms PallLean.Paper93.DeepMath.PathB.TriangularInv.subset_sum_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.TriangularInv.superset_sum_eq_zero
