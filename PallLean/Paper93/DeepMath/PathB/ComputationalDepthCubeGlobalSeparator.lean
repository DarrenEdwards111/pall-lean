import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeSumProdCompress

/-!
# Step 5 scaffolding: the global observer separator (`no single observer compresses all views`)

The compressibility rung bounded a shallow `∑∏` through *each* boundary.  The separation HAL wants (step 5) is stronger:
"**no single admissible observer compresses all views simultaneously**".  We formalise the *global* object — the join of
the derivative features across a whole **family** of boundaries — and prove the load-bearing positive fact:

> the easy shallow `∑∏` has a global rank bound that is **independent of the observer family**.

  `globalCubeSpan Fam κ f = ⊔_{ρ∈Fam} cubeDerivSpan κ (restrictB ρ f)` — features visible across the family.
  `globalCubeRank Fam κ f` — its dimension.
  `le_globalCubeRank_of_mem` — every single-boundary rank is `≤` the global rank (monotone).
  **`globalCubeRank_boolFn_sumProd_le`** — for a shallow `∑∏`, `globalCubeRank Fam κ (boolFn ∑∏) ≤ ∑ⱼ 2^{|Sⱼ|}` for
        **every** family `Fam`: all boundary-restrictions of each monomial live in the *same* `2^{|Sⱼ|}`-dim pullback
        subspace, so no family of observers can pump the rank past the intrinsic bound.

  `not_sumProd_of_globalCubeRank_gt` / `sumProd_separation_of_globalRobust` — the **separation criterion**: if some
        observer family witnesses `globalCubeRank > ∑ⱼ 2^{|Sⱼ|}`, then `f` is **not** that shallow `∑∏`.
  `GlobalRobust κ f bound` — the hard-side predicate ("`f`'s global rank exceeds `bound`").

## The honest gate (where the real difficulty sits)

The criterion reduces the separation to: **prove the hard family is `GlobalRobust` beyond `m·2^D`** — i.e. its global
rank *grows* with the observer family while the easy bound stays fixed.  For parity this is character-independence; for a
composite `MOD_q` (the `ACC⁰[6]` target) it is exactly the `F_2`/`F_3` incompatible-field wall the polynomial arc hit
from four angles (`…CompositeCRT`).  That discharge is **not** done here — it is the load-bearing step 6 (the global dual
separator), and per the book1 assessment is `P≠NP`-strength.  `GlobalRobust` is left as an explicit hypothesis; the
non-vacuity lemma `one_le_globalCubeRank_chiFull` only shows parity has *nonzero* global rank, not that it grows.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (boolFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- Iterated cube derivative distributes over a finite sum. -/
theorem cubeDerivList_finset_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin n → Bool) → F)
    (L : List (Fin n)) :
    cubeDerivList L (∑ i ∈ s, g i) = ∑ i ∈ s, cubeDerivList L (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [cubeDerivList_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, cubeDerivList_add, ih, Finset.sum_insert ha]

/-- `finrank` of a `Finset.sup` of subspaces is at most the sum of their `finrank`s. -/
theorem finrank_finset_sup_le {ι : Type*} (s : Finset ι)
    (g : ι → Submodule F ((Fin n → Bool) → F)) :
    Module.finrank F ↥(s.sup g) ≤ ∑ i ∈ s, Module.finrank F ↥(g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [finrank_bot]
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    have hkey := Submodule.finrank_sup_add_finrank_inf_eq (g a) (s.sup g)
    omega

/-- **Global cube span**: derivative features of `f` across a whole family of boundaries. -/
noncomputable def globalCubeSpan (Fam : Finset (Fin n → Option Bool)) (κ : ℕ)
    (f : (Fin n → Bool) → F) : Submodule F ((Fin n → Bool) → F) :=
  Fam.sup (fun ρ => cubeDerivSpan κ (restrictB ρ f))

/-- **Global cube rank**: dimension of the features visible across the family. -/
noncomputable def globalCubeRank (Fam : Finset (Fin n → Option Bool)) (κ : ℕ)
    (f : (Fin n → Bool) → F) : ℕ :=
  Module.finrank F (globalCubeSpan Fam κ f)

/-- Every single-boundary rank is at most the global rank. -/
theorem le_globalCubeRank_of_mem (Fam : Finset (Fin n → Option Bool)) (κ : ℕ)
    (f : (Fin n → Bool) → F) {ρ : Fin n → Option Bool} (hρ : ρ ∈ Fam) :
    boundaryCubeRank ρ κ f ≤ globalCubeRank Fam κ f := by
  rw [boundaryCubeRank, cubeDerivRank, globalCubeRank, globalCubeSpan]
  exact Submodule.finrank_mono (Finset.le_sup (f := fun ρ => cubeDerivSpan κ (restrictB ρ f)) hρ)

/-- **The easy global bound (proved)**: a shallow `∑∏` has `globalCubeRank Fam κ (boolFn ∑∏) ≤ ∑ⱼ 2^{|Sⱼ|}` for *every*
observer family — all boundary-restrictions of each monomial live in the same `2^{|Sⱼ|}`-dim pullback subspace, so no
family of observers can inflate the rank. -/
theorem globalCubeRank_boolFn_sumProd_le (Fam : Finset (Fin n → Option Bool)) {m : ℕ}
    (S : Fin m → Finset (Fin n)) {κ : ℕ} :
    globalCubeRank Fam κ (boolFn (∑ j, ∏ i ∈ S j, X i : MvPolynomial (Fin n) F))
      ≤ ∑ j, 2 ^ (S j).card := by
  rw [globalCubeRank]
  have hsub : globalCubeSpan Fam κ (boolFn (∑ j, ∏ i ∈ S j, X i : MvPolynomial (Fin n) F))
      ≤ (Finset.univ : Finset (Fin m)).sup (fun j => LinearMap.range (embS (S j) (F := F))) := by
    apply Finset.sup_le
    intro ρ _
    rw [cubeDerivSpan, Submodule.span_le]
    rintro g ⟨L, hlen, rfl⟩
    rw [boolFn_sum, restrictB_sum, cubeDerivList_finset_sum]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have hmem : cubeDerivList L (restrictB ρ (boolFn (∏ i ∈ S j, X i : MvPolynomial (Fin n) F)))
        ∈ LinearMap.range (embS (S j) (F := F)) :=
      cubeDerivList_mem_range_embS (S j) L _
        (restrictB_mem_range_embS (S j) ρ _ (boolFn_monoAND_mem_range (S j)))
    exact Finset.le_sup (f := fun j => LinearMap.range (embS (S j) (F := F))) (Finset.mem_univ j) hmem
  refine le_trans (Submodule.finrank_mono hsub) ?_
  refine le_trans (finrank_finset_sup_le _ _) ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  refine le_trans (LinearMap.finrank_range_le (embS (S j) (F := F))) ?_
  rw [Module.finrank_pi, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- **The separation criterion (proved)**: if some observer family witnesses global rank exceeding `∑ⱼ 2^{|Sⱼ|}`, then
`f` is not that shallow `∑∏`. -/
theorem not_sumProd_of_globalCubeRank_gt {m : ℕ} (S : Fin m → Finset (Fin n))
    (f : (Fin n → Bool) → F) {κ : ℕ} (Fam : Finset (Fin n → Option Bool))
    (h : ∑ j, 2 ^ (S j).card < globalCubeRank Fam κ f) :
    f ≠ boolFn (∑ j, ∏ i ∈ S j, X i : MvPolynomial (Fin n) F) := by
  intro heq
  rw [heq] at h
  exact absurd (globalCubeRank_boolFn_sumProd_le Fam S) (not_le.mpr h)

/-- The hard-side predicate: `f`'s global rank exceeds `bound` for some observer family. -/
def GlobalRobust (κ : ℕ) (f : (Fin n → Bool) → F) (bound : ℕ) : Prop :=
  ∃ Fam : Finset (Fin n → Option Bool), bound < globalCubeRank Fam κ f

/-- **The conditional separation (proved)**: a globally-robust `f` (beyond `∑ⱼ 2^{|Sⱼ|}`) is not the shallow `∑∏`.  The
discharge of `GlobalRobust` for a hard family is the load-bearing open gate (step 6). -/
theorem sumProd_separation_of_globalRobust {m : ℕ} (S : Fin m → Finset (Fin n))
    (f : (Fin n → Bool) → F) {κ : ℕ}
    (h : GlobalRobust κ f (∑ j, 2 ^ (S j).card)) :
    f ≠ boolFn (∑ j, ∏ i ∈ S j, X i : MvPolynomial (Fin n) F) := by
  obtain ⟨Fam, hFam⟩ := h
  exact not_sumProd_of_globalCubeRank_gt S f Fam hFam

/-- **Non-vacuity (proved)**: parity has *nonzero* global rank across a family containing a boundary with a visible
coordinate (`2 ≠ 0`).  This only shows the global machinery is inhabited on the robust side — **not** that parity's global
rank grows past `m·2^D` (that is the open gate). -/
theorem one_le_globalCubeRank_chiFull (Fam : Finset (Fin n → Option Bool))
    {ρ : Fin n → Option Bool} (hρ : ρ ∈ Fam) {j : Fin n} (hj : ρ j = none) (h2 : (2 : F) ≠ 0) :
    1 ≤ globalCubeRank Fam 1 (chiFull : (Fin n → Bool) → F) :=
  le_trans (one_le_boundaryCubeRank_chiFull ρ hj h2) (le_globalCubeRank_of_mem Fam 1 chiFull hρ)

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.globalCubeRank_boolFn_sumProd_le
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.sumProd_separation_of_globalRobust
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.one_le_globalCubeRank_chiFull
