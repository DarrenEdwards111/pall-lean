import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullPathDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestDecoder

/-!
# The `(K-s)`-shell count bound — star conservation (branch only)

The genuine geometric content of the switching count is **star conservation**: the canonical deepest
branch fixes exactly one *free* variable (a "star") per step, and never re-fixes one, so the leaf
`deepestEnd cs F ρ` has exactly

  `stars (deepestEnd cs F ρ) = stars ρ - (canonicalDT cs F ρ).depth`.

Hence a restriction with `K` stars whose canonical tree has depth `s` lands, at its leaf, in the
**`(K-s)`-star shell** `{σ : stars σ = K-s}` — whose cardinality `card_stars_eq` gives as exactly
`C(n,K-s)·2^(n-(K-s))`.  This is precisely the `hmem` (`deepestEnd ∈ Short`) that
`fullpath_switching_count` consumes, with `Short` the `(K-s)`-shell.  Assembling the two yields the
**`(K-s)`-shell count bound**

  `|Bad| ≤ C(n,K-s)·2^(n-(K-s))·(2w)^s`   for the reconstructible `K`-star depth-`s` bad set.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.

**Honest scope.**  `Bad` carries the reconstruction's requirements (`hnf`: ρ falsifies nothing on
`cs`; `hleaf`: leaf unsatisfied; `hpos`: query positions `< w`), so this bounds the *reconstructible*
`K`-star depth-`s` restrictions.  Relating that to `{depth = s}` over all restrictions (the ρ that
falsify some clause) and the choice of universe (`K`-star family) are separate steps.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Fixing a variable removes exactly it from the free set. -/
theorem freeVars_fixVar (σ : Restriction n) (i : Fin n) (b : Bool) :
    SwitchingCounting.freeVars (fixVar σ i b) = (SwitchingCounting.freeVars σ).erase i := by
  ext j
  simp only [SwitchingCounting.mem_freeVars, Finset.mem_erase]
  constructor
  · intro hj
    by_cases hji : j = i
    · subst hji; rw [fixVar, Function.update_self] at hj; simp at hj
    · rw [fixVar, Function.update_of_ne hji] at hj; exact ⟨hji, hj⟩
  · intro ⟨hji, hj⟩
    rw [fixVar, Function.update_of_ne hji]; exact hj

/-- Fixing a *free* variable decreases the star count by exactly one. -/
theorem stars_fixVar_succ {σ : Restriction n} {i : Fin n} {b : Bool} (h : σ i = none) :
    SwitchingCounting.stars (fixVar σ i b) + 1 = SwitchingCounting.stars σ := by
  unfold SwitchingCounting.stars
  rw [freeVars_fixVar, Finset.card_erase_of_mem (SwitchingCounting.mem_freeVars.mpr h)]
  have hpos : 0 < (SwitchingCounting.freeVars σ).card :=
    Finset.card_pos.mpr ⟨i, SwitchingCounting.mem_freeVars.mpr h⟩
  omega

/-- Every variable selected by the deepest branch was free in the start state. -/
theorem deepestSel_subset_freeVars (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Restriction n), deepestSel cs F σ ⊆ SwitchingCounting.freeVars σ := by
  intro F
  induction F with
  | zero => intro σ; simp only [deepestSel]; exact Finset.empty_subset _
  | succ fuel ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestSel]; simp only [hany, if_true]; exact Finset.empty_subset _
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestSel]; simp only [hany, Bool.false_eq_true, if_false, hact]
        exact Finset.empty_subset _
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestSel]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]
          exact Finset.empty_subset _
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hfree : σ (litVar ℓ) = none := activeTermLit_var_free hatl
          rw [deepestSel]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]
          split
          · rw [Finset.insert_subset_iff]
            refine ⟨SwitchingCounting.mem_freeVars.mpr hfree, ?_⟩
            refine (ih (fixVar σ (litVar ℓ) false)).trans ?_
            rw [freeVars_fixVar]; exact Finset.erase_subset _ _
          · rw [Finset.insert_subset_iff]
            refine ⟨SwitchingCounting.mem_freeVars.mpr hfree, ?_⟩
            refine (ih (fixVar σ (litVar ℓ) true)).trans ?_
            rw [freeVars_fixVar]; exact Finset.erase_subset _ _

/-- The selected variable is fresh: it is not among the variables selected later in the branch. -/
private theorem litVar_not_mem_deepestSel (cs : List (Clause n)) (fuel : ℕ)
    {σ : Restriction n} {ℓ : Rung4Literal n} {b : Bool} (hfree : σ (litVar ℓ) = none) :
    litVar ℓ ∉ deepestSel cs fuel (fixVar σ (litVar ℓ) b) := by
  intro hmem
  have hsub := deepestSel_subset_freeVars cs fuel (fixVar σ (litVar ℓ) b) hmem
  rw [freeVars_fixVar] at hsub
  exact Finset.notMem_erase _ _ hsub

/-- **The number of selected variables equals the tree depth.** -/
theorem deepestSel_card_eq_depth (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Restriction n),
      (deepestSel cs F σ).card = (canonicalDT cs F σ).depth := by
  intro F
  induction F with
  | zero => intro σ; simp only [deepestSel, canonicalDT, Finset.card_empty]; split <;> rfl
  | succ fuel ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestSel, canonicalDT]; simp only [hany, if_true, Finset.card_empty]; rfl
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestSel, canonicalDT]
        simp only [hany, Bool.false_eq_true, if_false, hact, Finset.card_empty]; rfl
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestSel, canonicalDT]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh, Finset.card_empty]; rfl
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hfree : σ (litVar ℓ) = none := activeTermLit_var_free hatl
          rw [deepestSel, canonicalDT]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh, BoolDecisionTree.depth]
          split
          · rename_i hcmp
            rw [Finset.card_insert_of_notMem (litVar_not_mem_deepestSel cs fuel hfree),
                ih (fixVar σ (litVar ℓ) false), max_eq_left hcmp]
          · rename_i hcmp
            rw [Finset.card_insert_of_notMem (litVar_not_mem_deepestSel cs fuel hfree),
                ih (fixVar σ (litVar ℓ) true), max_eq_right (not_le.mp hcmp).le]

/-- **Star conservation (with the selected set).**  The leaf's stars plus the number of selected
variables equals the start state's stars: the branch fixes each selected (free) variable exactly once. -/
theorem stars_deepestEnd_add_sel (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Restriction n),
      SwitchingCounting.stars (deepestEnd cs F σ) + (deepestSel cs F σ).card
        = SwitchingCounting.stars σ := by
  intro F
  induction F with
  | zero => intro σ; simp only [deepestEnd, deepestSel, Finset.card_empty, Nat.add_zero]
  | succ fuel ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestEnd, deepestSel]; simp only [hany, if_true, Finset.card_empty, Nat.add_zero]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestEnd, deepestSel]
        simp only [hany, Bool.false_eq_true, if_false, hact, Finset.card_empty, Nat.add_zero]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestEnd, deepestSel]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh, Finset.card_empty, Nat.add_zero]
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hfree : σ (litVar ℓ) = none := activeTermLit_var_free hatl
          rw [deepestEnd, deepestSel]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]
          split
          · rw [Finset.card_insert_of_notMem (litVar_not_mem_deepestSel cs fuel hfree)]
            have hih := ih (fixVar σ (litVar ℓ) false)
            have hfx := stars_fixVar_succ (i := litVar ℓ) (b := false) hfree
            omega
          · rw [Finset.card_insert_of_notMem (litVar_not_mem_deepestSel cs fuel hfree)]
            have hih := ih (fixVar σ (litVar ℓ) true)
            have hfx := stars_fixVar_succ (i := litVar ℓ) (b := true) hfree
            omega

/-- **Star conservation.**  `stars (deepestEnd cs F σ) + (canonicalDT cs F σ).depth = stars σ`. -/
theorem stars_deepestEnd_add_depth (cs : List (Clause n)) (F : ℕ) (σ : Restriction n) :
    SwitchingCounting.stars (deepestEnd cs F σ) + (canonicalDT cs F σ).depth
      = SwitchingCounting.stars σ := by
  rw [← deepestSel_card_eq_depth]; exact stars_deepestEnd_add_sel cs F σ

/-- **The leaf of a `K`-star depth-`s` branch has `K-s` stars.** -/
theorem leaf_stars_eq (cs : List (Clause n)) (F : ℕ) (σ : Restriction n) {K s : ℕ}
    (hK : SwitchingCounting.stars σ = K) (hs : (canonicalDT cs F σ).depth = s) :
    SwitchingCounting.stars (deepestEnd cs F σ) = K - s := by
  have h := stars_deepestEnd_add_depth cs F σ
  omega

/-- **The leaf lands in the `(K-s)`-star shell.**  This is the `hmem` of `fullpath_switching_count`
with `Short` the `(K-s)`-shell. -/
theorem deepestEnd_mem_shell (cs : List (Clause n)) (F : ℕ) (σ : Restriction n) {K s : ℕ}
    (hK : SwitchingCounting.stars σ = K) (hs : (canonicalDT cs F σ).depth = s) :
    deepestEnd cs F σ ∈
      Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ = K - s) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, leaf_stars_eq cs F σ hK hs⟩

/-- **The `(K-s)`-shell count bound.**  For the reconstructible `K`-star depth-`s` bad set, the
switching injection lands every leaf in the `(K-s)`-shell, whose size `card_stars_eq` gives as
`C(n,K-s)·2^(n-(K-s))`; with the `(2w)^s` label count this yields

  `|Bad| ≤ C(n,K-s)·2^(n-(K-s))·(2w)^s`. -/
theorem shell_count (cs : List (Clause n)) (w K s F : ℕ) [NeZero w]
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, SwitchingCounting.stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w) :
    Bad.card ≤ n.choose (K - s) * 2 ^ (n - (K - s)) * (2 * w) ^ s := by
  have hmem : ∀ ρ ∈ Bad,
      deepestEnd cs F ρ ∈
        Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ = K - s) :=
    fun ρ hρ => deepestEnd_mem_shell cs F ρ (hstars ρ hρ) (hdepth ρ hρ)
  have hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s :=
    fun ρ hρ => (deepestFullSeq_length_eq_depth cs F ρ).trans (hdepth ρ hρ)
  have hcount := fullpath_switching_count cs w s F hmem hnf hleaf hlen hpos
  rwa [SwitchingCounting.card_stars_eq (K - s)] at hcount

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_deepestEnd_add_depth
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.shell_count
