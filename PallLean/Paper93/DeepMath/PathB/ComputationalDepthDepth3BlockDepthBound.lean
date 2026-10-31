import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockStars

/-!
# Block-DT model, foundation 8b: the leaf-depth bound (branch only)

Each block contributes at least one fresh masked variable (the active term has a free literal; that
variable is killed before the next block, so blocks' masks are disjoint).  Hence the total number of
masked variables is at least the number of blocks:

  `(blockStream cs F ρ).length ≤ |maskedVars (blockMasks cs F ρ)|`,

and with star conservation (`stars_blockEncode`),

  `stars (blockEncode cs F ρ) ≤ stars ρ - (blockStream cs F ρ).length`.

So a `K`-star restriction whose block descent has `s` blocks has a boundary leaf with `≤ K - s` stars.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `maskedVars` of a cons splits as the head mask's set union the tail's masked set. -/
theorem maskedVars_cons (mask : Fin n → Bool) (rest : List (Fin n → Bool)) :
    maskedVars (mask :: rest)
      = Finset.univ.filter (fun v => mask v) ∪ maskedVars rest := by
  ext v
  simp only [maskedVars, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    List.any_cons, Bool.or_eq_true]

/-- **The leaf-depth bound.**  At least one masked variable per block. -/
theorem blockStream_length_le_maskedVars (cs : List (Clause n)) :
    ∀ (F : ℕ) (ρ : Restriction n),
      (blockStream cs F ρ).length ≤ (maskedVars (blockMasks cs F ρ)).card := by
  intro F
  induction F with
  | zero => intro ρ; rw [blockStream]; exact Nat.zero_le _
  | succ F ih =>
    intro ρ
    cases hany : SwitchingCounting.anyTermSat cs ρ with
    | true => rw [blockStream]; simp only [hany, if_true, List.length_nil]; exact Nat.zero_le _
    | false =>
      cases hact : SwitchingCounting.activeTerm cs ρ with
      | none =>
        rw [blockStream]; simp only [hany, Bool.false_eq_true, if_false, hact, List.length_nil]
        exact Nat.zero_le _
      | some T =>
        have hstream : blockStream cs (F + 1) ρ = T :: blockStream cs F (killTerm ρ T) := by
          rw [blockStream]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hmask : blockMasks cs (F + 1) ρ
            = (fun v => decide (ρ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits
                ∨ (Rung4Literal.neg v) ∈ T.lits))) :: blockMasks cs F (killTerm ρ T) := by
          rw [blockMasks]; simp only [hany, Bool.false_eq_true, if_false, hact]
        -- a free literal of `T` gives a fresh masked variable
        have hfl : 0 < (SwitchingCounting.freeLits ρ T).length := by
          have hfind : cs.find?
              (fun U => !SwitchingCounting.termFalsified ρ U
                && decide (0 < (SwitchingCounting.freeLits ρ U).length)) = some T := by
            rw [← SwitchingCounting.activeTerm_eq_find hany]; exact hact
          have hp := List.find?_some hfind
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
          exact hp.2
        obtain ⟨ℓ, hℓ⟩ := List.exists_mem_of_length_pos hfl
        have hℓT : ℓ ∈ T.lits := (List.mem_filter.mp hℓ).1
        have hℓfree : ρ (litVar ℓ) = none := by
          have hf : Depth3.litFree ρ ℓ = true := (List.mem_filter.mp hℓ).2
          rw [litFree_var] at hf
          cases hx : ρ (litVar ℓ) with
          | none => rfl
          | some _ => rw [hx] at hf; simp at hf
        set headSet : Finset (Fin n) := Finset.univ.filter
          (fun v => decide (ρ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits
            ∨ (Rung4Literal.neg v) ∈ T.lits))) with hheadSet
        -- the head mask set is disjoint from the tail's masked set
        have hdisj : Disjoint headSet (maskedVars (blockMasks cs F (killTerm ρ T))) := by
          rw [Finset.disjoint_left]
          intro v hv hvt
          rw [hheadSet, Finset.mem_filter, decide_eq_true_eq] at hv
          rw [maskedVars, Finset.mem_filter] at hvt
          have hkn : killTerm ρ T v = none := masked_imp_free cs F (killTerm ρ T) hvt.2
          rw [killTerm_block_val hv.2.1 hv.2.2] at hkn
          split at hkn <;> simp at hkn
        -- the head mask set is nonempty (contains `litVar ℓ`)
        have hℓmem : litVar ℓ ∈ headSet := by
          rw [hheadSet, Finset.mem_filter, decide_eq_true_eq]
          refine ⟨Finset.mem_univ _, hℓfree, ?_⟩
          cases ℓ with
          | pos v => exact Or.inl hℓT
          | neg v => exact Or.inr hℓT
        have hheadpos : 1 ≤ headSet.card := Finset.card_pos.mpr ⟨litVar ℓ, hℓmem⟩
        rw [hstream, hmask, List.length_cons, maskedVars_cons, ← hheadSet,
            Finset.card_union_of_disjoint hdisj]
        have := ih (killTerm ρ T)
        omega

/-- **The boundary leaf has at most `stars ρ - (#blocks)` stars.** -/
theorem stars_blockEncode_le (cs : List (Clause n)) (F : ℕ) (ρ : Restriction n) :
    SwitchingCounting.stars (blockEncode cs F ρ)
      ≤ SwitchingCounting.stars ρ - (blockStream cs F ρ).length := by
  have hcons := stars_blockEncode cs F ρ
  have hlen := blockStream_length_le_maskedVars cs F ρ
  omega

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockStream_length_le_maskedVars
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_blockEncode_le
