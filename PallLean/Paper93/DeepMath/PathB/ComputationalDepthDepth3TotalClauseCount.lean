import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount2

/-!
# Total bottom-clause accounting through a collapse round

The existing iteration records a per-gate clause bound after `mergePass`.  Multiplying that bound
by the surviving gate count introduces an avoidable second gate-count factor: the merge only
flattens sibling clause lists and therefore preserves the total number of bottom-clause
occurrences.  This module records that exact invariant and combines it with the pre-merge
`2^s` bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- Total number of clause occurrences among all syntactic bottom gates. -/
def bottomClauseCount (C : Layered n) : ℕ :=
  ((bottomGates C).map List.length).sum

/-- The corresponding count for a list of layered circuits. -/
def bottomClauseCountList (gs : List (Layered n)) : ℕ :=
  ((bottomGatesList gs).map List.length).sum

/-- Total bottom payload, charging one slot even for an empty (constant) bottom gate.  Raw clause
occurrences do not control the number of bottom gates because `dnf []` and `cnf []` are legal. -/
def bottomSlotCount (C : Layered n) : ℕ :=
  ((bottomGates C).map fun cs => max 1 cs.length).sum

private theorem length_le_sum_max_one_length {α : Type} :
    ∀ css : List (List α), css.length ≤ (css.map fun cs => max 1 cs.length).sum
  | [] => by simp
  | cs :: css => by
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hhead : 1 ≤ max 1 cs.length := Nat.le_max_left _ _
      have htail := length_le_sum_max_one_length css
      omega

private theorem sum_length_le_sum_max_one_length {α : Type} :
    ∀ css : List (List α), (css.map List.length).sum ≤
      (css.map fun cs => max 1 cs.length).sum
  | [] => by simp
  | cs :: css => by
      simp only [List.map_cons, List.sum_cons]
      have hhead : cs.length ≤ max 1 cs.length := Nat.le_max_right _ _
      have htail := sum_length_le_sum_max_one_length css
      omega

/-- The slot count controls the syntactic bottom-gate count, including empty constant gates. -/
theorem bottomGates_length_le_bottomSlotCount (C : Layered n) :
    (bottomGates C).length ≤ bottomSlotCount C := by
  exact length_le_sum_max_one_length (bottomGates C)

/-- The slot count also controls the raw total number of clause occurrences. -/
theorem bottomClauseCount_le_bottomSlotCount (C : Layered n) :
    bottomClauseCount C ≤ bottomSlotCount C := by
  exact sum_length_le_sum_max_one_length (bottomGates C)

/-- Slot accounting is at most one constant-gate charge per bottom gate plus the raw clause
occurrences.  This converse comparison is intentionally additive: empty bottom gates require the
first summand, while nonempty gates are already paid for by the second. -/
theorem bottomSlotCount_le_bottomGates_length_add_bottomClauseCount (C : Layered n) :
    bottomSlotCount C ≤ (bottomGates C).length + bottomClauseCount C := by
  unfold bottomSlotCount bottomClauseCount
  induction bottomGates C with
  | nil => simp
  | cons cs css ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hhead : max 1 cs.length ≤ 1 + cs.length := by omega
      omega

@[simp] theorem bottomClauseCount_dnf (cs : List (Clause n)) :
    bottomClauseCount (dnf cs) = cs.length := by
  simp [bottomClauseCount, bottomGates]

@[simp] theorem bottomClauseCount_cnf (cs : List (Clause n)) :
    bottomClauseCount (cnf cs) = cs.length := by
  simp [bottomClauseCount, bottomGates]

@[simp] theorem bottomClauseCount_gAnd (gs : List (Layered n)) :
    bottomClauseCount (gAnd gs) = bottomClauseCountList gs := rfl

@[simp] theorem bottomClauseCount_gOr (gs : List (Layered n)) :
    bottomClauseCount (gOr gs) = bottomClauseCountList gs := rfl

@[simp] theorem bottomClauseCountList_nil :
    bottomClauseCountList ([] : List (Layered n)) = 0 := rfl

@[simp] theorem bottomClauseCountList_cons (g : Layered n) (gs : List (Layered n)) :
    bottomClauseCountList (g :: gs) = bottomClauseCount g + bottomClauseCountList gs := by
  simp [bottomClauseCountList, bottomClauseCount, bottomGatesList, List.map_append]

private theorem flatten_map_bottomGates_cnf (css : List (List (Clause n))) :
    (List.map (bottomGates ∘ cnf) css).flatten = css := by
  induction css with
  | nil => rfl
  | cons cs css ih => simp [bottomGates, ih]

private theorem flatten_map_bottomGates_dnf (dss : List (List (Clause n))) :
    (List.map (bottomGates ∘ dnf) dss).flatten = dss := by
  induction dss with
  | nil => rfl
  | cons cs dss ih => simp [bottomGates, ih]

/- Flattening uniform siblings, and recursively doing so elsewhere, preserves the exact total
number of bottom-clause occurrences. -/
mutual
theorem mergePass_bottomClauseCount :
    ∀ C : Layered n, bottomClauseCount (mergePass C) = bottomClauseCount C
  | dnf cs => rfl
  | cnf cs => rfl
  | gAnd gs => by
      cases h : allCnf gs with
      | some css =>
          have hgs := allCnf_some h
          rw [show mergePass (gAnd gs) = cnf css.flatten by simp only [mergePass, h],
            bottomClauseCount_cnf, List.length_flatten, hgs]
          simp only [bottomClauseCount, bottomGates, bottomGatesList_eq, List.map_map]
          rw [flatten_map_bottomGates_cnf]
      | none =>
          rw [show mergePass (gAnd gs) = gAnd (mergePassList gs) by
            simp only [mergePass, h], bottomClauseCount_gAnd, bottomClauseCount_gAnd]
          exact mergePassList_bottomClauseCount gs
  | gOr gs => by
      cases h : allDnf gs with
      | some dss =>
          have hgs := allDnf_some h
          rw [show mergePass (gOr gs) = dnf dss.flatten by simp only [mergePass, h],
            bottomClauseCount_dnf, List.length_flatten, hgs]
          simp only [bottomClauseCount, bottomGates, bottomGatesList_eq, List.map_map]
          rw [flatten_map_bottomGates_dnf]
      | none =>
          rw [show mergePass (gOr gs) = gOr (mergePassList gs) by
            simp only [mergePass, h], bottomClauseCount_gOr, bottomClauseCount_gOr]
          exact mergePassList_bottomClauseCount gs
theorem mergePassList_bottomClauseCount :
    ∀ gs : List (Layered n),
      bottomClauseCountList (mergePassList gs) = bottomClauseCountList gs
  | [] => rfl
  | g :: gs => by
      rw [mergePassList, bottomClauseCountList_cons, bottomClauseCountList_cons,
        mergePass_bottomClauseCount g, mergePassList_bottomClauseCount gs]
end

/-- Gate-wise clause bounds sum to a total bound. -/
theorem bottomClauseCount_le_mul {C : Layered n} {M c : ℕ}
    (hcnt : (bottomGates C).length ≤ M) (hcount : BottomCount c C) :
    bottomClauseCount C ≤ M * c := by
  unfold bottomClauseCount
  have heach : ∀ x ∈ (bottomGates C).map List.length, x ≤ c := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨cs, hcs, rfl⟩ := hx
    exact hcount cs hcs
  have hsum := List.sum_le_card_nsmul ((bottomGates C).map List.length) c heach
  rw [List.length_map, smul_eq_mul] at hsum
  exact hsum.trans (Nat.mul_le_mul_right c hcnt)

/-- A shallow collapse round has total bottom-clause count at most `M * 2^s`; `mergePass` does
not introduce the additional factor of `M` present in the coarser per-gate recurrence. -/
theorem collapseRound_bottomClauseCount_le {F M s : ℕ} {ρ : Restriction n}
    {C : Layered n} (hcnt : (bottomGates C).length ≤ M) (hsh : Shallows F ρ s C) :
    bottomClauseCount (collapseRound F ρ C) ≤ M * 2 ^ s := by
  rw [collapseRound, mergePass_bottomClauseCount]
  apply bottomClauseCount_le_mul
  · rw [leafCollapse_bottomGates_length]
    exact hcnt
  · exact leafCollapse_tower_BottomCount F ρ hsh

/-- Occurrence-sensitive form of the collapse bound.  It needs no external gate cap: the current
slot count supplies one, while correctly retaining a unit charge for empty bottom gates. -/
theorem collapseRound_bottomClauseCount_le_bottomSlotCount {F s : ℕ} {ρ : Restriction n}
    {C : Layered n} (hsh : Shallows F ρ s C) :
    bottomClauseCount (collapseRound F ρ C) ≤ bottomSlotCount C * 2 ^ s := by
  exact collapseRound_bottomClauseCount_le (bottomGates_length_le_bottomSlotCount C) hsh

/-- The actual slot invariant needed by the next round is controlled after restriction, switching,
and merge.  The current construction does not prove contraction: its verified worst-case recurrence
is multiplication by `2^s + 1`, with the `+1` retaining legal empty constant gates. -/
theorem collapseRound_bottomSlotCount_le {F s : ℕ} {ρ : Restriction n}
    {C : Layered n} (hne : NonEmptyGates C) (hsh : Shallows F ρ s C) :
    bottomSlotCount (collapseRound F ρ C) ≤ bottomSlotCount C * (2 ^ s + 1) := by
  calc
    bottomSlotCount (collapseRound F ρ C) ≤
        (bottomGates (collapseRound F ρ C)).length +
          bottomClauseCount (collapseRound F ρ C) :=
      bottomSlotCount_le_bottomGates_length_add_bottomClauseCount _
    _ ≤ bottomSlotCount C + bottomSlotCount C * 2 ^ s := by
      gcongr
      · exact (collapseRound_count_le F ρ hne).trans
          (bottomGates_length_le_bottomSlotCount C)
      · exact collapseRound_bottomClauseCount_le_bottomSlotCount hsh
    _ = bottomSlotCount C * (2 ^ s + 1) := by ring

/-! ## Semantic lower barrier for slot contraction -/

mutual
/-- A layered circuit with no syntactic bottom gate computes a constant function.  The list
companions are mutual because an empty internal `gAnd`/`gOr` tower may itself contain empty towers. -/
theorem bottomGates_nil_eval_eq :
    ∀ C : Layered n, bottomGates C = [] →
      ∀ x y : Fin n → Bool, Layered.eval C x = Layered.eval C y
  | Layered.dnf cs, h => by simp [bottomGates] at h
  | Layered.cnf cs, h => by simp [bottomGates] at h
  | Layered.gAnd gs, h => by
      intro x y
      rw [Layered.eval_gAnd, Layered.eval_gAnd]
      exact bottomGatesList_nil_all_eval_eq gs h x y
  | Layered.gOr gs, h => by
      intro x y
      rw [Layered.eval_gOr, Layered.eval_gOr]
      exact bottomGatesList_nil_any_eval_eq gs h x y
theorem bottomGatesList_nil_all_eval_eq :
    ∀ gs : List (Layered n), bottomGatesList gs = [] →
      ∀ x y : Fin n → Bool,
        gs.all (fun g => Layered.eval g x) = gs.all (fun g => Layered.eval g y)
  | [], _ => by simp
  | g :: gs, h => by
      intro x y
      change bottomGates g ++ bottomGatesList gs = [] at h
      have hs := List.append_eq_nil_iff.mp h
      simp only [List.all_cons]
      rw [bottomGates_nil_eval_eq g hs.1 x y,
        bottomGatesList_nil_all_eval_eq gs hs.2 x y]
theorem bottomGatesList_nil_any_eval_eq :
    ∀ gs : List (Layered n), bottomGatesList gs = [] →
      ∀ x y : Fin n → Bool,
        gs.any (fun g => Layered.eval g x) = gs.any (fun g => Layered.eval g y)
  | [], _ => by simp
  | g :: gs, h => by
      intro x y
      change bottomGates g ++ bottomGatesList gs = [] at h
      have hs := List.append_eq_nil_iff.mp h
      simp only [List.any_cons]
      rw [bottomGates_nil_eval_eq g hs.1 x y,
        bottomGatesList_nil_any_eval_eq gs hs.2 x y]
end

/-- Zero slot count is semantically possible only for a constant function. -/
theorem bottomSlotCount_zero_eval_eq (C : Layered n) (hzero : bottomSlotCount C = 0) :
    ∀ x y : Fin n → Bool, Layered.eval C x = Layered.eval C y := by
  apply bottomGates_nil_eval_eq C
  cases h : bottomGates C with
  | nil => rfl
  | cons cs css =>
      rw [bottomSlotCount, h] at hzero
      simp only [List.map_cons, List.sum_cons] at hzero
      have hpos : 1 ≤ max 1 cs.length := Nat.le_max_left _ _
      omega

/-- A single live literal gives a cleanup-independent obstruction to uniform strict slot
contraction.  Every circuit equivalent to that literal on the fully live subcube needs at least
one bottom slot, even if arbitrary constant propagation and semantic duplicate elimination are
allowed. -/
theorem equivOn_singleLiteral_bottomSlotCount_pos (i : Fin n) (C' : Layered n)
    (heq : Layered.EquivOn (fun _ => none)
      (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) C') :
    0 < bottomSlotCount C' := by
  by_contra hnpos
  have hzero : bottomSlotCount C' = 0 := Nat.eq_zero_of_not_pos hnpos
  have hconst := bottomSlotCount_zero_eval_eq C' hzero
    (fun _ => false) (fun _ => true)
  have hfalse : false = Layered.eval C' (fun _ => false) := by
    simpa [DTree.agreeRestriction, DTree.dnfValue, Rung4Literal.eval] using
      heq (fun _ => false) (by simp [DTree.agreeRestriction])
  have htrue : true = Layered.eval C' (fun _ => true) := by
    simpa [DTree.agreeRestriction, DTree.dnfValue, Rung4Literal.eval] using
      heq (fun _ => true) (by simp [DTree.agreeRestriction])
  have : false = true := hfalse.trans (hconst.trans htrue.symm)
  exact Bool.false_ne_true this

/-- The one-slot obstruction persists on every restricted subcube that leaves the literal's
coordinate live.  Thus fixing unrelated variables cannot discharge its baseline charge. -/
theorem equivOn_singleLiteral_bottomSlotCount_pos_of_free (ρ : Restriction n) (i : Fin n)
    (hi : ρ i = none) (C' : Layered n)
    (heq : Layered.EquivOn ρ (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) C') :
    0 < bottomSlotCount C' := by
  by_contra hnpos
  have hzero : bottomSlotCount C' = 0 := Nat.eq_zero_of_not_pos hnpos
  set x : Fin n → Bool := fun j => (ρ j).getD false with hx
  set y : Fin n → Bool := Function.update x i true with hy
  have hxagree : DTree.agreeRestriction ρ x := by
    intro j b hj
    simp [hx, hj]
  have hyagree : DTree.agreeRestriction ρ y := by
    intro j b hj
    have hji : j ≠ i := by
      rintro rfl
      rw [hi] at hj
      simp at hj
    rw [hy, Function.update_of_ne hji]
    exact hxagree j b hj
  have hxi : x i = false := by simp [hx, hi]
  have hyi : y i = true := by simp [hy]
  have hfalse : false = Layered.eval C' x := by
    simpa [DTree.dnfValue, Rung4Literal.eval, hxi] using heq x hxagree
  have htrue : true = Layered.eval C' y := by
    simpa [DTree.dnfValue, Rung4Literal.eval, hyi] using heq y hyagree
  have hconst := bottomSlotCount_zero_eval_eq C' hzero x y
  exact Bool.false_ne_true (hfalse.trans (hconst.trans htrue.symm))

/-- Consequently, no semantics-preserving cleanup can strictly contract the one-slot live-literal
circuit on the fully live subcube.  This includes cleanup procedures stronger than the concrete
`collapseRound` pipeline. -/
theorem singleLiteral_no_equivOn_bottomSlotCount_lt (i : Fin n) (C' : Layered n)
    (heq : Layered.EquivOn (fun _ => none)
      (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) C') :
    ¬ bottomSlotCount C' < bottomSlotCount
      (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) := by
  intro hlt
  have hpos := equivOn_singleLiteral_bottomSlotCount_pos i C' heq
  have hsource : bottomSlotCount (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) = 1 := by
    simp [bottomSlotCount, bottomGates]
  rw [hsource] at hlt
  omega

/-! ## Semantic excess-slot potential -/

/-- The least bottom-slot count among all layered circuits with the same semantics on `ρ`'s
subcube.  This builds ideal constant propagation and semantic deduplication into the potential,
rather than committing to a particular cleanup algorithm. -/
noncomputable def semanticBottomSlotCount (ρ : Restriction n) (C : Layered n) : ℕ :=
  sInf {m : ℕ | ∃ C' : Layered n, Layered.EquivOn ρ C C' ∧ bottomSlotCount C' = m}

private theorem semanticBottomSlotCount_set_nonempty (ρ : Restriction n) (C : Layered n) :
    {m : ℕ | ∃ C' : Layered n, Layered.EquivOn ρ C C' ∧ bottomSlotCount C' = m}.Nonempty := by
  refine ⟨bottomSlotCount C, C, ?_, rfl⟩
  intro x _
  rfl

/-- The semantic minimum is attained by an equivalent layered circuit. -/
theorem exists_equivOn_bottomSlotCount_eq_semantic (ρ : Restriction n) (C : Layered n) :
    ∃ C' : Layered n,
      Layered.EquivOn ρ C C' ∧ bottomSlotCount C' = semanticBottomSlotCount ρ C := by
  exact Nat.sInf_mem (semanticBottomSlotCount_set_nonempty ρ C)

/-- Using the original syntax as a candidate bounds semantic slot count by syntactic slot count. -/
theorem semanticBottomSlotCount_le (ρ : Restriction n) (C : Layered n) :
    semanticBottomSlotCount ρ C ≤ bottomSlotCount C := by
  exact Nat.sInf_le ⟨C, (fun _ _ => rfl), rfl⟩

/-- Passing to a finer restriction can only decrease the ideal semantic slot minimum. -/
theorem semanticBottomSlotCount_anti_of_extends {ρ τ : Restriction n} (C : Layered n)
    (h : ∀ v b, ρ v = some b → τ v = some b) :
    semanticBottomSlotCount τ C ≤ semanticBottomSlotCount ρ C := by
  obtain ⟨C', heq, hslots⟩ := exists_equivOn_bottomSlotCount_eq_semantic ρ C
  refine Nat.sInf_le ⟨C', ?_, hslots⟩
  intro x hx
  exact heq x (fun i b hρ => hx i b (h i b hρ))

/-- Any uniform lower bound on equivalent representatives lower-bounds the semantic minimum. -/
theorem le_semanticBottomSlotCount_of_forall {ρ : Restriction n} {C : Layered n} {k : ℕ}
    (h : ∀ C' : Layered n, Layered.EquivOn ρ C C' → k ≤ bottomSlotCount C') :
    k ≤ semanticBottomSlotCount ρ C := by
  obtain ⟨C', heq, hslots⟩ := exists_equivOn_bottomSlotCount_eq_semantic ρ C
  rw [← hslots]
  exact h C' heq

/-- A live literal has semantic slot count exactly one: ideal cleanup cannot remove its sole
baseline slot. -/
theorem semanticBottomSlotCount_singleLiteral (i : Fin n) :
    semanticBottomSlotCount (fun _ => none)
      (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) = 1 := by
  apply Nat.le_antisymm
  · calc
      semanticBottomSlotCount (fun _ => none)
          (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) ≤
          bottomSlotCount (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) :=
        semanticBottomSlotCount_le _ _
      _ = 1 := by simp [bottomSlotCount, bottomGates]
  · apply le_semanticBottomSlotCount_of_forall
    intro C' heq
    exact equivOn_singleLiteral_bottomSlotCount_pos i C' heq

/-- A live literal has semantic minimum one on every subcube that leaves its coordinate free. -/
theorem semanticBottomSlotCount_singleLiteral_of_free (ρ : Restriction n) (i : Fin n)
    (hi : ρ i = none) :
    semanticBottomSlotCount ρ (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) = 1 := by
  apply Nat.le_antisymm
  · calc
      semanticBottomSlotCount ρ (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) ≤
          bottomSlotCount (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) :=
        semanticBottomSlotCount_le _ _
      _ = 1 := by simp [bottomSlotCount, bottomGates]
  · apply le_semanticBottomSlotCount_of_forall
    intro C' heq
    exact equivOn_singleLiteral_bottomSlotCount_pos_of_free ρ i hi C' heq

/-- Once its coordinate is fixed, a literal is semantically constant and needs no bottom slots. -/
theorem semanticBottomSlotCount_singleLiteral_of_fixed (ρ : Restriction n) (i : Fin n) (b : Bool)
    (hi : ρ i = some b) :
    semanticBottomSlotCount ρ (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold semanticBottomSlotCount
  apply Nat.sInf_le
  refine ⟨if b then Layered.gAnd [] else Layered.gOr [], ?_, ?_⟩
  · intro x hx
    have hxi := hx i b hi
    cases b <;> simp_all [DTree.dnfValue, Rung4Literal.eval]
  · cases b <;> simp [bottomSlotCount, bottomGates, bottomGatesList]

/-- Semantic excess ignores the single irreducible baseline slot. -/
noncomputable def semanticSlotExcess (ρ : Restriction n) (C : Layered n) : ℕ :=
  semanticBottomSlotCount ρ C - 1

/-- A single syntactic clause never carries semantic excess, independently of its width or the
ambient restriction.  Its original one-slot representation is already enough to force the
semantic minimum below the excess threshold. -/
@[simp] theorem semanticSlotExcess_singleClause (ρ : Restriction n) (T : Clause n) :
    semanticSlotExcess ρ (Layered.dnf [T]) = 0 := by
  unfold semanticSlotExcess
  have hle := semanticBottomSlotCount_le ρ (Layered.dnf [T])
  have hslot : bottomSlotCount (Layered.dnf [T]) = 1 := by
    simp [bottomSlotCount, bottomGates]
  omega

/-- An aggregate excess potential over a collection of survivor circuits. -/
noncomputable def aggregateSemanticSlotExcess (ρ : Restriction n) (Cs : List (Layered n)) : ℕ :=
  (Cs.map (semanticSlotExcess ρ)).sum

/-- The irreducible baseline charge: one exactly when the semantic slot minimum is positive. -/
noncomputable def semanticSlotBaseline (ρ : Restriction n) (C : Layered n) : ℕ :=
  min 1 (semanticBottomSlotCount ρ C)

/-- Baseline plus excess reconstructs the full semantic minimum; it is not a smaller potential. -/
theorem semanticSlotBaseline_add_excess (ρ : Restriction n) (C : Layered n) :
    semanticSlotBaseline ρ C + semanticSlotExcess ρ C = semanticBottomSlotCount ρ C := by
  unfold semanticSlotBaseline semanticSlotExcess
  omega

/-- The proposed combined shellwise potential over survivor components. -/
noncomputable def aggregateSemanticBaselineExcess
    (ρ : Restriction n) (Cs : List (Layered n)) : ℕ :=
  (Cs.map fun C => semanticSlotBaseline ρ C + semanticSlotExcess ρ C).sum

/-- Algebraically, the combined potential is exactly the sum of semantic minimum slot counts. -/
theorem aggregateSemanticBaselineExcess_eq (ρ : Restriction n) (Cs : List (Layered n)) :
    aggregateSemanticBaselineExcess ρ Cs =
      (Cs.map (semanticBottomSlotCount ρ)).sum := by
  simp [aggregateSemanticBaselineExcess, semanticSlotBaseline_add_excess]

/-- Arbitrarily many live literals retain their entire baseline-plus-excess mass under every
restriction that leaves the literal coordinate free. -/
theorem aggregateSemanticBaselineExcess_replicate_singleLiteral_of_free
    (ρ : Restriction n) (q : ℕ) (i : Fin n) (hi : ρ i = none) :
    aggregateSemanticBaselineExcess ρ
      (List.replicate q (Layered.dnf [⟨[Rung4Literal.pos i]⟩])) = q := by
  rw [aggregateSemanticBaselineExcess_eq]
  simp [semanticBottomSlotCount_singleLiteral_of_free ρ i hi]

/-- Every live-literal component has zero semantic excess. -/
@[simp] theorem semanticSlotExcess_singleLiteral (i : Fin n) :
    semanticSlotExcess (fun _ => none) (Layered.dnf [⟨[Rung4Literal.pos i]⟩]) = 0 := by
  rw [semanticSlotExcess, semanticBottomSlotCount_singleLiteral]

/-- Arbitrarily many irreducible one-slot components have zero aggregate semantic excess. -/
theorem aggregateSemanticSlotExcess_replicate_singleLiteral (q : ℕ) (i : Fin n) :
    aggregateSemanticSlotExcess (fun _ => none)
      (List.replicate q (Layered.dnf [⟨[Rung4Literal.pos i]⟩])) = 0 := by
  simp [aggregateSemanticSlotExcess]

/-- The same family still carries exactly `q` raw bottom slots.  Hence aggregate excess alone
cannot upper-bound the encoder's baseline slot mass; a separate component-count charge is
unavoidable even under ideal semantic cleanup. -/
theorem sum_bottomSlotCount_replicate_singleLiteral (q : ℕ) (i : Fin n) :
    ((List.replicate q (Layered.dnf [⟨[Rung4Literal.pos i]⟩])).map bottomSlotCount).sum = q := by
  simp [bottomSlotCount, bottomGates]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.mergePass_bottomClauseCount
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRound_bottomClauseCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRound_bottomClauseCount_le_bottomSlotCount
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRound_bottomSlotCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.equivOn_singleLiteral_bottomSlotCount_pos
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.singleLiteral_no_equivOn_bottomSlotCount_lt
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.semanticBottomSlotCount_singleLiteral
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.aggregateSemanticSlotExcess_replicate_singleLiteral
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.sum_bottomSlotCount_replicate_singleLiteral
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.semanticBottomSlotCount_singleLiteral_of_free
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.semanticBottomSlotCount_singleLiteral_of_fixed
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.semanticBottomSlotCount_anti_of_extends
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.aggregateSemanticBaselineExcess_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.aggregateSemanticBaselineExcess_replicate_singleLiteral_of_free
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.semanticSlotExcess_singleClause
