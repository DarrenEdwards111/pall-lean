import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingLayeredBridge

/-!
# Support-sensitive normalized survivor rounds

This module isolates the circuit-support and survivor-round layer from the much larger width-two
2-SAT bridge.  Keeping this dependency-safe prefix independently compiled lets quantitative
iteration consume its kernel-checked interface without replaying the later exhaustive examples.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

variable {n G pad : ℕ}

/-! ### Density-aware support code for realized prefixes

The exact ragged alphabet counts clause occurrences, while the variables queried by a canonical
prefix must occur inside those clauses.  The following support code makes that relationship
explicit.  It bounds the number of distinct realized `d`-variable prefix sets, not the number of
roots in an endpoint fiber; reconstructing roots still requires the endpoint injection already
proved in the witness-label development. -/

/-- Variables occurring in one clause. -/
def clauseVariableSupport {n : ℕ} (T : Depth3.Clause n) : Finset (Fin n) :=
  (T.lits.map litVar).toFinset

/-- Variables occurring in one DNF gate. -/
def gateVariableSupport {n : ℕ} (cs : List (Depth3.Clause n)) : Finset (Fin n) :=
  cs.toFinset.biUnion clauseVariableSupport

/-- A gate with empty variable support is already a semantic canonical terminal under every
restriction: each of its clauses has an empty literal list, so the DNF is either satisfied by an
empty clause or has no active clause.  Consequently its canonical tree is a leaf for every fuel. -/
theorem canonicalDT_depth_eq_zero_of_gateVariableSupport_card_eq_zero {n : ℕ}
    (cs : List (Depth3.Clause n))
    (hzero : (gateVariableSupport cs).card = 0) (fuel : ℕ) (σ : Restriction n) :
    (canonicalDT cs fuel σ).depth = 0 := by
  have hsupp : gateVariableSupport cs = ∅ := Finset.card_eq_zero.mp hzero
  have hlits : ∀ T ∈ cs, T.lits = [] := by
    intro T hT
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro ell hell
    have hv : litVar ell ∈ gateVariableSupport cs := by
      apply Finset.mem_biUnion.mpr
      refine ⟨T, List.mem_toFinset.mpr hT, ?_⟩
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨ell, hell, rfl⟩)
    rw [hsupp] at hv
    simp at hv
  apply canonicalDT_depth_eq_zero_of_terminal cs σ
  unfold CanonicalTerminal
  by_cases hany : anyTermSat cs σ = true
  · exact Or.inl hany
  · right
    rw [activeTerm_eq_find (Bool.eq_false_of_not_eq_true hany)]
    apply List.find?_eq_none.mpr
    intro T hT
    have hTempty : T = ⟨[]⟩ := by
      cases T with
      | mk lits =>
          have h := hlits ⟨lits⟩ hT
          simp only at h
          subst lits
          rfl
    subst T
    simp [freeLits]

/-- Variables occurring anywhere in the exact indexed gate family. -/
def familyVariableSupport {n G : ℕ} (gates : Fin G → List (Depth3.Clause n)) :
    Finset (Fin n) :=
  Finset.univ.biUnion fun g => gateVariableSupport (gates g)

/-- Literal negation changes polarity but not the variable support of a clause. -/
@[simp] theorem clauseVariableSupport_negClause {n : ℕ} (T : Depth3.Clause n) :
    clauseVariableSupport (⟨T.lits.map negLit⟩ : Depth3.Clause n) =
      clauseVariableSupport T := by
  have hmap : T.lits.map (litVar ∘ negLit) = T.lits.map litVar := by
    apply List.map_congr_left
    intro ell _hell
    cases ell <;> rfl
  simpa [clauseVariableSupport, List.map_map] using congrArg List.toFinset hmap

/-- De Morgan dualization preserves the complete variable support of a bottom gate. -/
@[simp] theorem gateVariableSupport_negDNF {n : ℕ} (cs : List (Depth3.Clause n)) :
    gateVariableSupport (negDNF cs) = gateVariableSupport cs := by
  ext v
  simp [gateVariableSupport, negDNF]

/-- The unpolarized support owned by the circuit's syntactic bottom gates. -/
def layeredBottomVariableSupport {n : ℕ} (C : Layered n) : Finset (Fin n) :=
  (bottomGates C).toFinset.biUnion gateVariableSupport

/-! ### Semantic completeness of bottom support -/

/-- A literal has the same value under two assignments that agree at the variable it reads. -/
theorem literal_eval_eq_of_eq_at_var {n : ℕ} (ell : Rung4Literal n)
    {x y : Fin n → Bool} (h : x (litVar ell) = y (litVar ell)) :
    Rung4Literal.eval ell x = Rung4Literal.eval ell y := by
  cases ell <;> simpa [litVar, Rung4Literal.eval] using h

/-- Conjunction of a literal list depends only on the variables occurring in that list. -/
theorem literalList_all_eval_eq_of_agree_on {n : ℕ} (S : Finset (Fin n))
    {x y : Fin n → Bool} (hxy : ∀ v ∈ S, x v = y v) :
    ∀ lits : List (Rung4Literal n),
      (∀ ell ∈ lits, litVar ell ∈ S) →
      lits.all (fun ell => Rung4Literal.eval ell x) =
        lits.all (fun ell => Rung4Literal.eval ell y)
  | [], _ => rfl
  | ell :: lits, hsupp => by
      rw [List.all_cons, List.all_cons,
        literal_eval_eq_of_eq_at_var ell (hxy _ (hsupp ell (by simp))),
        literalList_all_eval_eq_of_agree_on S hxy lits
          (fun ell' hell' => hsupp ell' (by simp [hell']))]

/-- Disjunction of a literal list depends only on the variables occurring in that list. -/
theorem literalList_any_eval_eq_of_agree_on {n : ℕ} (S : Finset (Fin n))
    {x y : Fin n → Bool} (hxy : ∀ v ∈ S, x v = y v) :
    ∀ lits : List (Rung4Literal n),
      (∀ ell ∈ lits, litVar ell ∈ S) →
      lits.any (fun ell => Rung4Literal.eval ell x) =
        lits.any (fun ell => Rung4Literal.eval ell y)
  | [], _ => rfl
  | ell :: lits, hsupp => by
      rw [List.any_cons, List.any_cons,
        literal_eval_eq_of_eq_at_var ell (hxy _ (hsupp ell (by simp))),
        literalList_any_eval_eq_of_agree_on S hxy lits
          (fun ell' hell' => hsupp ell' (by simp [hell']))]

theorem list_all_apply_eq_of_forall_eq {α : Type} (f g : α → Bool) :
    ∀ xs : List α, (∀ a ∈ xs, f a = g a) → xs.all f = xs.all g
  | [], _ => rfl
  | a :: xs, h => by
      rw [List.all_cons, List.all_cons, h a (by simp),
        list_all_apply_eq_of_forall_eq f g xs
          (fun b hb => h b (by simp [hb]))]

theorem list_any_apply_eq_of_forall_eq {α : Type} (f g : α → Bool) :
    ∀ xs : List α, (∀ a ∈ xs, f a = g a) → xs.any f = xs.any g
  | [], _ => rfl
  | a :: xs, h => by
      rw [List.any_cons, List.any_cons, h a (by simp),
        list_any_apply_eq_of_forall_eq f g xs
          (fun b hb => h b (by simp [hb]))]

/-- A layered circuit depends only on a set containing the support of every bottom clause. -/
theorem Layered.eval_eq_of_BottomPred_support {n : ℕ} (S : Finset (Fin n))
    {x y : Fin n → Bool} (hxy : ∀ v ∈ S, x v = y v) :
    ∀ C : Layered n,
      BottomPred (fun T => clauseVariableSupport T ⊆ S) C →
      Layered.eval C x = Layered.eval C y
  | Layered.dnf cs, hbot => by
      simp only [Layered.eval_dnf, DTree.dnfValue]
      apply list_any_apply_eq_of_forall_eq
      intro T hT
      apply literalList_all_eval_eq_of_agree_on S hxy
      intro ell hell
      apply hbot cs (by exact List.mem_cons_self) T hT
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨ell, hell, rfl⟩)
  | Layered.cnf cs, hbot => by
      simp only [Layered.eval_cnf, cnfValue]
      apply list_all_apply_eq_of_forall_eq
      intro T hT
      apply literalList_any_eval_eq_of_agree_on S hxy
      intro ell hell
      apply hbot cs (by exact List.mem_cons_self) T hT
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨ell, hell, rfl⟩)
  | Layered.gAnd gs, hbot => by
      simp only [Layered.eval_gAnd]
      apply list_all_apply_eq_of_forall_eq
      intro g hg
      exact Layered.eval_eq_of_BottomPred_support S hxy g
        (BottomPred_child_gAnd hbot hg)
  | Layered.gOr gs, hbot => by
      simp only [Layered.eval_gOr]
      apply list_any_apply_eq_of_forall_eq
      intro g hg
      exact Layered.eval_eq_of_BottomPred_support S hxy g
        (BottomPred_child_gOr hbot hg)

/-- The syntactically extracted bottom support is semantically complete: agreement on it forces
agreement of the whole layered circuit, independently of depth and gate count. -/
theorem Layered.eval_eq_of_agree_on_bottomSupport {n : ℕ} (C : Layered n)
    {x y : Fin n → Bool}
    (hxy : ∀ v ∈ layeredBottomVariableSupport C, x v = y v) :
    Layered.eval C x = Layered.eval C y := by
  apply Layered.eval_eq_of_BottomPred_support (layeredBottomVariableSupport C) hxy C
  intro cs hcs T hT v hv
  rw [layeredBottomVariableSupport]
  exact Finset.mem_biUnion.mpr ⟨cs, List.mem_toFinset.mpr hcs,
    Finset.mem_biUnion.mpr ⟨T, List.mem_toFinset.mpr hT, hv⟩⟩

/-- A layered circuit computing parity, possibly complemented by one fixed phase, must mention
every coordinate in its bottom support.  The statement is already localization-aware: applying
it to a circuit over `Fin (stars σ)` says that every coordinate still live after `σ` occurs in
the localized bottom family.  Thus semantic preservation of parity on a nontrivial live cube is
incompatible with reducing that live support, independently of switching parameters. -/
theorem Layered.bottomSupport_eq_univ_of_eval_eq_parity_xor {n : ℕ}
    (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase) :
    layeredBottomVariableSupport C = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro j
  by_contra hj
  let x : Fin n → Bool := fun _ => false
  let y : Fin n → Bool := Function.update x j (!x j)
  have hagree : ∀ v ∈ layeredBottomVariableSupport C, x v = y v := by
    intro v hv
    have hvj : v ≠ j := by
      intro hvj
      subst v
      exact hj hv
    simp [y, hvj]
  have heval : Layered.eval C x = Layered.eval C y :=
    MultiSwitching.Layered.eval_eq_of_agree_on_bottomSupport C hagree
  have hflip : DTree.parity y = !DTree.parity x := DTree.parity_flip x j
  rw [hparity x, hparity y, hflip] at heval
  cases hp : DTree.parity x <;> cases phase <;> simp [hp] at heval

/-- Cardinal form of the localization-aware support necessity theorem. -/
theorem Layered.bottomSupport_card_eq_of_eval_eq_parity_xor {n : ℕ}
    (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase) :
    (layeredBottomVariableSupport C).card = n := by
  rw [MultiSwitching.Layered.bottomSupport_eq_univ_of_eval_eq_parity_xor C phase hparity,
    Finset.card_univ, Fintype.card_fin]

/-- Duplicate normalization and adjoining the De Morgan polarity introduce no new variables. -/
theorem normalizedLayeredBottomFamily_support_subset_bottomSupport {n : ℕ}
    (C : Layered n) :
    familyVariableSupport (normalizedLayeredBottomFamily C) ⊆
      layeredBottomVariableSupport C := by
  intro v hv
  rw [familyVariableSupport] at hv
  obtain ⟨g, _hg, hvg⟩ := Finset.mem_biUnion.mp hv
  rw [gateVariableSupport] at hvg
  obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hvg
  have hTraw : T ∈ layeredBottomFamily C g :=
    (PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.mem_eraseDups_iff
      T _).mp (List.mem_toFinset.mp hT)
  have hgmem : layeredBottomFamily C g ∈ layeredBottomFamilyList C := by
    exact List.get_mem _ _
  rw [layeredBottomFamilyList, List.mem_append] at hgmem
  rw [layeredBottomVariableSupport]
  apply Finset.mem_biUnion.mpr
  rcases hgmem with hpos | hneg
  · exact ⟨layeredBottomFamily C g, List.mem_toFinset.mpr hpos,
      Finset.mem_biUnion.mpr ⟨T, List.mem_toFinset.mpr hTraw, hvT⟩⟩
  · obtain ⟨cs, hcs, hcsEq⟩ := List.mem_map.mp hneg
    refine ⟨cs, List.mem_toFinset.mpr hcs, ?_⟩
    rw [← gateVariableSupport_negDNF cs]
    rw [hcsEq]
    exact Finset.mem_biUnion.mpr ⟨T, List.mem_toFinset.mpr hTraw, hvT⟩

/-- The normalized two-polarity family has exactly the circuit's unpolarized bottom support.
The reverse inclusion uses the positive copy of each bottom gate; duplicate erasure preserves
membership, so neither normalization nor adjoining the negative polarity loses a variable. -/
theorem normalizedLayeredBottomFamily_support_eq_bottomSupport {n : ℕ}
    (C : Layered n) :
    familyVariableSupport (normalizedLayeredBottomFamily C) =
      layeredBottomVariableSupport C := by
  apply Finset.Subset.antisymm
  · exact normalizedLayeredBottomFamily_support_subset_bottomSupport C
  · intro v hv
    rw [layeredBottomVariableSupport] at hv
    obtain ⟨cs, hcs, hvcs⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hvcs
    obtain ⟨g, hg⟩ := List.get_of_mem
      (show cs ∈ layeredBottomFamilyList C by
        exact List.mem_append_left _ (List.mem_toFinset.mp hcs))
    rw [familyVariableSupport]
    apply Finset.mem_biUnion.mpr
    refine ⟨g, Finset.mem_univ g, ?_⟩
    rw [gateVariableSupport]
    apply Finset.mem_biUnion.mpr
    refine ⟨T, ?_, hvT⟩
    apply List.mem_toFinset.mpr
    apply (PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.mem_eraseDups_iff
      T _).mpr
    change T ∈ layeredBottomFamily C g
    rw [show layeredBottomFamily C g = cs by exact hg]
    exact List.mem_toFinset.mp hT

/-- A localized parity-equivalent circuit therefore gives the switching selector a genuinely
full-support normalized family, not merely a full-support unpolarized circuit. -/
theorem normalizedLayeredBottomFamily_support_eq_univ_of_eval_eq_parity_xor {n : ℕ}
    (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase) :
    familyVariableSupport (normalizedLayeredBottomFamily C) = Finset.univ := by
  rw [normalizedLayeredBottomFamily_support_eq_bottomSupport,
    Layered.bottomSupport_eq_univ_of_eval_eq_parity_xor C phase hparity]

/-- Every coordinate queried anywhere in a canonical gate tree occurs syntactically in that
gate.  Unlike the existing freshness theorem, this records the static support restriction and is
therefore useful when many ambient live variables are irrelevant to the family. -/
theorem canonicalDT_queriedVars_subset_gateVariableSupport {n : ℕ}
    (cs : List (Depth3.Clause n)) :
    ∀ fuel σ, queriedVars (canonicalDT cs fuel σ) ⊆ gateVariableSupport cs := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ
      rw [canonicalDT]
      split <;> simp [queriedVars]
  | succ fuel ih =>
      intro σ
      rw [canonicalDT]
      split
      · simp [queriedVars]
      · split
        · simp [queriedVars]
        · rename_i T hactive
          obtain ⟨ell, hhead, _hfree⟩ := activeTerm_first_free hactive
          simp only [hhead, queriedVars]
          intro v hv
          rw [Finset.mem_insert, Finset.mem_union] at hv
          rcases hv with rfl | hv | hv
          · apply Finset.mem_biUnion.mpr
            refine ⟨T, List.mem_toFinset.mpr
              (SwitchingCounting.activeTerm_mem hactive), ?_⟩
            apply List.mem_toFinset.mpr
            apply List.mem_map.mpr
            refine ⟨ell, ?_, rfl⟩
            have hellFree : ell ∈ freeLits σ T := List.mem_of_mem_head? hhead
            exact (List.mem_filter.mp hellFree).1
          · exact ih _ hv
          · exact ih _ hv

/-- Converting a canonical gate tree to its rejecting-path CNF introduces no variable outside
the source gate.  This is the leaf-level support invariant needed to propagate support through a
full collapse round. -/
theorem dtreeToCNF_canonicalDT_clauseVariableSupport_subset {n fuel : ℕ}
    (σ : Restriction n) (cs : List (Depth3.Clause n))
    (T : Depth3.Clause n)
    (hT : T ∈ dtreeToCNF (toDTree (canonicalDT cs fuel σ))) :
    clauseVariableSupport T ⊆ gateVariableSupport cs := by
  intro v hv
  have hv' : v ∈ T.lits.map litVarOf := by
    simpa [clauseVariableSupport, SwitchingCounting.litVar, Depth3.litVarOf] using
      (List.mem_toFinset.mp hv)
  have hquery := dtreeToCNF_litVars_subset
    (toDTree (canonicalDT cs fuel σ)) T hT v hv'
  rw [toDTree_queriedVars] at hquery
  exact canonicalDT_queriedVars_subset_gateVariableSupport cs fuel σ hquery

/-- Dual leaf support invariant: negating the canonical tree and taking its accepting-path DNF
still uses only variables of the original CNF payload. -/
theorem dtreeToDNF_negTree_canonicalDT_clauseVariableSupport_subset {n fuel : ℕ}
    (σ : Restriction n) (cs : List (Depth3.Clause n))
    (T : Depth3.Clause n)
    (hT : T ∈ dtreeToDNF
      (DTree.negTree (toDTree (canonicalDT (negDNF cs) fuel σ)))) :
    clauseVariableSupport T ⊆ gateVariableSupport cs := by
  intro v hv
  have hv' : v ∈ T.lits.map litVarOf := by
    simpa [clauseVariableSupport, SwitchingCounting.litVar, Depth3.litVarOf] using
      (List.mem_toFinset.mp hv)
  have hquery := dtreeToDNF_litVars_subset
    (DTree.negTree (toDTree (canonicalDT (negDNF cs) fuel σ))) T hT v hv'
  rw [DTree.negTree_queriedVars, toDTree_queriedVars] at hquery
  rw [← gateVariableSupport_negDNF cs]
  exact canonicalDT_queriedVars_subset_gateVariableSupport (negDNF cs) fuel σ hquery

/-- Gate-level form of the rejecting-path support invariant. -/
theorem gateVariableSupport_dtreeToCNF_canonicalDT_subset {n fuel : ℕ}
    (σ : Restriction n) (cs : List (Depth3.Clause n)) :
    gateVariableSupport (dtreeToCNF (toDTree (canonicalDT cs fuel σ))) ⊆
      gateVariableSupport cs := by
  intro v hv
  rw [gateVariableSupport] at hv
  obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hv
  exact dtreeToCNF_canonicalDT_clauseVariableSupport_subset σ cs T
    (List.mem_toFinset.mp hT) hvT

/-- Gate-level form of the dual accepting-path support invariant. -/
theorem gateVariableSupport_dtreeToDNF_negTree_canonicalDT_subset {n fuel : ℕ}
    (σ : Restriction n) (cs : List (Depth3.Clause n)) :
    gateVariableSupport (dtreeToDNF
      (DTree.negTree (toDTree (canonicalDT (negDNF cs) fuel σ)))) ⊆
      gateVariableSupport cs := by
  intro v hv
  rw [gateVariableSupport] at hv
  obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hv
  exact dtreeToDNF_negTree_canonicalDT_clauseVariableSupport_subset σ cs T
    (List.mem_toFinset.mp hT) hvT

/- Preservation-style companion to `leafCollapse_BottomPred`.  The older theorem is a setter:
it assumes the two switched shapes satisfy `P` for every source gate.  Support propagation needs
the source-sensitive form below, where `P` is assumed on the current bottom clauses and each leaf
conversion is only required to preserve it. -/
mutual
theorem leafCollapse_BottomPred_of {P : Depth3.Clause n → Prop} (fuel : ℕ)
    (σ : Restriction n)
    (hdnf : ∀ (cs : List (Depth3.Clause n)),
      (∀ T ∈ cs, P T) →
        ∀ T ∈ dtreeToCNF (toDTree (canonicalDT cs fuel σ)), P T)
    (hcnf : ∀ (cs : List (Depth3.Clause n)),
      (∀ T ∈ cs, P T) →
        ∀ T ∈ dtreeToDNF
          (DTree.negTree (toDTree (canonicalDT (negDNF cs) fuel σ))), P T) :
    ∀ {C : Layered n}, BottomPred P C → BottomPred P (leafCollapse fuel σ C)
  | Layered.dnf cs, h => by
      intro cs' hcs' T hT
      rw [show leafCollapse fuel σ (Layered.dnf cs) =
          Layered.cnf (dtreeToCNF (toDTree (canonicalDT cs fuel σ))) from rfl,
        show bottomGates
            (Layered.cnf (dtreeToCNF (toDTree (canonicalDT cs fuel σ)))) =
          [dtreeToCNF (toDTree (canonicalDT cs fuel σ))] from rfl,
        List.mem_singleton] at hcs'
      subst hcs'
      exact hdnf cs (fun U hU => h cs (by exact List.mem_cons_self) U hU) T hT
  | Layered.cnf cs, h => by
      intro cs' hcs' T hT
      rw [show leafCollapse fuel σ (Layered.cnf cs) =
          Layered.dnf (dtreeToDNF
            (DTree.negTree (toDTree (canonicalDT (negDNF cs) fuel σ)))) from rfl,
        show bottomGates
            (Layered.dnf (dtreeToDNF
              (DTree.negTree (toDTree (canonicalDT (negDNF cs) fuel σ))))) =
          [dtreeToDNF
            (DTree.negTree (toDTree (canonicalDT (negDNF cs) fuel σ)))] from rfl,
        List.mem_singleton] at hcs'
      subst hcs'
      exact hcnf cs (fun U hU => h cs (by exact List.mem_cons_self) U hU) T hT
  | Layered.gAnd gs, h => by
      show BottomPred P (Layered.gAnd (leafCollapseList fuel σ gs))
      intro cs' hcs' T hT
      rw [bottomGates_gAnd, bottomGatesList_eq, leafCollapseList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseList_BottomPred_of fuel σ hdnf hcnf gs
        (fun g' hg' => BottomPred_child_gAnd h hg') g hg cs' hcsl T hT
  | Layered.gOr gs, h => by
      show BottomPred P (Layered.gOr (leafCollapseList fuel σ gs))
      intro cs' hcs' T hT
      rw [bottomGates_gOr, bottomGatesList_eq, leafCollapseList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseList_BottomPred_of fuel σ hdnf hcnf gs
        (fun g' hg' => BottomPred_child_gOr h hg') g hg cs' hcsl T hT
theorem leafCollapseList_BottomPred_of {P : Depth3.Clause n → Prop} (fuel : ℕ)
    (σ : Restriction n)
    (hdnf : ∀ (cs : List (Depth3.Clause n)),
      (∀ T ∈ cs, P T) →
        ∀ T ∈ dtreeToCNF (toDTree (canonicalDT cs fuel σ)), P T)
    (hcnf : ∀ (cs : List (Depth3.Clause n)),
      (∀ T ∈ cs, P T) →
        ∀ T ∈ dtreeToDNF
          (DTree.negTree (toDTree (canonicalDT (negDNF cs) fuel σ))), P T) :
    ∀ (gs : List (Layered n)),
      (∀ g ∈ gs, BottomPred P g) →
        ∀ g ∈ gs, BottomPred P (leafCollapse fuel σ g)
  | [], _hall, g, hg => by simp at hg
  | ghead :: gs, hall, g, hg => by
      rcases List.mem_cons.mp hg with rfl | h
      · exact leafCollapse_BottomPred_of fuel σ hdnf hcnf (hall _ (by simp))
      · exact leafCollapseList_BottomPred_of fuel σ hdnf hcnf gs
          (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')) g h
end

/-- A `BottomPred` saying that every bottom clause is supported in `S` bounds the complete
bottom-layer support by `S`. -/
theorem layeredBottomVariableSupport_subset_of_BottomPred {n : ℕ}
    {C : Layered n} {S : Finset (Fin n)}
    (h : BottomPred (fun T => clauseVariableSupport T ⊆ S) C) :
    layeredBottomVariableSupport C ⊆ S := by
  intro v hv
  rw [layeredBottomVariableSupport] at hv
  obtain ⟨cs, hcs, hvcs⟩ := Finset.mem_biUnion.mp hv
  rw [gateVariableSupport] at hvcs
  obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hvcs
  exact h cs (List.mem_toFinset.mp hcs) T (List.mem_toFinset.mp hT) hvT

/-- The recursive leaf conversion introduces no bottom variable outside the original circuit's
bottom support. -/
theorem layeredBottomVariableSupport_leafCollapse_subset {n fuel : ℕ}
    (σ : Restriction n) (C : Layered n) :
    layeredBottomVariableSupport (leafCollapse fuel σ C) ⊆
      layeredBottomVariableSupport C := by
  apply layeredBottomVariableSupport_subset_of_BottomPred
  apply leafCollapse_BottomPred_of
    (P := fun T => clauseVariableSupport T ⊆ layeredBottomVariableSupport C) fuel σ
  · intro cs hcs T hT
    exact (dtreeToCNF_canonicalDT_clauseVariableSupport_subset σ cs T hT).trans
      (fun v hv => by
        rw [gateVariableSupport] at hv
        obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp hv
        exact hcs U (List.mem_toFinset.mp hU) hvU)
  · intro cs hcs T hT
    exact (dtreeToDNF_negTree_canonicalDT_clauseVariableSupport_subset σ cs T hT).trans
      (fun v hv => by
        rw [gateVariableSupport] at hv
        obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp hv
        exact hcs U (List.mem_toFinset.mp hU) hvU)
  · intro cs hcs T hT
    intro v hv
    rw [layeredBottomVariableSupport]
    exact Finset.mem_biUnion.mpr ⟨cs, List.mem_toFinset.mpr hcs,
      Finset.mem_biUnion.mpr ⟨T, List.mem_toFinset.mpr hT, hv⟩⟩

/-- A complete collapse round is support-nonincreasing: the leaf conversion preserves support,
and the merge pass only flattens existing bottom clauses. -/
theorem layeredBottomVariableSupport_collapseRound_subset {n fuel : ℕ}
    (σ : Restriction n) (C : Layered n) :
    layeredBottomVariableSupport (collapseRound fuel σ C) ⊆
      layeredBottomVariableSupport C := by
  apply layeredBottomVariableSupport_subset_of_BottomPred
  apply mergePass_BottomPred
  apply leafCollapse_BottomPred_of
    (P := fun T => clauseVariableSupport T ⊆ layeredBottomVariableSupport C) fuel σ
  · intro cs hcs T hT
    exact (dtreeToCNF_canonicalDT_clauseVariableSupport_subset σ cs T hT).trans
      (fun v hv => by
        rw [gateVariableSupport] at hv
        obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp hv
        exact hcs U (List.mem_toFinset.mp hU) hvU)
  · intro cs hcs T hT
    exact (dtreeToDNF_negTree_canonicalDT_clauseVariableSupport_subset σ cs T hT).trans
      (fun v hv => by
        rw [gateVariableSupport] at hv
        obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp hv
        exact hcs U (List.mem_toFinset.mp hU) hvU)
  · intro cs hcs T hT
    intro v hv
    rw [layeredBottomVariableSupport]
    exact Finset.mem_biUnion.mpr ⟨cs, List.mem_toFinset.mpr hcs,
      Finset.mem_biUnion.mpr ⟨T, List.mem_toFinset.mpr hT, hv⟩⟩

/-- A read-once common-family path pays only for coordinates that are both live and actually
owned by the gate family.  This sharpens the ambient `stars` bound when padding coordinates are
live but irrelevant to every gate. -/
theorem canonicalFamily_trace_length_le_live_support {n G : ℕ}
    (gates : Fin G → List (Depth3.Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length ≤
      ((familyVariableSupport gates).filter fun i ↦ σ i = none).card := by
  rw [CommonTree.trace_length_eq_queryVars_length]
  have hnd := CommonTree.queryVars_readOnce_nodup σ
    (canonicalFamilyTree gates fuel σ) x hext
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro v hv
  rw [Finset.mem_filter]
  have hvList : v ∈ CommonTree.queryVars
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x :=
    List.mem_toFinset.mp hv
  constructor
  · have hvRaw := CommonTree.mem_queryVars_of_mem_readOnce σ
      (canonicalFamilyTree gates fuel σ) x hext hvList
    rw [canonicalFamilyTree, CommonTree.queryVars_commonRefineFin] at hvRaw
    obtain ⟨segment, hsegment, hvSegment⟩ := List.mem_flatten.mp hvRaw
    obtain ⟨tree, htree, rfl⟩ := List.mem_map.mp hsegment
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp htree
    apply Finset.mem_biUnion.mpr
    refine ⟨g, Finset.mem_univ g, ?_⟩
    apply canonicalDT_queriedVars_subset_gateVariableSupport (gates g) fuel σ
    exact CommonTree.queryVars_ofBool_toFinset_subset_queriedVars
      (canonicalDT (gates g) fuel σ) x (List.mem_toFinset.mpr hvSegment)
  · exact mem_freeVars.mp
      (CommonTree.mem_queryVars_readOnce_freeVars σ
        (canonicalFamilyTree gates fuel σ) x hext hvList)

/-- Every coordinate queried by the canonical family prefix belongs to the family's syntactic
variable support.  In particular, the canonical certificate never spends an irrelevant ambient
coordinate merely because that coordinate is live at the root. -/
theorem canonicalFamily_prefixVars_subset_familyVariableSupport {n G : ℕ}
    (gates : Fin G → List (Depth3.Clause n)) (fuel : ℕ) (σ : Restriction n)
    (budget : ℕ) (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    CommonTree.prefixVars σ (canonicalFamilyTree gates fuel σ) budget x ⊆
      familyVariableSupport gates := by
  intro v hv
  have hvPrefix : v ∈ CommonTree.queryVars
      (CommonTree.prefixEndpoints σ (canonicalFamilyTree gates fuel σ) budget) x :=
    List.mem_toFinset.mp hv
  rw [CommonTree.queryVars_prefixEndpoints] at hvPrefix
  have hvRead : v ∈ CommonTree.queryVars
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x :=
    List.mem_of_mem_take hvPrefix
  have hvRaw := CommonTree.mem_queryVars_of_mem_readOnce σ
    (canonicalFamilyTree gates fuel σ) x hext hvRead
  rw [canonicalFamilyTree, CommonTree.queryVars_commonRefineFin] at hvRaw
  obtain ⟨segment, hsegment, hvSegment⟩ := List.mem_flatten.mp hvRaw
  obtain ⟨tree, htree, rfl⟩ := List.mem_map.mp hsegment
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp htree
  apply Finset.mem_biUnion.mpr
  refine ⟨g, Finset.mem_univ g, ?_⟩
  apply canonicalDT_queriedVars_subset_gateVariableSupport (gates g) fuel σ
  exact CommonTree.queryVars_ofBool_toFinset_subset_queriedVars
    (canonicalDT (gates g) fuel σ) x (List.mem_toFinset.mpr hvSegment)

/-- All root-live coordinates outside the family support remain live at the canonical prefix
leaf.  This is the structural half of the correlated survivor-capacity argument. -/
theorem freeVars_sdiff_familySupport_subset_canonicalPrefixEndpoint {n G : ℕ}
    (gates : Fin G → List (Depth3.Clause n)) (fuel : ℕ) (σ : Restriction n)
    (budget : ℕ) (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    freeVars σ \ familyVariableSupport gates ⊆
      freeVars (CommonTree.prefixEndpoint σ (canonicalFamilyTree gates fuel σ) budget x) := by
  rw [CommonTree.freeVars_prefixEndpoint]
  intro v hv
  rw [Finset.mem_sdiff] at hv ⊢
  refine ⟨hv.1, ?_⟩
  intro hvPrefix
  exact hv.2 (canonicalFamily_prefixVars_subset_familyVariableSupport
    gates fuel σ budget x hext hvPrefix)

/-- If the trunk budget covers the live part of the actual family support, irrelevant ambient
survivors need not be charged.  Ample fuel is still stated using the full live count because it
is what makes each completed canonical member path semantically terminal. -/
theorem commonShallowAt_zero_of_live_support_le {n G : ℕ}
    (gates : Fin G → List (Depth3.Clause n)) (fuel : ℕ) (σ : Restriction n)
    (trunkDepth : ℕ) (hstarsFuel : stars σ ≤ fuel)
    (hsupport : ((familyVariableSupport gates).filter fun i ↦ σ i = none).card ≤
      trunkDepth) :
    CommonShallowAt gates fuel σ trunkDepth 0 := by
  apply commonShallowAt_of_prefix_residual gates fuel σ trunkDepth 0
  intro x hext g
  have htrace : (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length ≤
      trunkDepth :=
    (canonicalFamily_trace_length_le_live_support gates fuel σ x hext).trans hsupport
  have hend := CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
    σ (canonicalFamilyTree gates fuel σ) trunkDepth x htrace
  rw [CommonTree.prefixEndpoint] at hend
  rw [hend]
  exact Nat.le_of_eq (canonicalDT_depth_eq_zero_of_terminal (gates g)
    (CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) x)
    (canonicalFamily_pathEndpoint_terminal gates fuel σ x hext hstarsFuel g) fuel)

/-- Pointwise form of `commonShallowAt_zero_of_live_support_le`: the specific canonical prefix
used by the support-respecting survivor construction leaves every family member at depth zero.
Exposing the canonical leaf, rather than only an existential common trunk, is what lets the same
leaf feed both the zero-overlap selector and the layered collapse round. -/
theorem canonicalFamily_prefix_depth_eq_zero_of_live_support_le {n G : ℕ}
    (gates : Fin G → List (Depth3.Clause n)) (fuel : ℕ) (σ : Restriction n)
    (trunkDepth : ℕ) (hstarsFuel : stars σ ≤ fuel)
    (hsupport : ((familyVariableSupport gates).filter fun i ↦ σ i = none).card ≤
      trunkDepth) (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) (g : Fin G) :
    (canonicalDT (gates g) fuel
      (CommonTree.prefixEndpoint σ (canonicalFamilyTree gates fuel σ) trunkDepth x)).depth = 0 := by
  have htrace : (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length ≤
      trunkDepth :=
    (canonicalFamily_trace_length_le_live_support gates fuel σ x hext).trans hsupport
  have hend := CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
    σ (canonicalFamilyTree gates fuel σ) trunkDepth x htrace
  rw [hend]
  exact canonicalDT_depth_eq_zero_of_terminal (gates g)
    (CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) x)
    (canonicalFamily_pathEndpoint_terminal gates fuel σ x hext hstarsFuel g) fuel

/-- The root-local support tail on the exact `K`-star shell.  This is intentionally independent
of fixed Boolean values: it is a necessary envelope for the bad event, not an exact semantic
classification. -/
noncomputable def liveFamilySupportTail {n G : ℕ}
    (gates : Fin G → List (Depth3.Clause n)) (K trunkDepth : ℕ) :
    Finset (Restriction n) :=
  Finset.univ.filter fun σ =>
    stars σ = K ∧
      trunkDepth < ((familyVariableSupport gates).filter fun i ↦ σ i = none).card

theorem mem_liveFamilySupportTail_iff {n G : ℕ}
    {gates : Fin G → List (Depth3.Clause n)} {K trunkDepth : ℕ}
    {σ : Restriction n} :
    σ ∈ liveFamilySupportTail gates K trunkDepth ↔
      stars σ = K ∧
        trunkDepth < ((familyVariableSupport gates).filter fun i ↦ σ i = none).card := by
  simp [liveFamilySupportTail]

/-- With ample fuel, querying all live family-support coordinates proves that every bad root lies
in the strict live-support tail.  The conclusion holds for every requested residual depth because
the support trunk actually leaves residual depth zero. -/
theorem commonShallowBad_subset_liveFamilySupportTail
    {n G fuel K trunkDepth residualDepth : ℕ}
    {gates : Fin G → List (Depth3.Clause n)} (hKfuel : K ≤ fuel) :
    commonShallowBad gates fuel K trunkDepth residualDepth ⊆
      liveFamilySupportTail gates K trunkDepth := by
  intro σ hσ
  rw [mem_liveFamilySupportTail_iff]
  obtain ⟨hstars, hbad⟩ := mem_commonShallowBad.mp hσ
  refine ⟨hstars, ?_⟩
  by_contra hnot
  apply hbad
  apply CommonShallowAt.mono
    (commonShallowAt_zero_of_live_support_le gates fuel σ trunkDepth
      (by simpa [hstars] using hKfuel) (Nat.le_of_not_gt hnot))
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-- The corresponding tail measured using the circuit's unpolarized syntactic bottom support.
This is the sharp circuit-owned event: adjoining the second polarity and erasing duplicates do not
enlarge its support. -/
noncomputable def liveLayeredBottomSupportTail {n : ℕ}
    (C : Layered n) (K trunkDepth : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter fun σ =>
    stars σ = K ∧
      trunkDepth < ((layeredBottomVariableSupport C).filter fun i ↦ σ i = none).card

theorem mem_liveLayeredBottomSupportTail_iff {n : ℕ} {C : Layered n}
    {K trunkDepth : ℕ} {σ : Restriction n} :
    σ ∈ liveLayeredBottomSupportTail C K trunkDepth ↔
      stars σ = K ∧
        trunkDepth < ((layeredBottomVariableSupport C).filter fun i ↦ σ i = none).card := by
  simp [liveLayeredBottomSupportTail]

/-! ### Dense-support endpoint of the support-tail method

The tail estimate below is useful only when the circuit support leaves substantial ambient room.
At the opposite endpoint, where the bottom support is the whole cube, the hypergeometric random
variable is deterministic: every live coordinate lies in the support.  Recording this before the
general counting formula makes the applicability boundary explicit. -/

/-- With full bottom support, the number of live support coordinates is exactly `stars σ`. -/
theorem live_bottomSupport_card_eq_stars_of_eq_univ {n : ℕ} {C : Layered n}
    (hfull : layeredBottomVariableSupport C = Finset.univ) (σ : Restriction n) :
    ((layeredBottomVariableSupport C).filter fun i ↦ σ i = none).card = stars σ := by
  rw [hfull]
  apply congrArg Finset.card
  ext i
  simp [mem_freeVars]

/-- If the support is full and the trunk budget is smaller than the shell size, the support tail
is not merely large: it is the entire shell.  Thus there is no root outside the tail from which
the current zero-overlap survivor selector could start. -/
theorem liveLayeredBottomSupportTail_eq_shell_of_full_support
    {n K trunkDepth : ℕ} {C : Layered n}
    (hfull : layeredBottomVariableSupport C = Finset.univ)
    (hdepth : trunkDepth < K) :
    liveLayeredBottomSupportTail C K trunkDepth =
      Finset.univ.filter fun σ : Restriction n ↦ stars σ = K := by
  ext σ
  rw [mem_liveLayeredBottomSupportTail_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [live_bottomSupport_card_eq_stars_of_eq_univ hfull]
  constructor
  · intro h
    exact h.1
  · intro hstars
    exact ⟨hstars, by omega⟩

/-- Exact dense-support specialization of the hypergeometric tail count. -/
theorem liveLayeredBottomSupportTail_card_of_full_support
    {n K trunkDepth : ℕ} {C : Layered n}
    (hfull : layeredBottomVariableSupport C = Finset.univ)
    (hdepth : trunkDepth < K) :
    (liveLayeredBottomSupportTail C K trunkDepth).card =
      n.choose K * 2 ^ (n - K) := by
  rw [liveLayeredBottomSupportTail_eq_shell_of_full_support hfull hdepth,
    SwitchingCounting.card_stars_eq]

/-- At the parameters used by the initial geometric successor, every full-support root is bad for
the support-tail selector.  In particular its required `σ ∉ tail` premise is impossible for
positive survivor scale. -/
theorem fullSupport_halfShell_mem_liveLayeredBottomSupportTail
    {n R : ℕ} {C : Layered n}
    (hfull : layeredBottomVariableSupport C = Finset.univ)
    (hR : 0 < R) {σ : Restriction n} (hstars : stars σ = 20 * R) :
    σ ∈ liveLayeredBottomSupportTail C (20 * R) (10 * R) := by
  rw [liveLayeredBottomSupportTail_eq_shell_of_full_support hfull (by omega)]
  simp [hstars]

/-! ### Exact hypergeometric support-tail count

The semantic reduction above leaves a purely support-theoretic event.  We expose its fixed-overlap
classes separately: this keeps the exact binomial summand available even when the final tail sum
is too coarse for the circuit recurrence. -/

/-- Restrictions on the `K`-star shell with exactly `q` live coordinates in a fixed support. -/
noncomputable def liveSupportOverlap {n : ℕ} (support : Finset (Fin n))
    (K q : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter fun σ =>
    stars σ = K ∧ (support.filter fun i ↦ σ i = none).card = q

theorem mem_liveSupportOverlap_iff {n K q : ℕ} {support : Finset (Fin n)}
    {σ : Restriction n} :
    σ ∈ liveSupportOverlap support K q ↔
      stars σ = K ∧ (support.filter fun i ↦ σ i = none).card = q := by
  simp [liveSupportOverlap]

/-- Free-variable sets underlying one fixed support-overlap class. -/
def liveSupportOverlapFreeSets {n : ℕ} (support : Finset (Fin n))
    (K q : ℕ) : Finset (Finset (Fin n)) :=
  occupancySizeFiber (fun _ : Fin 1 => support) (fun _ => q) (K - q)

theorem mem_liveSupportOverlapFreeSets_iff {n K q : ℕ}
    {support : Finset (Fin n)} {S : Finset (Fin n)} :
    S ∈ liveSupportOverlapFreeSets support K q ↔
      (S ∩ support).card = q ∧ (S \ support).card = K - q := by
  rw [liveSupportOverlapFreeSets, mem_occupancySizeFiber]
  simp [supportUnion]

/-- The free-set part of a fixed overlap class is the usual hypergeometric product. -/
theorem liveSupportOverlapFreeSets_card {n K q : ℕ}
    (support : Finset (Fin n)) :
    (liveSupportOverlapFreeSets support K q).card =
      support.card.choose q * (n - support.card).choose (K - q) := by
  rw [liveSupportOverlapFreeSets,
    occupancySizeFiber_card_uniform
      (fun _ : Fin 1 => support)
      (fun g h hne => False.elim (hne (Subsingleton.elim g h)))
      (fun _ => rfl)]
  simp

theorem mem_liveSupportOverlap_iff_freeSet {n K q : ℕ}
    {support : Finset (Fin n)} (hq : q ≤ K) (σ : Restriction n) :
    σ ∈ liveSupportOverlap support K q ↔
      freeVars σ ∈ liveSupportOverlapFreeSets support K q := by
  rw [mem_liveSupportOverlap_iff, mem_liveSupportOverlapFreeSets_iff]
  have hinter : (freeVars σ ∩ support).card =
      (support.filter fun i ↦ σ i = none).card := by
    apply congrArg Finset.card
    ext i
    simp [mem_freeVars, and_comm]
  rw [hinter]
  constructor
  · rintro ⟨hstars, hoverlap⟩
    refine ⟨hoverlap, ?_⟩
    have hpartition := Finset.card_sdiff_add_card_inter (freeVars σ) support
    rw [stars] at hstars
    omega
  · rintro ⟨hoverlap, houtside⟩
    refine ⟨?_, hoverlap⟩
    rw [stars]
    have hpartition := Finset.card_sdiff_add_card_inter (freeVars σ) support
    omega

/-- Exact cardinality of one support-overlap class.  Boolean values on all `n-K` fixed
coordinates are unrestricted, so every free set contributes the common factor `2^(n-K)`. -/
theorem liveSupportOverlap_card {n K q : ℕ} (support : Finset (Fin n))
    (hq : q ≤ K) :
    (liveSupportOverlap support K q).card =
      support.card.choose q * (n - support.card).choose (K - q) * 2 ^ (n - K) := by
  classical
  have hmaps : Set.MapsTo (fun σ : Restriction n => freeVars σ)
      (liveSupportOverlap support K q : Set (Restriction n))
      (liveSupportOverlapFreeSets support K q : Set (Finset (Fin n))) := by
    intro σ hσ
    rw [Finset.mem_coe] at hσ ⊢
    exact (mem_liveSupportOverlap_iff_freeSet hq σ).mp hσ
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hterm : ∀ S ∈ liveSupportOverlapFreeSets support K q,
      ((liveSupportOverlap support K q).filter (fun σ => freeVars σ = S)).card =
        2 ^ (n - K) := by
    intro S hS
    have hScard : S.card = K := by
      have hoverlap := (mem_liveSupportOverlapFreeSets_iff).mp hS
      have hpartition := Finset.card_sdiff_add_card_inter S support
      omega
    have heq : (liveSupportOverlap support K q).filter (fun σ => freeVars σ = S) =
        Finset.univ.filter (fun σ : Restriction n => freeVars σ = S) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hfree
        refine ⟨?_, hfree⟩
        rw [mem_liveSupportOverlap_iff_freeSet hq, hfree]
        exact hS
    rw [heq, card_freeVars_eq, hScard]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
    liveSupportOverlapFreeSets_card]

/-- The circuit-owned tail is the disjoint union of its exact overlap classes. -/
theorem liveLayeredBottomSupportTail_eq_biUnion_overlap {n K trunkDepth : ℕ}
    (C : Layered n) :
    liveLayeredBottomSupportTail C K trunkDepth =
      (Finset.Icc (trunkDepth + 1) K).biUnion
        (liveSupportOverlap (layeredBottomVariableSupport C) K) := by
  ext σ
  rw [mem_liveLayeredBottomSupportTail_iff]
  simp only [Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨hstars, hlive⟩
    let q := ((layeredBottomVariableSupport C).filter fun i ↦ σ i = none).card
    have hqle : q ≤ K := by
      have hfilter :
          ((layeredBottomVariableSupport C).filter fun i ↦ σ i = none) ⊆ freeVars σ := by
        intro i hi
        exact mem_freeVars.mpr (Finset.mem_filter.mp hi).2
      calc q ≤ (freeVars σ).card := Finset.card_le_card hfilter
        _ = K := hstars
    refine ⟨q, ⟨by omega, hqle⟩, ?_⟩
    rw [mem_liveSupportOverlap_iff]
    exact ⟨hstars, rfl⟩
  · rintro ⟨q, hq, hσ⟩
    rw [mem_liveSupportOverlap_iff] at hσ
    exact ⟨hσ.1, by omega⟩

/-- Exact hypergeometric cardinality of the circuit-owned live-support tail. -/
theorem liveLayeredBottomSupportTail_card {n K trunkDepth : ℕ} (C : Layered n) :
    (liveLayeredBottomSupportTail C K trunkDepth).card =
      ∑ q ∈ Finset.Icc (trunkDepth + 1) K,
        (layeredBottomVariableSupport C).card.choose q *
          (n - (layeredBottomVariableSupport C).card).choose (K - q) * 2 ^ (n - K) := by
  have hpair : ((Finset.Icc (trunkDepth + 1) K : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (liveSupportOverlap (layeredBottomVariableSupport C) K) := by
    intro q hq r hr hne
    change Disjoint (liveSupportOverlap (layeredBottomVariableSupport C) K q)
      (liveSupportOverlap (layeredBottomVariableSupport C) K r)
    rw [Finset.disjoint_left]
    intro σ hσq hσr
    rw [mem_liveSupportOverlap_iff] at hσq hσr
    exact hne (hσq.2.symm.trans hσr.2)
  rw [liveLayeredBottomSupportTail_eq_biUnion_overlap,
    Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro q hq
  exact liveSupportOverlap_card _ (Finset.mem_Icc.mp hq).2

/-- Circuit-specialized support-tail reduction.  Every normalized-family bad root is charged to
more than `trunkDepth` live coordinates in the original, unpolarized bottom-gate support. -/
theorem normalizedLayered_commonShallowBad_subset_liveBottomSupportTail
    {n fuel K trunkDepth residualDepth : ℕ} {C : Layered n}
    (hKfuel : K ≤ fuel) :
    commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth residualDepth ⊆
      liveLayeredBottomSupportTail C K trunkDepth := by
  intro σ hσ
  rw [mem_liveLayeredBottomSupportTail_iff]
  obtain ⟨hstars, hbad⟩ := mem_commonShallowBad.mp hσ
  refine ⟨hstars, ?_⟩
  by_contra hnot
  apply hbad
  apply CommonShallowAt.mono
    (commonShallowAt_zero_of_live_support_le
      (normalizedLayeredBottomFamily C) fuel σ trunkDepth
      (by simpa [hstars] using hKfuel) ?_)
  · exact Nat.le_refl _
  · exact Nat.zero_le _
  apply (Finset.card_le_card ?_).trans (Nat.le_of_not_gt hnot)
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨normalizedLayeredBottomFamily_support_subset_bottomSupport C hi.1, hi.2⟩

/-- After the common fixed-value factor is cancelled, the exact hypergeometric coefficient is
the only numerical obligation needed to contract the normalized circuit bad set.  This packages
the support-tail reduction and keeps the remaining estimate independent of the `2^(n-K)` Boolean
fibers. -/
theorem normalizedLayered_commonShallowBad_scaled_le_of_hypergeometric_tail
    {n fuel K trunkDepth residualDepth savingExponent : ℕ} {C : Layered n}
    (hKfuel : K ≤ fuel)
    (htail :
      (∑ q ∈ Finset.Icc (trunkDepth + 1) K,
          (layeredBottomVariableSupport C).card.choose q *
            (n - (layeredBottomVariableSupport C).card).choose (K - q)) *
          2 ^ savingExponent ≤ n.choose K) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth
        residualDepth).card * 2 ^ savingExponent ≤
      (Finset.univ.filter fun σ : Restriction n ↦ stars σ = K).card := by
  have hsubset := normalizedLayered_commonShallowBad_subset_liveBottomSupportTail
    (C := C) (trunkDepth := trunkDepth) (residualDepth := residualDepth) hKfuel
  have hcard :
      (commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth
          residualDepth).card ≤
        (liveLayeredBottomSupportTail C K trunkDepth).card :=
    Finset.card_le_card hsubset
  rw [liveLayeredBottomSupportTail_card] at hcard
  rw [SwitchingCounting.card_stars_eq]
  rw [← Finset.sum_mul] at hcard
  calc
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth
        residualDepth).card * 2 ^ savingExponent ≤
        ((∑ q ∈ Finset.Icc (trunkDepth + 1) K,
            (layeredBottomVariableSupport C).card.choose q *
              (n - (layeredBottomVariableSupport C).card).choose (K - q)) *
            2 ^ (n - K)) * 2 ^ savingExponent := Nat.mul_le_mul_right _ hcard
    _ = ((∑ q ∈ Finset.Icc (trunkDepth + 1) K,
            (layeredBottomVariableSupport C).card.choose q *
              (n - (layeredBottomVariableSupport C).card).choose (K - q)) *
            2 ^ savingExponent) * 2 ^ (n - K) := by ring
    _ ≤ n.choose K * 2 ^ (n - K) := Nat.mul_le_mul_right _ htail

/-- Replicating every ambient coordinate `c` times contains, as a distinguished subfamily, every
`r`-subset of the original coordinates with one of `c` labels independently attached to each
member.  The descending-factorial proof avoids any division. -/
theorem pow_mul_choose_le_choose_mul (c a r : ℕ) :
    c ^ r * a.choose r ≤ (c * a).choose r := by
  by_cases hc : c = 0
  · subst c
    cases r <;> simp
  have hcpos : 0 < c := Nat.pos_of_ne_zero hc
  have hdesc : c ^ r * a.descFactorial r ≤ (c * a).descFactorial r := by
    induction r with
    | zero => simp
    | succ r ih =>
        rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ]
        by_cases hra : r ≤ a
        · have hfactor : c * (a - r) ≤ c * a - r := by
            rw [Nat.mul_sub_left_distrib c a r]
            exact Nat.sub_le_sub_left (Nat.le_mul_of_pos_left r hcpos) _
          calc
            c ^ r * c * ((a - r) * a.descFactorial r) =
                (c * (a - r)) * (c ^ r * a.descFactorial r) := by ring
            _ ≤ (c * a - r) * (c ^ r * a.descFactorial r) :=
              Nat.mul_le_mul_right _ hfactor
            _ ≤ (c * a - r) * (c * a).descFactorial r :=
              Nat.mul_le_mul_left _ ih
        · have har : a - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hra)
          simp [har]
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hcanc : (c ^ r * a.choose r) * r.factorial ≤
      (c * a).choose r * r.factorial := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdesc
  exact Nat.le_of_mul_le_mul_right hcanc (Nat.factorial_pos _)

/-- In the nonzero support-tail regime, sixteenfold ambient density makes the enlarged
`n + 31*a` binomial row cost at most four choices per selected coordinate. -/
theorem choose_add_thirtyone_mul_le_four_pow_choose
    {n a d : ℕ} (hdensity : 16 * a ≤ n) (hsupport : d + 1 ≤ a) :
    (n + 31 * a).choose (2 * d) ≤ 4 ^ (2 * d) * n.choose (2 * d) := by
  have hdesc : ∀ r ≤ 2 * d,
      (n + 31 * a).descFactorial r ≤ 4 ^ r * n.descFactorial r := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
        rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ]
        have hrlt : r < 2 * d := by omega
        have hrn : r ≤ n := by omega
        have hfactor : n + 31 * a - r ≤ 4 * (n - r) := by omega
        calc
          (n + 31 * a - r) * (n + 31 * a).descFactorial r ≤
              (4 * (n - r)) * (n + 31 * a).descFactorial r :=
            Nat.mul_le_mul_right _ hfactor
          _ ≤ (4 * (n - r)) * (4 ^ r * n.descFactorial r) :=
            Nat.mul_le_mul_left _ (ih (by omega))
          _ = 4 ^ r * 4 * ((n - r) * n.descFactorial r) := by ring
  have h := hdesc (2 * d) (Nat.le_refl _)
  simp only [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hcanc : (n + 31 * a).choose (2 * d) * (2 * d).factorial ≤
      (4 ^ (2 * d) * n.choose (2 * d)) * (2 * d).factorial := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  exact Nat.le_of_mul_le_mul_right hcanc (Nat.factorial_pos _)

/-- A weighted Vandermonde envelope for the without-replacement upper tail.  Each selected support
coordinate receives one of `32` labels, and the resulting distinguished subsets live inside an
ambient set of size `n + 31*a`. -/
theorem hypergeometric_upper_tail_mul_thirtytwo_pow_le
    {n a d : ℕ} (ha : a ≤ n) :
    (∑ q ∈ Finset.Icc (d + 1) (2 * d),
        a.choose q * (n - a).choose (2 * d - q)) * 32 ^ (d + 1) ≤
      (n + 31 * a).choose (2 * d) := by
  calc
    (∑ q ∈ Finset.Icc (d + 1) (2 * d),
        a.choose q * (n - a).choose (2 * d - q)) * 32 ^ (d + 1) =
        ∑ q ∈ Finset.Icc (d + 1) (2 * d),
          (a.choose q * (n - a).choose (2 * d - q)) * 32 ^ (d + 1) := by
            rw [Finset.sum_mul]
    _ ≤ ∑ q ∈ Finset.Icc (d + 1) (2 * d),
          (32 * a).choose q * (n - a).choose (2 * d - q) := by
      apply Finset.sum_le_sum
      intro q hq
      have hpow : 32 ^ (d + 1) ≤ 32 ^ q :=
        pow_le_pow_right' (by norm_num) (Finset.mem_Icc.mp hq).1
      calc
        (a.choose q * (n - a).choose (2 * d - q)) * 32 ^ (d + 1) ≤
            (a.choose q * (n - a).choose (2 * d - q)) * 32 ^ q :=
          Nat.mul_le_mul_left _ hpow
        _ = (32 ^ q * a.choose q) * (n - a).choose (2 * d - q) := by ring
        _ ≤ (32 * a).choose q * (n - a).choose (2 * d - q) :=
          Nat.mul_le_mul_right _ (pow_mul_choose_le_choose_mul 32 a q)
    _ ≤ ∑ q ∈ Finset.range (2 * d + 1),
          (32 * a).choose q * (n - a).choose (2 * d - q) := by
      apply Finset.sum_le_sum_of_subset
      intro q hq
      rw [Finset.mem_Icc] at hq
      simpa [Finset.mem_range] using hq.2
    _ = (32 * a + (n - a)).choose (2 * d) := by
      rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = (n + 31 * a).choose (2 * d) := by
      apply congrArg (fun x : ℕ => Nat.choose x (2 * d))
      calc
        32 * a + (n - a) = (n - a) + a + 31 * a := by ring
        _ = n + 31 * a := by rw [Nat.sub_add_cancel ha]

/-- Generic without-replacement half-shell tail bound.  A support occupying at most one sixteenth
of the ambient coordinates has probability at most `2^-d` of contributing more than half of a
`2*d` sample.  The statement remains valid when `2*d > n` (both relevant binomial rows vanish). -/
theorem hypergeometric_upper_tail_sixteen_density
    {n a d : ℕ} (hdensity : 16 * a ≤ n) :
    (∑ q ∈ Finset.Icc (d + 1) (2 * d),
        a.choose q * (n - a).choose (2 * d - q)) * 2 ^ d ≤ n.choose (2 * d) := by
  by_cases hsmall : a ≤ d
  · have hzero : ∑ q ∈ Finset.Icc (d + 1) (2 * d),
        a.choose q * (n - a).choose (2 * d - q) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      simp [Nat.choose_eq_zero_of_lt
        (lt_of_le_of_lt hsmall (Finset.mem_Icc.mp hq).1)]
    simp [hzero]
  have hsupport : d + 1 ≤ a := by omega
  have ha : a ≤ n := by omega
  let tail := ∑ q ∈ Finset.Icc (d + 1) (2 * d),
      a.choose q * (n - a).choose (2 * d - q)
  have hweighted : tail * 32 ^ (d + 1) ≤
      4 ^ (2 * d) * n.choose (2 * d) :=
    (hypergeometric_upper_tail_mul_thirtytwo_pow_le ha).trans
      (choose_add_thirtyone_mul_le_four_pow_choose hdensity hsupport)
  have hscale : 2 ^ d * 4 ^ (2 * d) ≤ 32 ^ (d + 1) := by
    calc
      2 ^ d * 4 ^ (2 * d) = 2 ^ d * (4 ^ 2) ^ d := by rw [pow_mul]
      _ = (2 * 4 ^ 2) ^ d := by rw [mul_pow]
      _ = 32 ^ d := by norm_num
      _ ≤ 32 ^ (d + 1) := pow_le_pow_right' (by norm_num) (by omega)
  have hmul : (tail * 2 ^ d) * (4 ^ (2 * d)) ≤
      n.choose (2 * d) * (4 ^ (2 * d)) := by
    calc
      (tail * 2 ^ d) * 4 ^ (2 * d) = tail * (2 ^ d * 4 ^ (2 * d)) := by ring
      _ ≤ tail * 32 ^ (d + 1) := Nat.mul_le_mul_left _ hscale
      _ ≤ 4 ^ (2 * d) * n.choose (2 * d) := hweighted
      _ = n.choose (2 * d) * 4 ^ (2 * d) := by ring
  exact Nat.le_of_mul_le_mul_right hmul (pow_pos (by norm_num) _)

/-- The strengthened bad event needed by overlap-aware iteration—the complete root support tail,
not merely failure of common shallowness—has the same half-shell contraction.  Excluding this tail
simultaneously gives a canonical shallow trunk and enough irrelevant live coordinates for the
next survivor cube. -/
theorem liveLayeredBottomSupportTail_scaled_le_sixteen_density
    {n R : ℕ} {C : Layered n}
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n) :
    (liveLayeredBottomSupportTail C (20 * R) (10 * R)).card * 2 ^ (10 * R) ≤
      (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card := by
  rw [liveLayeredBottomSupportTail_card, SwitchingCounting.card_stars_eq]
  have htail := hypergeometric_upper_tail_sixteen_density
    (d := 10 * R) hsupport
  rw [show 20 * R = 2 * (10 * R) by ring]
  rw [← Finset.sum_mul]
  calc
    ((∑ q ∈ Finset.Icc (10 * R + 1) (2 * (10 * R)),
          (layeredBottomVariableSupport C).card.choose q *
            (n - (layeredBottomVariableSupport C).card).choose (2 * (10 * R) - q)) *
        2 ^ (n - 2 * (10 * R))) * 2 ^ (10 * R) =
        ((∑ q ∈ Finset.Icc (10 * R + 1) (2 * (10 * R)),
          (layeredBottomVariableSupport C).card.choose q *
            (n - (layeredBottomVariableSupport C).card).choose (2 * (10 * R) - q)) *
          2 ^ (10 * R)) * 2 ^ (n - 2 * (10 * R)) := by ring
    _ ≤ n.choose (2 * (10 * R)) * 2 ^ (n - 2 * (10 * R)) :=
      Nat.mul_le_mul_right _ htail

theorem clauseVariableSupport_card_le_width {n w : ℕ} {T : Depth3.Clause n}
    (hw : T.lits.length ≤ w) : (clauseVariableSupport T).card ≤ w := by
  exact (List.toFinset_card_le _).trans (by simpa using hw)

theorem gateVariableSupport_card_le {n w : ℕ} {cs : List (Depth3.Clause n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    (gateVariableSupport cs).card ≤ w * cs.length := by
  calc
    (gateVariableSupport cs).card ≤
        ∑ T ∈ cs.toFinset, (clauseVariableSupport T).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ cs.toFinset, w := by
      apply Finset.sum_le_sum
      intro T hT
      exact clauseVariableSupport_card_le_width (hw T (List.mem_toFinset.mp hT))
    _ = cs.toFinset.card * w := by simp
    _ ≤ cs.length * w := Nat.mul_le_mul_right w (List.toFinset_card_le cs)
    _ = w * cs.length := Nat.mul_comm _ _

/-- Width times the exact ragged alphabet bounds the family's complete coordinate support. -/
theorem familyVariableSupport_card_le {n G w : ℕ}
    {gates : Fin G → List (Depth3.Clause n)}
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w) :
    (familyVariableSupport gates).card ≤ w * ∑ g, (gates g).length := by
  calc
    (familyVariableSupport gates).card ≤
        ∑ g, (gateVariableSupport (gates g)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ g, w * (gates g).length := by
      apply Finset.sum_le_sum
      intro g _
      exact gateVariableSupport_card_le (hw g)
    _ = w * ∑ g, (gates g).length := by rw [Finset.mul_sum]

/-- A list of width-`w` gates owns at most width times its number of clause occurrences.  The list
form deliberately avoids charging duplicate gates twice merely to pass through `toFinset`. -/
private theorem listGateVariableSupport_card_le {n w : ℕ} :
    ∀ css : List (List (Depth3.Clause n)),
      (∀ cs ∈ css, ∀ T ∈ cs, T.lits.length ≤ w) →
      (css.toFinset.biUnion gateVariableSupport).card ≤
        w * (css.map List.length).sum
  | [] => by simp
  | cs :: css => by
      intro hw
      have hhead : (gateVariableSupport cs).card ≤ w * cs.length :=
        gateVariableSupport_card_le (hw cs (by simp))
      have htail : (css.toFinset.biUnion gateVariableSupport).card ≤
          w * (css.map List.length).sum :=
        listGateVariableSupport_card_le css (by
          intro cs' hcs'
          exact hw cs' (by simp [hcs']))
      rw [List.toFinset_cons, Finset.biUnion_insert, List.map_cons, List.sum_cons]
      calc
        (gateVariableSupport cs ∪ css.toFinset.biUnion gateVariableSupport).card ≤
            (gateVariableSupport cs).card +
              (css.toFinset.biUnion gateVariableSupport).card :=
          Finset.card_union_le _ _
        _ ≤ w * cs.length + w * (css.map List.length).sum := Nat.add_le_add hhead htail
        _ = w * (cs.length + (css.map List.length).sum) := by rw [Nat.mul_add]

/-- The variables owned by the unpolarized bottom gates cost at most width times their actual
clause occurrences. -/
theorem layeredBottomVariableSupport_card_le {n w : ℕ} {C : Layered n}
    (hw : BottomWidth w C) :
    (layeredBottomVariableSupport C).card ≤ w * bottomClauseCount C := by
  exact listGateVariableSupport_card_le (bottomGates C) hw

/-- The circuit-owned recurrence margin forces a strong support-density gap: even at the maximal
width/slot charge, the unpolarized bottom support occupies at most one sixteenth of the ambient
coordinates.  This is the quantitative regime needed by the remaining hypergeometric tail lemma;
unlike the earlier prefix estimate, it contains no extra factor of the shell size. -/
theorem sixteen_mul_layeredBottomVariableSupport_card_le_of_actual_margin
    {n s : ℕ} {C : Layered n} (hw : BottomWidth (s + 1) C)
    (hmargin :
      8 * (s + 2) * bottomSlotCount C * 2 ^ (s + 1) + 4 * (s + 2) ≤ n) :
    16 * (layeredBottomVariableSupport C).card ≤ n := by
  have hsupport :
      (layeredBottomVariableSupport C).card ≤ (s + 1) * bottomSlotCount C :=
    (layeredBottomVariableSupport_card_le hw).trans
      (Nat.mul_le_mul_left (s + 1) (bottomClauseCount_le_bottomSlotCount C))
  have hpow : 2 ≤ 2 ^ (s + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_left 2 (pow_pos (by omega) s)
  calc
    16 * (layeredBottomVariableSupport C).card ≤
        16 * ((s + 1) * bottomSlotCount C) := Nat.mul_le_mul_left 16 hsupport
    _ ≤ 8 * (s + 2) * bottomSlotCount C * 2 ^ (s + 1) := by
      nlinarith
    _ ≤ 8 * (s + 2) * bottomSlotCount C * 2 ^ (s + 1) + 4 * (s + 2) :=
      Nat.le_add_right _ _
    _ ≤ n := hmargin

/-- The actual circuit-owned recurrence margin now closes the support-only contraction at the
intended half-shell parameters `K = 20*R`, `d = 10*R`. -/
theorem normalizedLayered_commonShallowBad_scaled_le_of_actual_margin
    {n fuel s R residualDepth : ℕ} {C : Layered n}
    (hKfuel : 20 * R ≤ fuel)
    (hw : BottomWidth (s + 1) C)
    (hmargin :
      8 * (s + 2) * bottomSlotCount C * 2 ^ (s + 1) + 4 * (s + 2) ≤ n) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel (20 * R) (10 * R)
        residualDepth).card * 2 ^ (10 * R) ≤
      (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card := by
  apply normalizedLayered_commonShallowBad_scaled_le_of_hypergeometric_tail hKfuel
  simpa [show 20 * R = 2 * (10 * R) by ring] using
    hypergeometric_upper_tail_sixteen_density
      (sixteen_mul_layeredBottomVariableSupport_card_le_of_actual_margin hw hmargin)

/-- Support-sensitive form of the normalized half-shell contraction.  Unlike the historical
`actual_margin` interface, this charges each variable used by the bottom layer only once, so it
remains applicable when the circuit has many overlapping clause occurrences. -/
theorem normalizedLayered_commonShallowBad_scaled_le_of_sixteen_support
    {n fuel R residualDepth : ℕ} {C : Layered n}
    (hKfuel : 20 * R ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel (20 * R) (10 * R)
        residualDepth).card * 2 ^ (10 * R) ≤
      (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card := by
  apply normalizedLayered_commonShallowBad_scaled_le_of_hypergeometric_tail hKfuel
  simpa [show 20 * R = 2 * (10 * R) by ring] using
    hypergeometric_upper_tail_sixteen_density hsupport

/-- Complete survivor-round interface under the exact distinct-variable support density.  Slot
count is retained only in the output recurrence; it is absent from the round-zero density premise. -/
theorem supportDensity_normalizedSurvivorRound
    {n fuel R residualDepth : ℕ} {C : Layered n}
    (hKfuel : 20 * R ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hne : NonEmptyGates C) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel (20 * R) (10 * R)
        residualDepth).card * 2 ^ (10 * R) ≤
        (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card ∧
      ∀ σ : Restriction n,
        stars σ = 20 * R →
        σ ∉ commonShallowBad (normalizedLayeredBottomFamily C) fuel
          (20 * R) (10 * R) residualDepth →
        ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
          ∃ trunk : CommonTree n (Restriction n),
            CommonTree.depth trunk ≤ 10 * R ∧
            let τ := CommonTree.run trunk x
            10 * R ≤ stars τ ∧
            stars τ ≤ fuel ∧
            bottomSlotCount (collapseRound fuel τ C) ≤
              bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) := by
  constructor
  · exact normalizedLayered_commonShallowBad_scaled_le_of_sixteen_support hKfuel hsupport
  · intro σ hstars hgood x hx
    have hcommon : CommonShallowAt (normalizedLayeredBottomFamily C) fuel σ
        (10 * R) residualDepth := by
      by_contra hnot
      apply hgood
      rw [mem_commonShallowBad]
      exact ⟨hstars, hnot⟩
    have hfuel : stars σ ≤ fuel := by
      calc
        stars σ = 20 * R := hstars
        _ ≤ fuel := hKfuel
    obtain ⟨trunk, hdepth, hlower, hleafFuel, hslot⟩ :=
      hcommon.leaf_collapseRound_bottomSlotCount_bound hfuel
        (normalizedLayeredBottomFamily_covers C) hne x hx
    refine ⟨trunk, hdepth, ?_, hleafFuel, hslot⟩
    rw [hstars] at hlower
    omega

/-- One complete normalized survivor-round interface at the actual circuit-owned margin.  The
first conjunct is the half-shell bad-set contraction.  The second says that every root outside
that bad set supplies the common trunk and, at every reached leaf, the slot-count recurrence
needed to formulate the following round's margin. -/
theorem actualMargin_normalizedSurvivorRound
    {n fuel s R residualDepth : ℕ} {C : Layered n}
    (hKfuel : 20 * R ≤ fuel)
    (hw : BottomWidth (s + 1) C)
    (hmargin :
      8 * (s + 2) * bottomSlotCount C * 2 ^ (s + 1) + 4 * (s + 2) ≤ n)
    (hne : NonEmptyGates C) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel (20 * R) (10 * R)
        residualDepth).card * 2 ^ (10 * R) ≤
        (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card ∧
      ∀ σ : Restriction n,
        stars σ = 20 * R →
        σ ∉ commonShallowBad (normalizedLayeredBottomFamily C) fuel
          (20 * R) (10 * R) residualDepth →
        ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
          ∃ trunk : CommonTree n (Restriction n),
            CommonTree.depth trunk ≤ 10 * R ∧
            let τ := CommonTree.run trunk x
            10 * R ≤ stars τ ∧
            stars τ ≤ fuel ∧
            bottomSlotCount (collapseRound fuel τ C) ≤
              bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) := by
  constructor
  · exact normalizedLayered_commonShallowBad_scaled_le_of_actual_margin
      hKfuel hw hmargin
  · intro σ hstars hgood x hx
    have hcommon : CommonShallowAt (normalizedLayeredBottomFamily C) fuel σ
        (10 * R) residualDepth := by
      by_contra hnot
      apply hgood
      rw [mem_commonShallowBad]
      exact ⟨hstars, hnot⟩
    have hfuel : stars σ ≤ fuel := by
      calc
        stars σ = 20 * R := hstars
        _ ≤ fuel := hKfuel
    obtain ⟨trunk, hdepth, hlower, hleafFuel, hslot⟩ :=
      hcommon.leaf_collapseRound_bottomSlotCount_bound hfuel
        (normalizedLayeredBottomFamily_covers C) hne x hx
    refine ⟨trunk, hdepth, ?_, hleafFuel, hslot⟩
    rw [hstars] at hlower
    omega

#print axioms actualMargin_normalizedSurvivorRound

/-- Support-density survivor round with an exact half-shell subcube at every reached leaf. -/
theorem supportDensity_normalizedSurvivorRound_exactSubcube
    {n fuel R residualDepth : ℕ} {C : Layered n}
    (hKfuel : 20 * R ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hne : NonEmptyGates C) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel (20 * R) (10 * R)
        residualDepth).card * 2 ^ (10 * R) ≤
        (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card ∧
      ∀ σ : Restriction n,
        stars σ = 20 * R →
        σ ∉ commonShallowBad (normalizedLayeredBottomFamily C) fuel
          (20 * R) (10 * R) residualDepth →
        ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
          ∃ trunk : CommonTree n (Restriction n),
            CommonTree.depth trunk ≤ 10 * R ∧
            let tau := CommonTree.run trunk x
            ∃ kappa : Restriction n,
              RestrictionExtends tau kappa ∧
              stars kappa = 10 * R ∧
              stars kappa ≤ fuel ∧
              Layered.EquivOn kappa C (collapseRound fuel tau C) ∧
              bottomSlotCount (collapseRound fuel tau C) ≤
                bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) := by
  obtain ⟨hbad, hleaf⟩ :=
    supportDensity_normalizedSurvivorRound hKfuel hsupport hne
  refine ⟨hbad, ?_⟩
  intro σ hstars hgood x hx
  obtain ⟨trunk, hdepth, hlive, hleafFuel, hslot⟩ :=
    hleaf σ hstars hgood x hx
  obtain ⟨kappa, hext, hkappaStars⟩ :=
    exists_restrictionExtends_stars_eq (CommonTree.run trunk x) hlive
  refine ⟨trunk, hdepth, kappa, hext, hkappaStars, ?_, ?_, hslot⟩
  · rw [hkappaStars]
    omega
  · intro y hy
    exact collapseRound_EquivOn fuel hleafFuel C y
      (fun i b hi => hy i b (hext i b hi))

/-- The actual-margin survivor round admits an exact half-shell subcube at every reached leaf.
Besides selecting an extension with exactly `10*R` live coordinates, the conclusion transports
the existing collapse equivalence from the trunk leaf to that finer subcube.  The circuit still
lives over the original ambient coordinate type; reindexing its live coordinates is a separate
interface. -/
theorem actualMargin_normalizedSurvivorRound_exactSubcube
    {n fuel s R residualDepth : ℕ} {C : Layered n}
    (hKfuel : 20 * R ≤ fuel)
    (hw : BottomWidth (s + 1) C)
    (hmargin :
      8 * (s + 2) * bottomSlotCount C * 2 ^ (s + 1) + 4 * (s + 2) ≤ n)
    (hne : NonEmptyGates C) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel (20 * R) (10 * R)
        residualDepth).card * 2 ^ (10 * R) ≤
        (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card ∧
      ∀ σ : Restriction n,
        stars σ = 20 * R →
        σ ∉ commonShallowBad (normalizedLayeredBottomFamily C) fuel
          (20 * R) (10 * R) residualDepth →
        ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
          ∃ trunk : CommonTree n (Restriction n),
            CommonTree.depth trunk ≤ 10 * R ∧
            let tau := CommonTree.run trunk x
            ∃ kappa : Restriction n,
              RestrictionExtends tau kappa ∧
              stars kappa = 10 * R ∧
              stars kappa ≤ fuel ∧
              Layered.EquivOn kappa C (collapseRound fuel tau C) ∧
              bottomSlotCount (collapseRound fuel tau C) ≤
                bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) := by
  obtain ⟨hbad, hleaf⟩ :=
    actualMargin_normalizedSurvivorRound hKfuel hw hmargin hne
  refine ⟨hbad, ?_⟩
  intro σ hstars hgood x hx
  obtain ⟨trunk, hdepth, hlive, hleafFuel, hslot⟩ :=
    hleaf σ hstars hgood x hx
  obtain ⟨kappa, hext, hkappaStars⟩ :=
    exists_restrictionExtends_stars_eq (CommonTree.run trunk x) hlive
  refine ⟨trunk, hdepth, kappa, hext, hkappaStars, ?_, ?_, hslot⟩
  · rw [hkappaStars]
    omega
  · intro y hy
    exact collapseRound_EquivOn fuel hleafFuel C y
      (fun i b hi => hy i b (hext i b hi))

/-! ### Dense-support common-shallow nonemptiness -/

/-- Even the exact queried-variable-subset factor cannot pay for a half-shell contraction when
its support alphabet already covers the ambient live cube.  This statement keeps both binomial
coefficients exact: after cancelling the Boolean shell fibers, `choose n r` occurs once from the
smaller shell and once again inside `choose A r`, while `choose n (2*r)` is at most their product.
The requested saving and the downward-shell Boolean charge then make the inequality strict. -/
theorem not_supportSubset_exact_balance_half_of_live_le_supportAlphabet
    {n A r : ℕ} (hr : 0 < r) (h2rn : 2 * r ≤ n) (hle : n ≤ A) :
    ¬(Nat.choose n (2 * r - r) * 2 ^ (n - (2 * r - r)) *
          Nat.choose A r * 2 ^ r ≤
        Nat.choose n (2 * r) * 2 ^ (n - 2 * r)) := by
  intro h
  have hsub : 2 * r - r = r := by omega
  rw [hsub] at h
  have hexp : n - r = (n - 2 * r) + r := by omega
  rw [hexp, pow_add] at h
  have hp : 0 < 2 ^ (n - 2 * r) := by positivity
  have hc : n.choose r * (2 ^ (2 * r) * A.choose r) ≤ n.choose (2 * r) := by
    apply Nat.le_of_mul_le_mul_left _ hp
    convert h using 1 <;> ring
  have hlabel : n.choose r ≤ A.choose r := Nat.choose_le_choose r hle
  have hchoose : n.choose (2 * r) ≤ n.choose r * n.choose r := by
    have hmul := Nat.choose_mul (n := n) (k := 2 * r) (s := r) (by omega)
    have hcentral : 0 < (2 * r).choose r := Nat.choose_pos (by omega)
    have hstep : n.choose (2 * r) ≤ n.choose r * (n - r).choose r := by
      apply Nat.le_of_mul_le_mul_left _ hcentral
      calc
        (2 * r).choose r * n.choose (2 * r) =
            n.choose (2 * r) * (2 * r).choose r := by ring
        _ = n.choose r * (n - r).choose r := by simpa [hsub] using hmul
        _ ≤ (2 * r).choose r * (n.choose r * (n - r).choose r) := by
          exact Nat.le_mul_of_pos_left _ hcentral
    exact hstep.trans (Nat.mul_le_mul_left _
      (Nat.choose_le_choose r (Nat.sub_le n r)))
  have hnr : 0 < n.choose r := Nat.choose_pos (by omega)
  have htwo : 2 ≤ 2 ^ (2 * r) := by
    calc
      2 = 2 ^ 1 := by simp
      _ ≤ 2 ^ (2 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hstrict : n.choose r * n.choose r <
      n.choose r * (2 ^ (2 * r) * A.choose r) := by
    apply Nat.mul_lt_mul_of_pos_left _ hnr
    calc
      n.choose r ≤ A.choose r := hlabel
      _ < 2 * A.choose r := by
        have hAr : 0 < A.choose r := Nat.choose_pos (by omega)
        omega
      _ ≤ 2 ^ (2 * r) * A.choose r := Nat.mul_le_mul_right _ htwo
  exact (Nat.not_lt_of_ge hc) (hchoose.trans_lt hstrict)

/-- Full normalized support makes the exact support-subset half-shell balance impossible for a
width-two family.  Unlike the rectangular-density no-go below, this rules out the sharper encoder
that remembers only the `10*r` queried variables: full support forces its ambient alphabet
`2 * ∑_g |gate_g|` to have cardinality at least `n`. -/
theorem not_normalizedLayered_supportSubset_balance_of_full_support
    {n r : ℕ} {C : Layered n}
    (hr : 0 < r) (hKn : 20 * r ≤ n) (hw : BottomWidth 2 C)
    (hsupport : familyVariableSupport (normalizedLayeredBottomFamily C) = Finset.univ) :
    ¬((Finset.univ.filter fun τ : Restriction n => stars τ = 20 * r - 10 * r).card *
          Nat.choose (2 * ∑ g, (normalizedLayeredBottomFamily C g).length) (10 * r) *
          2 ^ (10 * r) ≤
        (Finset.univ.filter fun σ : Restriction n => stars σ = 20 * r).card) := by
  have hsupportCard : n =
      (familyVariableSupport (normalizedLayeredBottomFamily C)).card := by
    rw [hsupport, Finset.card_univ, Fintype.card_fin]
  have hle : n ≤ 2 * ∑ g, (normalizedLayeredBottomFamily C g).length := by
    calc
      n = (familyVariableSupport (normalizedLayeredBottomFamily C)).card := hsupportCard
      _ ≤ 2 * ∑ g, (normalizedLayeredBottomFamily C g).length :=
        familyVariableSupport_card_le (normalizedLayeredBottomFamily_width_le hw)
  rw [card_stars_eq (N := n) (K := 20 * r - 10 * r),
    card_stars_eq (N := n) (K := 20 * r)]
  have htwenty : 20 * r = 2 * (10 * r) := by ring
  rw [htwenty]
  exact not_supportSubset_exact_balance_half_of_live_le_supportAlphabet
    (r := 10 * r) (by omega) (by simpa [htwenty] using hKn) hle

/-- Semantic form of the exact support-subset no-go: localized parity XOR a phase forces the full
support premise used above, so the queried-variable-set balance is vacuous on every nonempty
`20*r` shell. -/
theorem not_normalizedLayered_supportSubset_balance_of_eval_eq_parity_xor
    {n r : ℕ} {C : Layered n} (phase : Bool)
    (hr : 0 < r) (hKn : 20 * r ≤ n) (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase) :
    ¬((Finset.univ.filter fun τ : Restriction n => stars τ = 20 * r - 10 * r).card *
          Nat.choose (2 * ∑ g, (normalizedLayeredBottomFamily C g).length) (10 * r) *
          2 ^ (10 * r) ≤
        (Finset.univ.filter fun σ : Restriction n => stars σ = 20 * r).card) :=
  not_normalizedLayered_supportSubset_balance_of_full_support hr hKn hw
    (normalizedLayeredBottomFamily_support_eq_univ_of_eval_eq_parity_xor
      C phase hparity)

/-- Full normalized support is incompatible with the rectangular realized-density premise on any
positive shell.  At width two, support counting forces the exact indexed gate/term rectangle
`G*m` to carry at least half of the ambient coordinates.  The density base already charges more
than twice that rectangle before its positive shell multiplier is applied.  Thus the dense-parity
specialization below has inconsistent semantic and quantitative premises; iterating its successor
cannot repair the obstruction. -/
theorem not_normalizedLayered_realized_density_of_full_support
    {n m r : ℕ} {C : Layered n}
    (hr : 0 < r) (hw : BottomWidth 2 C) (hcount : BottomCount m C)
    (hsupport : familyVariableSupport (normalizedLayeredBottomFamily C) = Finset.univ) :
    ¬((4 * ((2 + 1) * ((layeredBottomFamilyList C).length * m + 1))) *
          (20 * r) + 20 * r ≤ n + 1) := by
  let A := (layeredBottomFamilyList C).length * m
  have htotal : (∑ g, (normalizedLayeredBottomFamily C g).length) ≤ A := by
    dsimp only [A]
    calc
      (∑ g, (normalizedLayeredBottomFamily C g).length) ≤ ∑ _g, m := by
        apply Finset.sum_le_sum
        intro g _
        exact normalizedLayeredBottomFamily_length_le hcount g
      _ = (layeredBottomFamilyList C).length * m := by simp
  have hnA : n ≤ 2 * A := by
    have hsupportCard : n =
        (familyVariableSupport (normalizedLayeredBottomFamily C)).card := by
      rw [hsupport, Finset.card_univ, Fintype.card_fin]
    rw [hsupportCard]
    exact (familyVariableSupport_card_le
      (normalizedLayeredBottomFamily_width_le hw)).trans
        (Nat.mul_le_mul_left 2 htotal)
  have hK : 0 < 20 * r := Nat.mul_pos (by omega) hr
  intro hdensity
  have hstrict : n + 1 < 12 * (A + 1) * (20 * r) + 20 * r := by
    calc
      n + 1 ≤ 2 * A + 1 := Nat.add_le_add_right hnA 1
      _ < 12 * (A + 1) := by omega
      _ ≤ 12 * (A + 1) * (20 * r) := Nat.le_mul_of_pos_right _ hK
      _ < 12 * (A + 1) * (20 * r) + 20 * r := Nat.lt_add_of_pos_right hK
  have hstrict' : n + 1 <
      (4 * ((2 + 1) * ((layeredBottomFamilyList C).length * m + 1))) *
        (20 * r) + 20 * r := by
    have hcoef : 12 * (A + 1) =
        4 * ((2 + 1) * ((layeredBottomFamilyList C).length * m + 1)) := by
      simp only [A, Nat.reduceAdd]
      ring
    rw [← hcoef]
    exact hstrict
  exact (Nat.not_lt_of_ge hdensity) hstrict'

/-- Semantic specialization of the no-go theorem: a width-two circuit computing parity XOR a
fixed phase can never satisfy the positive-shell rectangular density premise used by the proposed
dense successor. -/
theorem not_normalizedLayered_realized_density_of_eval_eq_parity_xor
    {n m r : ℕ} {C : Layered n} (phase : Bool)
    (hr : 0 < r) (hw : BottomWidth 2 C) (hcount : BottomCount m C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase) :
    ¬((4 * ((2 + 1) * ((layeredBottomFamilyList C).length * m + 1))) *
          (20 * r) + 20 * r ≤ n + 1) :=
  not_normalizedLayered_realized_density_of_full_support hr hw hcount
    (normalizedLayeredBottomFamily_support_eq_univ_of_eval_eq_parity_xor
      C phase hparity)

/-- Circuit-specialized strict nonemptiness at the realized rectangular density.  This removes
the abstract `Fin G` family from the interface: the circuit supplies its exact two-polarity gate
count and the `BottomCount m` hypothesis supplies the rectangular clause bound. -/
theorem exists_normalizedLayered_commonShallowAt_of_realized_density
    {n m r fuel residualDepth : ℕ} {C : Layered n}
    (hr : 0 < r)
    (hw : BottomWidth 2 C) (hcount : BottomCount m C)
    (hKfuel : 20 * r ≤ fuel) (hKn : 20 * r ≤ n)
    (hdensity :
      (4 * ((2 + 1) * ((layeredBottomFamilyList C).length * m + 1))) *
          (20 * r) + 20 * r ≤ n + 1) :
    ∃ σ : Restriction n,
      stars σ = 20 * r ∧
      CommonShallowAt (normalizedLayeredBottomFamily C) fuel σ
        (10 * r) residualDepth := by
  let shell := Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * r
  let bad := commonShallowBad (normalizedLayeredBottomFamily C) fuel
    (20 * r) (10 * r) residualDepth
  have hscaled : bad.card * 2 ^ (10 * r) ≤ shell.card := by
    have hbound := normalizedLayered_commonShallowBad_scaled_le_of_realized_density
      (d := 10 * r) (residualDepth := residualDepth)
      (savingNum := 1) (savingDen := 2)
      hw hcount hKfuel (by omega) (by omega) hKn (by omega) hdensity
    have hhalf : (20 * r) / 2 = 10 * r := by omega
    simp only [one_mul] at hbound
    rw [hhalf] at hbound
    simpa [bad, shell] using hbound
  have hshellPos : 0 < shell.card := by
    rw [show shell.card = Nat.choose n (20 * r) * 2 ^ (n - 20 * r) by
      simpa [shell] using card_stars_eq n (20 * r)]
    exact Nat.mul_pos (Nat.choose_pos hKn) (pow_pos (by omega) _)
  have hsaving : 2 ≤ 2 ^ (10 * r) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (10 * r) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcard : bad.card < shell.card := by
    nlinarith
  obtain ⟨σ, hσshell, hσbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hstars : stars σ = 20 * r := by
    simpa [shell] using hσshell
  refine ⟨σ, hstars, ?_⟩
  by_contra hnot
  apply hσbad
  rw [mem_commonShallowBad]
  exact ⟨hstars, hnot⟩

/-- Full variable support does not make the geometric common-shallow selector vacuous.  Under the
realized-family density hypotheses, a full-support family still has a `20*r`-star root with a
`10*r` common trunk and the requested residual depth.  The support premise is deliberately absent
from the proof of the cardinal contraction: retaining all live variables is compatible with
canonical common shallowness. -/
theorem exists_commonShallowAt_linearGap_realized_of_full_support
    {G m r fuel residualDepth : ℕ}
    {gates : Fin G → List (Clause (1000 * (G * m) * r))}
    (hG : 0 < G) (hm : 0 < m) (hr : 0 < r)
    (_hfull : familyVariableSupport gates = Finset.univ)
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ 2)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : 20 * r ≤ fuel) :
    ∃ σ : Restriction (1000 * (G * m) * r),
      stars σ = 20 * r ∧
      CommonShallowAt gates fuel σ (10 * r) residualDepth :=
  exists_commonShallowAt_linearGap_realized hG hm hr hnd hw hgate hKfuel

/-! ### Fixed-value profiles do not give a uniform endpoint saving

The earlier independent-singleton regression used only the all-false fixed profile.  The next
two lemmas remove that artifact: every restriction in a nontrivial live shell is bad for this
family at residual depth zero, independently of all values fixed outside the live set. -/

/-- Complete an arbitrary restriction by setting its live coordinates to false. -/
def restrictionFalseCompletion {n : ℕ} (sigma : Restriction n) : Fin n → Bool :=
  fun i => (sigma i).getD false

theorem restrictionFalseCompletion_extends {n : ℕ} (sigma : Restriction n) :
    Rung4Restriction.Extends sigma (restrictionFalseCompletion sigma) := by
  intro i b hi
  simp [restrictionFalseCompletion, hi]

/-- Independent positive singleton gates saturate the residual-zero bad event for every fixed
Boolean profile, not only for the all-false roots used in the ordered-fiber example. -/
theorem restriction_not_commonShallowAt_independentLiteral_zero {n d : ℕ}
    (sigma : Restriction n) (hd : d < stars sigma) :
    ¬ CommonShallowAt (independentLiteralGates n) 1 sigma d 0 := by
  rintro ⟨trunk, hdepth, hleaf⟩
  let x := restrictionFalseCompletion sigma
  have hx : Rung4Restriction.Extends sigma x := restrictionFalseCompletion_extends sigma
  have hpathCard : (CommonTree.queryVars trunk x).toFinset.card ≤ d := by
    calc
      (CommonTree.queryVars trunk x).toFinset.card ≤
          (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ d := hdepth
  have hnotSubset : ¬ freeVars sigma ⊆ (CommonTree.queryVars trunk x).toFinset := by
    intro hsubset
    have hcard := Finset.card_le_card hsubset
    rw [← stars] at hcard
    omega
  obtain ⟨i, hiFree, hiPath⟩ := Finset.not_subset.mp hnotSubset
  have hisigma : sigma i = none := by simpa [mem_freeVars] using hiFree
  have hxi : x i = false := by simp [x, restrictionFalseCompletion, hisigma]
  let y : Fin n → Bool := Function.update x i true
  have hy : Rung4Restriction.Extends sigma y := by
    intro j b hj
    have hji : j ≠ i := by
      intro h
      subst j
      rw [hisigma] at hj
      contradiction
    simpa [y, Function.update_of_ne hji] using hx j b hj
  obtain ⟨_, htx, hshallowx⟩ := hleaf x hx
  obtain ⟨_, hty, _⟩ := hleaf y hy
  have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
    simpa [y, hxi] using
      CommonTree.run_update_of_not_mem_queryVars trunk x i (by simpa using hiPath)
  have hfree : CommonTree.run trunk x i = none := by
    cases ht : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : b = false := by
          exact (htx i b ht).symm.trans hxi
        have hby : b = true := by
          have hty' : CommonTree.run trunk y i = some b := by simpa [hrun] using ht
          have hyi : y i = true := by simp [y]
          exact (hty i b hty').symm.trans hyi
        exact False.elim (Bool.false_ne_true (hbx.symm.trans hby))
  have hdeep := independentLiteral_canonicalDT_depth_of_free
    (CommonTree.run trunk x) i hfree
  have hzero := hshallowx i
  omega

/-- Consequently the complete `K`-star shell, including every fixed-value profile, is exactly the
semantic bad set for independent singletons whenever the trunk is strictly shorter than the live
shell.  Endpoint-local profile averaging alone therefore cannot be a uniform source of saving. -/
theorem commonShallowBad_independentLiteral_zero_eq_shell {n K d : ℕ} (hd : d < K) :
    commonShallowBad (independentLiteralGates n) 1 K d 0 =
      (Finset.univ : Finset (Restriction n)).filter fun sigma => stars sigma = K := by
  ext sigma
  rw [mem_commonShallowBad]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.1
  · intro hstars
    exact ⟨hstars, restriction_not_commonShallowAt_independentLiteral_zero sigma (by omega)⟩

/-! ### Exact live-support classification for singleton families

The full-shell obstruction above has one singleton gate for every ambient coordinate.  The
density-aware version should instead distinguish ambient coordinates from the coordinates
actually owned by the family.  For singleton gates this distinction is exact: residual depth zero
costs precisely the number of distinct owned coordinates that remain live, regardless of repeated
ownership or the fixed Boolean profile. -/

/-- One positive singleton gate for each coordinate selected by `v`.  The selector need not be
injective, so this family also models arbitrary repeated ownership. -/
def selectedLiteralGates {n G : ℕ} (v : Fin G → Fin n) :
    Fin G → List (Clause n) :=
  fun g => [⟨[Rung4Literal.pos (v g)]⟩]

@[simp] theorem familyVariableSupport_selectedLiteralGates {n G : ℕ}
    (v : Fin G → Fin n) :
    familyVariableSupport (selectedLiteralGates v) = Finset.univ.image v := by
  ext i
  simp [familyVariableSupport, gateVariableSupport, clauseVariableSupport,
    selectedLiteralGates, eq_comm]
  constructor <;> rintro ⟨g, hg⟩ <;> exact ⟨g, by simpa using hg⟩

/-- A selected singleton whose coordinate is live has canonical depth one at every positive
fuel. -/
theorem selectedLiteral_canonicalDT_depth_of_free {n G fuel : ℕ}
    (v : Fin G → Fin n) (ρ : Restriction n) (g : Fin G)
    (hfuel : 0 < fuel) (hfree : ρ (v g) = none) :
    (canonicalDT (selectedLiteralGates v g) fuel ρ).depth = 1 := by
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  let cs : List (Clause n) := selectedLiteralGates v g
  have hfalse : CanonicalTerminal cs (fixVar ρ (v g) false) := by
    right
    simp [cs, selectedLiteralGates, activeTerm, anyTermSat, termSat,
      termFalsified, freeLits, Depth3.litTrue, litFixedVal, litFalse,
      litFree, fixVar]
  have htrue : CanonicalTerminal cs (fixVar ρ (v g) true) := by
    left
    simp [cs, selectedLiteralGates, anyTermSat, termSat, Depth3.litTrue,
      litFixedVal, fixVar]
  have hdFalse :
      (canonicalDT cs fuel (fixVar ρ (v g) false)).depth = 0 :=
    canonicalDT_depth_eq_zero_of_terminal cs _ hfalse fuel
  have hdTrue :
      (canonicalDT cs fuel (fixVar ρ (v g) true)).depth = 0 :=
    canonicalDT_depth_eq_zero_of_terminal cs _ htrue fuel
  have hroot : canonicalDT cs (fuel + 1) ρ =
      BoolDecisionTree.query (v g)
        (canonicalDT cs fuel (fixVar ρ (v g) false))
        (canonicalDT cs fuel (fixVar ρ (v g) true)) := by
    simp [canonicalDT, cs, selectedLiteralGates, anyTermSat, termSat, activeTerm,
      termFalsified, freeLits, Depth3.litTrue, litVar, litFixedVal, litFalse,
      litFree, hfree]
  rw [show selectedLiteralGates v g = cs by rfl, hroot]
  simp [BoolDecisionTree.depth, hdFalse, hdTrue]

/-- A selected singleton is always residual-depth at most one, independently of fuel and of the
root restriction.  This is the positive-residual benchmark against which width-two interactions
must be compared: unlike the residual-zero event, no live-support tail remains at all. -/
theorem selectedLiteral_canonicalDT_depth_le_one {n G fuel : ℕ}
    (v : Fin G → Fin n) (rho : Restriction n) (g : Fin G) :
    (canonicalDT (selectedLiteralGates v g) fuel rho).depth ≤ 1 := by
  by_cases hfuel : fuel = 0
  · subst fuel
    exact (canonicalDT_depth_le (selectedLiteralGates v g) 0 rho).trans (by omega)
  by_cases hfree : rho (v g) = none
  · rw [selectedLiteral_canonicalDT_depth_of_free v rho g (by omega) hfree]
  cases hvg : rho (v g) with
  | none => exact (hfree hvg).elim
  | some b =>
      have hterminal : CanonicalTerminal (selectedLiteralGates v g) rho := by
        cases b
        · right
          simp [selectedLiteralGates, activeTerm, anyTermSat, termSat,
            termFalsified, freeLits, Depth3.litTrue, litFixedVal, litFalse,
            litFree, hvg]
        · left
          simp [selectedLiteralGates, anyTermSat, termSat, Depth3.litTrue,
            litFixedVal, hvg]
      rw [canonicalDT_depth_eq_zero_of_terminal
        (selectedLiteralGates v g) rho hterminal fuel]
      omega

/-- Every selected-singleton family has a zero-query common trunk at residual depth one.  Thus
its semantic bad set is empty for every shell and every trunk budget at this residual threshold. -/
theorem commonShallowAt_selectedLiteral_one {n G fuel trunkDepth : ℕ}
    (v : Fin G → Fin n) (sigma : Restriction n) :
    CommonShallowAt (selectedLiteralGates v) fuel sigma trunkDepth 1 := by
  refine ⟨CommonTree.leaf sigma, by simp [CommonTree.depth], ?_⟩
  intro x hx
  exact ⟨fun _ _ h => h, hx, selectedLiteral_canonicalDT_depth_le_one v sigma⟩

/-- If more than `d` distinct selected coordinates remain live, no depth-`d` common trunk can
make every selected singleton residual-constant.  This is independent of fixed values and of
duplicate selectors. -/
theorem selectedLiteral_not_commonShallowAt_zero {n G fuel d : ℕ}
    (v : Fin G → Fin n) (sigma : Restriction n)
    (hfuel : stars sigma ≤ fuel)
    (hlive : d < ((Finset.univ.image v).filter fun i => sigma i = none).card) :
    ¬ CommonShallowAt (selectedLiteralGates v) fuel sigma d 0 := by
  rintro ⟨trunk, hdepth, hleaf⟩
  let x := restrictionFalseCompletion sigma
  have hx : Rung4Restriction.Extends sigma x := restrictionFalseCompletion_extends sigma
  let live := (Finset.univ.image v).filter fun i => sigma i = none
  let path := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ d := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ d := hdepth
  have hnotSubset : ¬ live ⊆ path := by
    intro hsubset
    have hlivePath : live.card ≤ path.card := Finset.card_le_card hsubset
    have hliveD : live.card ≤ d := hlivePath.trans hpathCard
    exact (Nat.not_le_of_gt (by simpa [live] using hlive))
      (by simpa [live] using hliveD)
  obtain ⟨i, hiLive, hiPath⟩ := Finset.not_subset.mp hnotSubset
  have hiImage : i ∈ Finset.univ.image v := (Finset.mem_filter.mp hiLive).1
  have hisigma : sigma i = none := (Finset.mem_filter.mp hiLive).2
  obtain ⟨g, _hg, hgi⟩ := Finset.mem_image.mp hiImage
  subst i
  have hxv : x (v g) = false := by simp [x, restrictionFalseCompletion, hisigma]
  let y : Fin n → Bool := Function.update x (v g) true
  have hy : Rung4Restriction.Extends sigma y := by
    intro j b hj
    have hjv : j ≠ v g := by
      intro h
      subst j
      rw [hisigma] at hj
      contradiction
    simpa [y, Function.update_of_ne hjv] using hx j b hj
  obtain ⟨_, htx, hshallowx⟩ := hleaf x hx
  obtain ⟨_, hty, _⟩ := hleaf y hy
  have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
    simpa [y, hxv, path] using
      CommonTree.run_update_of_not_mem_queryVars trunk x (v g) (by simpa [path] using hiPath)
  have hfree : CommonTree.run trunk x (v g) = none := by
    cases ht : CommonTree.run trunk x (v g) with
    | none => rfl
    | some b =>
        have hbx : b = false := by exact (htx (v g) b ht).symm.trans hxv
        have hby : b = true := by
          have hty' : CommonTree.run trunk y (v g) = some b := by simpa [hrun] using ht
          have hyv : y (v g) = true := by simp [y]
          exact (hty (v g) b hty').symm.trans hyv
        exact False.elim (Bool.false_ne_true (hbx.symm.trans hby))
  have hfuelPos : 0 < fuel := by
    have hiFree : v g ∈ freeVars sigma := by simpa [mem_freeVars] using hisigma
    have : 0 < stars sigma := by rw [stars]; exact Finset.card_pos.mpr ⟨v g, hiFree⟩
    omega
  have hdeep := selectedLiteral_canonicalDT_depth_of_free v
    (CommonTree.run trunk x) g hfuelPos hfree
  have hzero := hshallowx g
  omega

/-- Exact endpoint-local criterion for singleton families with ample fuel: a residual-zero common
trunk exists exactly when its depth budget covers the distinct selected coordinates still live at
the root.  Repeated gate ownership contributes no additional cost. -/
theorem commonShallowAt_selectedLiteral_zero_iff {n G fuel d : ℕ}
    (v : Fin G → Fin n) (sigma : Restriction n) (hfuel : stars sigma ≤ fuel) :
    CommonShallowAt (selectedLiteralGates v) fuel sigma d 0 ↔
      ((Finset.univ.image v).filter fun i => sigma i = none).card ≤ d := by
  constructor
  · intro h
    by_contra hnot
    exact selectedLiteral_not_commonShallowAt_zero v sigma hfuel (by omega) h
  · intro hlive
    apply commonShallowAt_zero_of_live_support_le
      (selectedLiteralGates v) fuel sigma d hfuel
    simpa using hlive

/-- Therefore the semantic bad set for a singleton family is exactly a hypergeometric support
tail on every shell covered by the fuel budget.  Fixed Boolean values and repeated coordinate
ownership disappear from the criterion; only the root's live-set intersection with the distinct
owned-coordinate image remains. -/
theorem commonShallowBad_selectedLiteral_zero_eq_liveSupportTail
    {n G fuel K d : ℕ} (v : Fin G → Fin n) (hKfuel : K ≤ fuel) :
    commonShallowBad (selectedLiteralGates v) fuel K d 0 =
      (Finset.univ : Finset (Restriction n)).filter fun sigma =>
        stars sigma = K ∧
          d < ((Finset.univ.image v).filter fun i => sigma i = none).card := by
  ext sigma
  rw [mem_commonShallowBad]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hstars, hbad⟩
    refine ⟨hstars, ?_⟩
    rw [commonShallowAt_selectedLiteral_zero_iff v sigma (by omega)] at hbad
    omega
  · rintro ⟨hstars, hlive⟩
    refine ⟨hstars, ?_⟩
    rw [commonShallowAt_selectedLiteral_zero_iff v sigma (by omega)]
    omega

/-! ### A closed hypergeometric bound for the singleton tail

The exact semantic classification above reduces the singleton problem to a standard sampling
without replacement event.  The following finite set packages that event independently of a
particular selector.  Covering every tail member by one live `(d+1)`-subset of the owned support
and using the exact extension-fiber count gives a closed binomial bound.  This is the factorially
sharp first-moment (union) bound; it deliberately does not claim that the overlapping cover is an
exact partition. -/

/-- Restrictions on the `K`-star shell having more than `d` live coordinates in `support`. -/
noncomputable def liveSupportTail {n : ℕ} (support : Finset (Fin n)) (K d : ℕ) :
    Finset (Restriction n) := by
  classical
  exact Finset.univ.filter fun sigma =>
    stars sigma = K ∧ d < (support.filter fun i => sigma i = none).card

/-- The hypergeometric union bound for a fixed support.  A tail root contains a live
`(d+1)`-subset of `support`.  For each candidate subset the exact shell fiber has cardinality
`choose (n-(d+1)) (K-(d+1)) * 2^(n-K)`, and there are `choose |support| (d+1)` candidates. -/
theorem liveSupportTail_card_le {n K d : ℕ} (support : Finset (Fin n))
    (hdK : d < K) (hKn : K ≤ n) :
    (liveSupportTail support K d).card ≤
      Nat.choose support.card (d + 1) *
        (Nat.choose (n - (d + 1)) (K - (d + 1)) * 2 ^ (n - K)) := by
  classical
  let requiredSets := support.powersetCard (d + 1)
  let cover := requiredSets.biUnion fun required =>
    targetPreservingShellExtensions (fun _ : Fin n => none) required K
  have hfreeAll : freeVars (fun _ : Fin n => none) = Finset.univ := by
    ext i
    simp [mem_freeVars]
  have hstarsAll : stars (fun _ : Fin n => none) = n := by
    rw [stars, hfreeAll, Finset.card_univ, Fintype.card_fin]
  have hrequiredSetsCard : requiredSets.card =
      Nat.choose support.card (d + 1) := by
    simp [requiredSets]
  have htailCover : liveSupportTail support K d ⊆ cover := by
    intro sigma hsigma
    rw [liveSupportTail, Finset.mem_filter] at hsigma
    have hinterCard : d + 1 ≤
        (support.filter fun i => sigma i = none).card := by omega
    obtain ⟨required, hrequired, hrequiredCard⟩ :=
      Finset.exists_subset_card_eq hinterCard
    have hrequiredSupport : required ⊆ support :=
      hrequired.trans (Finset.filter_subset _ _)
    have hrequiredLive : required ⊆ freeVars sigma := by
      intro i hi
      rw [mem_freeVars]
      exact (Finset.mem_filter.mp (hrequired hi)).2
    rw [Finset.mem_biUnion]
    refine ⟨required, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨hrequiredSupport, hrequiredCard⟩
    · rw [targetPreservingShellExtensions, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hsigma.2.1, hrequiredLive⟩
      intro i b hib
      simp at hib
  calc
    (liveSupportTail support K d).card ≤ cover.card :=
      Finset.card_le_card htailCover
    _ ≤ ∑ required ∈ requiredSets,
        (targetPreservingShellExtensions (fun _ : Fin n => none) required K).card :=
      Finset.card_biUnion_le
    _ = ∑ _required ∈ requiredSets,
        (Nat.choose (n - (d + 1)) (K - (d + 1)) * 2 ^ (n - K)) := by
      apply Finset.sum_congr rfl
      intro required hrequired
      have hrequiredData := Finset.mem_powersetCard.mp hrequired
      rw [targetPreservingShellExtensions_card]
      · rw [hfreeAll, Finset.card_univ, Fintype.card_fin, hrequiredData.2]
      · rw [hfreeAll]
        exact Finset.subset_univ _
      · omega
      · simpa [hstarsAll] using hKn
    _ = Nat.choose support.card (d + 1) *
        (Nat.choose (n - (d + 1)) (K - (d + 1)) * 2 ^ (n - K)) := by
      rw [Finset.sum_const, hrequiredSetsCard]
      rfl

/-- Selector-specialized form of the hypergeometric bound for the exact semantic bad set. -/
theorem commonShallowBad_selectedLiteral_zero_card_le
    {n G fuel K d : ℕ} (v : Fin G → Fin n) (hKfuel : K ≤ fuel)
    (hdK : d < K) (hKn : K ≤ n) :
    (commonShallowBad (selectedLiteralGates v) fuel K d 0).card ≤
      Nat.choose (Finset.univ.image v).card (d + 1) *
        (Nat.choose (n - (d + 1)) (K - (d + 1)) * 2 ^ (n - K)) := by
  rw [commonShallowBad_selectedLiteral_zero_eq_liveSupportTail v hKfuel]
  exact liveSupportTail_card_le (Finset.univ.image v) hdK hKn

/-- Division-free density form of the singleton bound.  Relative to the exact `K`-star shell,
the bad fraction is at most
`choose |image v| (d+1) * choose K (d+1) / choose n (d+1)`.
The Boolean-profile factor remains explicit and cancels against the shell cardinality. -/
theorem commonShallowBad_selectedLiteral_zero_hypergeometric_balance
    {n G fuel K d : ℕ} (v : Fin G → Fin n) (hKfuel : K ≤ fuel)
    (hdK : d < K) (hKn : K ≤ n) :
    Nat.choose n (d + 1) *
        (commonShallowBad (selectedLiteralGates v) fuel K d 0).card ≤
      Nat.choose (Finset.univ.image v).card (d + 1) *
        (Nat.choose n K * Nat.choose K (d + 1) * 2 ^ (n - K)) := by
  have hbound := commonShallowBad_selectedLiteral_zero_card_le
    v hKfuel hdK hKn
  have hmul := Nat.mul_le_mul_left (Nat.choose n (d + 1)) hbound
  calc
    Nat.choose n (d + 1) *
        (commonShallowBad (selectedLiteralGates v) fuel K d 0).card ≤
        Nat.choose n (d + 1) *
          (Nat.choose (Finset.univ.image v).card (d + 1) *
            (Nat.choose (n - (d + 1)) (K - (d + 1)) * 2 ^ (n - K))) := hmul
    _ = Nat.choose (Finset.univ.image v).card (d + 1) *
        ((Nat.choose n (d + 1) *
          Nat.choose (n - (d + 1)) (K - (d + 1))) * 2 ^ (n - K)) := by
      ac_rfl
    _ = Nat.choose (Finset.univ.image v).card (d + 1) *
        ((Nat.choose n K * Nat.choose K (d + 1)) * 2 ^ (n - K)) := by
      rw [Nat.choose_mul (by omega : d + 1 ≤ K)]
    _ = Nat.choose (Finset.univ.image v).card (d + 1) *
        (Nat.choose n K * Nat.choose K (d + 1) * 2 ^ (n - K)) := by
      rfl

/-! ### Distinct support does not determine residual-depth-one badness

At residual depth zero the singleton benchmark is exactly controlled by its distinct live
support.  The next residual threshold is qualitatively different.  The exhaustive width-two
gate already present in the regression suite and the two positive singleton gates below have
the same full two-coordinate support, but opposite semantic badness at the identical fully live
root.  Thus no residual-depth-one theorem can be a function only of the distinct support set. -/

/-- The exhaustive width-two family and the matching singleton family mention exactly the same
two coordinates. -/
theorem exhaustiveTwoBit_support_eq_selectedSingleton_support :
    familyVariableSupport exhaustiveTwoBitFamily =
      familyVariableSupport
        (selectedLiteralGates (fun i : Fin 2 => (i : Fin 2))) := by
  rw [familyVariableSupport_selectedLiteralGates]
  decide

/-- Kernel-checked separation at fixed parameters.  With fuel two, shell size two, zero common
queries, and residual threshold one, the fully live root is bad for a width-two family but good
for a singleton family having exactly the same distinct support.  This rules out lifting the
singleton live-support tail to width two without an additional interaction/overlap statistic. -/
theorem widthTwo_residualOne_badness_not_determined_by_distinct_support :
    familyVariableSupport exhaustiveTwoBitFamily =
        familyVariableSupport
          (selectedLiteralGates (fun i : Fin 2 => (i : Fin 2))) ∧
      (fun _ : Fin 2 => none) ∈
        commonShallowBad exhaustiveTwoBitFamily 2 2 0 1 ∧
      (fun _ : Fin 2 => none) ∉
        commonShallowBad
          (selectedLiteralGates (fun i : Fin 2 => (i : Fin 2))) 2 2 0 1 := by
  refine ⟨exhaustiveTwoBit_support_eq_selectedSingleton_support,
    allFreeTwo_mem_exhaustiveTwoBit_commonShallowBad_one, ?_⟩
  rw [mem_commonShallowBad]
  rintro ⟨_hstars, hbad⟩
  exact hbad (commonShallowAt_selectedLiteral_one
    (fuel := 2) (trunkDepth := 0) (fun i : Fin 2 => (i : Fin 2))
    (fun _ : Fin 2 => none))

#print axioms actualMargin_normalizedSurvivorRound_exactSubcube

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_eq_zero_of_gateVariableSupport_card_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.Layered.eval_eq_of_agree_on_bottomSupport
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.Layered.bottomSupport_eq_univ_of_eval_eq_parity_xor
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.Layered.bottomSupport_card_eq_of_eval_eq_parity_xor
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.normalizedLayeredBottomFamily_support_eq_bottomSupport
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.normalizedLayeredBottomFamily_support_eq_univ_of_eval_eq_parity_xor
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_supportSubset_exact_balance_half_of_live_le_supportAlphabet
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_normalizedLayered_supportSubset_balance_of_full_support
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_normalizedLayered_supportSubset_balance_of_eval_eq_parity_xor
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_normalizedLayered_realized_density_of_full_support
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_normalizedLayered_realized_density_of_eval_eq_parity_xor
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.liveLayeredBottomSupportTail_card_of_full_support
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.fullSupport_halfShell_mem_liveLayeredBottomSupportTail
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_normalizedLayered_commonShallowAt_of_realized_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_commonShallowAt_linearGap_realized_of_full_support
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.restriction_not_commonShallowAt_independentLiteral_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_independentLiteral_zero_eq_shell
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowAt_selectedLiteral_zero_iff
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_selectedLiteral_zero_eq_liveSupportTail
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.liveSupportTail_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_selectedLiteral_zero_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_selectedLiteral_zero_hypergeometric_balance
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.selectedLiteral_canonicalDT_depth_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowAt_selectedLiteral_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.widthTwo_residualOne_badness_not_determined_by_distinct_support
