import PallLean.Paper93.DeepMath.PathB.FaithfulSemanticLiveRank

/-!
# Finite-control live-rank obstruction

`FaithfulStateRankAt` currently applies `stateContextRank : Nat -> Nat` only to
the finite control state code

```
(TuringMachine.run ...).state.val : Nat
```

and not to the full configuration, tape, head position, tableau, or
input-length-indexed boundary object.  Therefore every fixed DTM/rank
presentation has a finite-control maximum, independent of input length.

This file records the consequence: the uniform binomial semantic live-minor
discharge cannot be proved for any semantic predicate that actually contains a
SAT-deciding finite-control presentation.  In the current faithful-semantic
type, the discharge field already forces the semantic SAT class to be empty.

That is not a P-vs-NP proof; it is a correction point.  To make the observer
route viable, the live rank has to be indexed by real live configuration data,
not only by finite control state.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- The maximum state-context rank over the DTM's finite control states. -/
noncomputable def finiteControlStateContextRankMax
    (M : TuringMachine.DTM) (stateContextRank : Nat -> Nat) : Nat :=
  Finset.univ.sup (fun q : Fin M.numStates => stateContextRank q.val)

/-- Every faithful state rank is bounded by the finite-control maximum,
because `FaithfulStateRankAt` looks only at `config.state.val`. -/
theorem FaithfulStateRankAt_le_finiteControlStateContextRankMax
    (M : TuringMachine.DTM) (stateContextRank : Nat -> Nat)
    (n : Nat) (input : Fin n -> Bool) (t : Nat) :
    FaithfulStateRankAt M stateContextRank n input t <=
      finiteControlStateContextRankMax M stateContextRank := by
  classical
  unfold FaithfulStateRankAt finiteControlStateContextRankMax
  by_cases hn : n >= 1
  · by_cases ht : t < TuringMachine.timeSteps M n + 1
    · rw [dif_pos hn, dif_pos ht]
      exact
        Finset.le_sup
          (s := (Finset.univ : Finset (Fin M.numStates)))
          (f := fun q : Fin M.numStates => stateContextRank q.val)
          (b :=
            (TuringMachine.run M n t
              (TuringMachine.initialConfig M n hn input)).state)
          (hb := by simp)
    · rw [dif_pos hn, dif_neg ht]
      exact Nat.zero_le _
  · rw [dif_neg hn]
    exact Nat.zero_le _

/-- Consequently, the whole faithful trajectory width is bounded by the same
finite-control maximum at every input length. -/
theorem FaithfulTrajectoryWidth_le_finiteControlStateContextRankMax
    (M : TuringMachine.DTM) (stateContextRank : Nat -> Nat)
    (n : Nat) :
    FaithfulTrajectoryWidth M stateContextRank n <=
      finiteControlStateContextRankMax M stateContextRank := by
  classical
  unfold FaithfulTrajectoryWidth finiteControlStateContextRankMax
  by_cases hn : n >= 1
  · rw [dif_pos hn]
    apply Finset.sup_le
    intro input _hinput
    apply Finset.sup_le
    intro t _ht
    exact
      Finset.le_sup
        (s := (Finset.univ : Finset (Fin M.numStates)))
        (f := fun q : Fin M.numStates => stateContextRank q.val)
        (b :=
          (TuringMachine.run M n t.val
            (TuringMachine.initialConfig M n hn input)).state)
        (hb := by simp)
  · rw [dif_neg hn]
    exact Nat.zero_le _

/-- At lengths at least two, every finite-control maximum `C` is bounded by
`n^C`.  This lets the existing binomial arithmetic gap dominate the finite
maximum by choosing exponent `C`. -/
theorem finiteControlRankMax_le_pow_of_large_length
    (C n : Nat) (hn2 : n >= 2) :
    C <= n ^ C := by
  by_cases hC : C = 0
  · simp [hC]
  · have hC_two : C <= 2 ^ C := (Nat.lt_two_pow_self (n := C)).le
    have htwo_n : 2 ^ C <= n ^ C :=
      Nat.pow_le_pow_left (by omega : 2 <= n) C
    exact le_trans hC_two htwo_n

/-- If the binomial lower bound is larger than the finite-control maximum, no
semantic live-boundary certificate can exist. -/
theorem no_semanticLiveBoundaryAt_of_finiteControlRankMax_lt_choose
    {enc : ThreeCNFEncoding}
    (M : TuringMachine.DTM)
    (stateContextRank : Nat -> Nat)
    {n : Nat}
    (hchoose :
      finiteControlStateContextRankMax M stateContextRank <
        Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty
      (FaithfulSemanticLiveBoundaryAt enc M stateContextRank n)) := by
  intro hcert
  rcases hcert with ⟨cert⟩
  have hlive_le_max :
      cert.liveRank <= finiteControlStateContextRankMax M stateContextRank :=
    le_trans cert.rank_le_stateContext
      (FaithfulStateRankAt_le_finiteControlStateContextRankMax
        M stateContextRank n cert.input cert.time)
  have hchoose_le_max :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        finiteControlStateContextRankMax M stateContextRank :=
    le_trans cert.rank_lower hlive_le_max
  exact (not_le_of_gt hchoose) hchoose_le_max

/-- A uniform semantic live-minor discharge is incompatible with any
SAT-deciding DTM whose finite-control rank presentation satisfies the semantic
predicate. -/
theorem not_uniformSemanticLiveMinorDischarge_of_finiteControlSemanticDecider
    {enc : ThreeCNFEncoding}
    {LiveRankSemantics : FaithfulLiveRankSemanticsPredicate}
    {M : TuringMachine.DTM}
    {stateContextRank : Nat -> Nat}
    (hdec : DTMDecidesSATWithEncoding enc M)
    (hsem : LiveRankSemantics M stateContextRank) :
    Not (UniformFaithfulSemanticLiveMinorDischarge enc LiveRankSemantics) := by
  intro hdischarge
  let C := finiteControlStateContextRankMax M stateContextRank
  rcases hdischarge C with ⟨n, hn20, hlog, hcert_at⟩
  have hn2 : n >= 2 := by
    exact le_trans (by norm_num : 2 <= 2 ^ 20) hn20
  have hC_le_npow : C <= n ^ C :=
    finiteControlRankMax_le_pow_of_large_length C n hn2
  have hgap : n ^ C < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent C n hn20 hlog
  have hC_lt_choose :
      C < Nat.choose (n / 3) (Nat.log 2 n) :=
    lt_of_le_of_lt hC_le_npow hgap
  exact
    (no_semanticLiveBoundaryAt_of_finiteControlRankMax_lt_choose
      (enc := enc) M stateContextRank hC_lt_choose)
      (hcert_at M stateContextRank hdec hsem)

/-- Equivalently: in the current finite-control faithful-semantic type, a
successful uniform discharge excludes *every* semantic presentation of every
SAT-deciding DTM, not merely the zero-rank presentation. -/
theorem uniformSemanticLiveMinorDischarge_excludes_all_finiteControlPresentations
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (hdischarge :
      UniformFaithfulSemanticLiveMinorDischarge enc LiveRankSemantics) :
    forall (M : TuringMachine.DTM) (stateContextRank : Nat -> Nat),
      DTMDecidesSATWithEncoding enc M ->
        Not (LiveRankSemantics M stateContextRank) := by
  intro M stateContextRank hdec hsem
  exact
    (not_uniformSemanticLiveMinorDischarge_of_finiteControlSemanticDecider
      (enc := enc) (M := M) (stateContextRank := stateContextRank)
      hdec hsem)
      hdischarge

/-- The semantic SAT observer class is empty under a uniform discharge, unless
there is no SAT-deciding DTM to present.  This is the finite-control correction:
the current semantic discharge is too strong for the current live-rank carrier.
-/
theorem no_FaithfulSemanticSATObserverClass_of_uniformSemanticLiveMinorDischarge
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (hdischarge :
      UniformFaithfulSemanticLiveMinorDischarge enc LiveRankSemantics)
    (T : TrajectoryObserverMachine) :
    Not (FaithfulSemanticSATObserverClass enc LiveRankSemantics T) := by
  intro hT
  rcases hT with ⟨M, stateContextRank, hdec, hsem, _hT_eq⟩
  exact
    (uniformSemanticLiveMinorDischarge_excludes_all_finiteControlPresentations
      enc LiveRankSemantics hdischarge M stateContextRank hdec)
      hsem

/-- Therefore any semantic presentation theorem together with uniform
finite-control discharge already proves that no DTM decides SAT. -/
theorem no_DTMDecidesSATWithEncoding_of_finiteControlSemanticPresentation
    (enc : ThreeCNFEncoding)
    (LiveRankSemantics : FaithfulLiveRankSemanticsPredicate)
    (hpresent :
      PaperMainSemanticFaithfulObserverPresentation enc LiveRankSemantics)
    (hdischarge :
      UniformFaithfulSemanticLiveMinorDischarge enc LiveRankSemantics) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  intro hM
  rcases hM with ⟨M, hdec⟩
  let T : TrajectoryObserverMachine :=
    faithfulTrajectoryObserver M (fun _ => 0)
  have hfaithful : FaithfulSATObserverClass enc T := by
    refine ⟨M, (fun _ => 0), hdec, ?_⟩
    rfl
  have hoperational : OperationalTrajectoryObserverDecidesSAT enc T :=
    OperationalTrajectoryObserverDecidesSAT_of_faithful hfaithful
  have hsemantic : FaithfulSemanticSATObserverClass enc LiveRankSemantics T :=
    hpresent T hoperational
  exact
    (no_FaithfulSemanticSATObserverClass_of_uniformSemanticLiveMinorDischarge
      enc LiveRankSemantics hdischarge T)
      hsemantic

#print axioms FaithfulStateRankAt_le_finiteControlStateContextRankMax
#print axioms FaithfulTrajectoryWidth_le_finiteControlStateContextRankMax
#print axioms not_uniformSemanticLiveMinorDischarge_of_finiteControlSemanticDecider
#print axioms uniformSemanticLiveMinorDischarge_excludes_all_finiteControlPresentations
#print axioms no_FaithfulSemanticSATObserverClass_of_uniformSemanticLiveMinorDischarge
#print axioms no_DTMDecidesSATWithEncoding_of_finiteControlSemanticPresentation

end PallLean.Paper93.DeepMath.PathB
