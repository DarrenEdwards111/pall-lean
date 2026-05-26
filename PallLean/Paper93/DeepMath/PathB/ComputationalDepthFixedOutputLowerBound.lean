import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictedTargets

/-
# Real restricted lower bound: fixed-output SAT searchers

This file proves an unconditional lower bound for a genuinely weak class of SAT
search machines: machines whose output is fixed independently of the input CNF.

The construction is simple and real:

* if the fixed output is `none`, use the empty satisfiable CNF;
* if the fixed output is `some a`, use an empty CNF with `a.length + 1`
  variables.  The formula is satisfiable, but the fixed assignment `a` has the
  wrong length, so it cannot satisfy the formula.

This is a restricted lower bound, not a P-vs-NP proof.  It proves that a weak
observer class cannot uniformly solve even the trivial all-clauses-empty SAT
fragment when it is forced to use one fixed output for every instance.
-/

namespace SATDepthMachine

/-! ## Empty satisfiable CNFs -/

/-- Empty CNF over `n` variables.  It is satisfiable by any assignment of length
`n`. -/
def emptyCNF (n : Nat) : CNF where
  vars := n
  clauses := []

/-- The empty CNF is satisfied exactly by assignments of the right length. -/
theorem satisfies_emptyCNF_iff
    (n : Nat) (a : RawAssignment) :
    Satisfies (emptyCNF n) a ↔ a.length = n := by
  unfold Satisfies emptyCNF CNF.eval
  simp

/-- Every empty CNF is satisfiable. -/
theorem satisfiable_emptyCNF
    (n : Nat) : Satisfiable (emptyCNF n) := by
  refine ⟨List.replicate n false, ?_⟩
  exact (satisfies_emptyCNF_iff n (List.replicate n false)).mpr
    (by simp)

/-- The all-empty-CNF fragment. -/
def EmptyCNFClass (φ : CNF) : Prop :=
  ∃ n : Nat, φ = emptyCNF n

theorem emptyCNF_mem_emptyClass
    (n : Nat) : EmptyCNFClass (emptyCNF n) :=
  ⟨n, rfl⟩

/-! ## Fixed-output searchers -/

/-- A fixed-output SAT searcher is a search machine whose output does not depend
on the input formula. -/
structure FixedOutputSearchMachine
    (U : MachineModel)
    (M : SearchMachine U) where
  output : Option RawAssignment
  run_eq : ∀ φ : CNF, U.searchRun M.code φ = output

/-- The weak machine class: searchers with input-independent output. -/
def IsFixedOutputSearcher
    (U : MachineModel)
    (M : SearchMachine U) : Prop :=
  Nonempty (FixedOutputSearchMachine U M)

/-! ## Lower bound -/

/-- If a fixed-output machine returns `none`, it misses the empty CNF over zero
variables. -/
theorem fixedOutput_none_fails_emptyCNF
    (U : MachineModel)
    (M : SearchMachine U)
    (F : FixedOutputSearchMachine U M)
    (hF : F.output = none) :
    RestrictedSearchMachineFails U EmptyCNFClass M := by
  refine ⟨emptyCNF 0, emptyCNF_mem_emptyClass 0,
    satisfiable_emptyCNF 0, ?_⟩
  intro h
  rcases h with ⟨a, hrun, _hsat⟩
  rw [F.run_eq (emptyCNF 0), hF] at hrun
  cases hrun

/-- If a fixed-output machine always returns `some a`, it misses the empty CNF
over `a.length + 1` variables. -/
theorem fixedOutput_some_fails_longer_emptyCNF
    (U : MachineModel)
    (M : SearchMachine U)
    (F : FixedOutputSearchMachine U M)
    (a : RawAssignment)
    (hF : F.output = some a) :
    RestrictedSearchMachineFails U EmptyCNFClass M := by
  refine ⟨emptyCNF (a.length + 1),
    emptyCNF_mem_emptyClass (a.length + 1),
    satisfiable_emptyCNF (a.length + 1), ?_⟩
  intro h
  rcases h with ⟨b, hrun, hsat⟩
  rw [F.run_eq (emptyCNF (a.length + 1)), hF] at hrun
  cases hrun
  have hlen : a.length = a.length + 1 :=
    (satisfies_emptyCNF_iff (a.length + 1) a).mp hsat
  exact Nat.succ_ne_self a.length hlen.symm

/-- Main restricted lower bound: every fixed-output searcher fails on a
satisfiable formula in the empty-CNF fragment. -/
theorem fixedOutputSearcher_fails_emptyCNFClass
    (U : MachineModel)
    (M : SearchMachine U)
    (hfixed : IsFixedOutputSearcher U M) :
    RestrictedSearchMachineFails U EmptyCNFClass M := by
  rcases hfixed with ⟨F⟩
  cases h : F.output with
  | none =>
      exact fixedOutput_none_fails_emptyCNF U M F h
  | some a =>
      exact fixedOutput_some_fails_longer_emptyCNF U M F a h

/-- No fixed-output search machine is correct even for the empty-CNF fragment.
-/
theorem not_restrictedSearchCorrect_emptyCNFClass_of_fixedOutput
    (U : MachineModel)
    (M : SearchMachine U)
    (hfixed : IsFixedOutputSearcher U M) :
    ¬ RestrictedSearchCorrect U EmptyCNFClass M :=
  (not_restrictedSearchCorrect_iff_fails U EmptyCNFClass M).mpr
    (fixedOutputSearcher_fails_emptyCNFClass U M hfixed)

/-! ## Class-level packaging -/

/-- Restricted deep search relative to the fixed-output machine class.  This is
not the same as `RestrictedDeepSearch`, which quantifies over all machines.
Here we only quantify over the weak fixed-output subclass. -/
def FixedOutputRestrictedDeepSearch
    (U : MachineModel) (R : CNF -> Prop) : Prop :=
  ∀ M : SearchMachine U,
    IsFixedOutputSearcher U M ->
      RestrictedSearchMachineFails U R M

/-- The empty-CNF fragment has a real lower bound against fixed-output
searchers. -/
theorem fixedOutputRestrictedDeepSearch_emptyCNFClass
    (U : MachineModel) :
    FixedOutputRestrictedDeepSearch U EmptyCNFClass := by
  intro M hfixed
  exact fixedOutputSearcher_fails_emptyCNFClass U M hfixed

/-! ## Axiom trace -/

#print axioms satisfies_emptyCNF_iff
#print axioms satisfiable_emptyCNF
#print axioms fixedOutput_none_fails_emptyCNF
#print axioms fixedOutput_some_fails_longer_emptyCNF
#print axioms fixedOutputSearcher_fails_emptyCNFClass
#print axioms not_restrictedSearchCorrect_emptyCNFClass_of_fixedOutput
#print axioms fixedOutputRestrictedDeepSearch_emptyCNFClass

end SATDepthMachine
