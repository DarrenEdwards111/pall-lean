import PallLean.Paper93.DeepMath.PathB.RouteBTouchedCanonicalSourceKR

/-!
# Route B touched canonical-interface KR seam

This file removes the final free per-position `localStateOf` function from the
canonical-source seam.  The local state is now computed canonically from the
actual Cook--Levin support geometry of the selected source:

* dormant window: state `0`;
* non-dormant source `i`: rank the row variable inside the concrete support
  of constraint `i` by counting support variables with smaller index, then
  reduce into the fixed four-state local alphabet.

This is still a seam, not the final normal-form theorem: the remaining datum is
only the interpreter and the exact identity that says this canonical local
interface word really interprets the touched split row.  But the interface word
itself is no longer externally chosen.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Rank of `v` inside a finite support by index order, reduced to the fixed
four-state local alphabet used by `InterfaceType`. -/
def supportLocalState
    {N : ℕ} (support : Finset (Fin N)) (v : Fin N) : Fin 4 :=
  ⟨((support.filter (fun w => w.1 < v.1)).card) % 4, Nat.mod_lt _ (by decide)⟩

/-- Canonical local state for a source choice, derived from the selected
constraint's actual support geometry. -/
noncomputable def canonicalTouchedLocalStateOfSource
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n))
    (src : TouchedWindowSource M n hn2 htb hns S hlen j) : Fin 4 :=
  match src.source with
  | none => ⟨0, by decide⟩
  | some i =>
      supportLocalState ((cookLevinTableau M n hn2 htb hns).constraints.get i).support
        (touchedRowVarAt M n hn2 htb hns S hlen j)

/-- Canonical local state for the canonical support-fibre source. -/
noncomputable def canonicalTouchedLocalState
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) : Fin 4 :=
  canonicalTouchedLocalStateOfSource M n hn2 htb hns S hlen j
    (canonicalTouchedWindowSource M n hn2 htb hns S hlen j)

/-- The fully canonical interface symbol at one KR position: source, type, and
local state are all derived from concrete Cook--Levin support/type data. -/
noncomputable def canonicalTouchedInterface
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) : PallLean.Paper93.InterfaceType :=
  touchedActualInterface
    (canonicalTouchedWindowSource M n hn2 htb hns S hlen j)
    (canonicalTouchedLocalState M n hn2 htb hns S hlen j)

/-- If the canonical source is non-dormant, the local state is computed from the
selected constraint's concrete support and the actual row variable at `j`. -/
theorem canonicalTouchedLocalState_eq_supportLocalState_of_source
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hi : canonicalTouchedSourceIdx M n hn2 htb hns S hlen j = some i) :
    canonicalTouchedLocalState M n hn2 htb hns S hlen j =
      supportLocalState ((cookLevinTableau M n hn2 htb hns).constraints.get i).support
        (touchedRowVarAt M n hn2 htb hns S hlen j) := by
  unfold canonicalTouchedLocalState canonicalTouchedLocalStateOfSource
    canonicalTouchedWindowSource
  simp [hi]

/-- Canonical-interface KR data.

No per-position source or local-state selector remains.  The only remaining
content is the real interpretation theorem for the canonical interface word. -/
def CookLevinTouchedCanonicalInterfaceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (interp : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    ∀ (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      (hlen : S.length = Nat.log 2 n) →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (cookLevinTableau M n hn2 htb hns).partition S →
      (∀ i, ∀ v ∈ alloc i, v ∈ S) →
      (∀ i, ∀ v ∈ alloc i,
        v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support) →
      (∀ i, (alloc i).length ≤ 6) →
      (∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []) →
      touchedSplitRow M n hn2 htb hns S m alloc =
        interp (fun j => touchedInterfaceStateCode
          (canonicalTouchedInterface M n hn2 htb hns S hlen j))

/-- Canonical-interface data supplies the canonical-source seam by instantiating
`localStateOf` with the canonical support-geometry local state. -/
theorem touchedCanonicalSourceKRData_of_touchedCanonicalInterfaceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedCanonicalInterfaceKRData M n hn2 htb hns) :
    CookLevinTouchedCanonicalSourceKRData M n hn2 htb hns := by
  rcases hData with ⟨interp, hsound⟩
  refine ⟨interp, ?_, ?_⟩
  · intro S m alloc hlen j
    exact canonicalTouchedLocalState M n hn2 htb hns S hlen j
  · intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
    exact hsound S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform canonical-interface KR data at paper scale. -/
def Step247UniformTouchedCanonicalInterfaceKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedCanonicalInterfaceKRData M n hn2 htb hns

/-- Uniform canonical-interface data implies the canonical-source seam. -/
theorem step247UniformTouchedCanonicalSourceKRData_of_touchedCanonicalInterfaceKRData
    (hData : Step247UniformTouchedCanonicalInterfaceKRData) :
    Step247UniformTouchedCanonicalSourceKRData := by
  intro M n hn hn2 htb hns
  exact touchedCanonicalSourceKRData_of_touchedCanonicalInterfaceKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform canonical-interface data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedCanonicalInterfaceKRData_TPhi
    (hData : Step247UniformTouchedCanonicalInterfaceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedCanonicalSourceKRData_TPhi
    (step247UniformTouchedCanonicalSourceKRData_of_touchedCanonicalInterfaceKRData hData)

/-! ## Axiom audit anchors -/

#print axioms supportLocalState
#print axioms canonicalTouchedLocalStateOfSource
#print axioms canonicalTouchedLocalState
#print axioms canonicalTouchedInterface
#print axioms canonicalTouchedLocalState_eq_supportLocalState_of_source
#print axioms touchedCanonicalSourceKRData_of_touchedCanonicalInterfaceKRData
#print axioms step247UniformTouchedCanonicalSourceKRData_of_touchedCanonicalInterfaceKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedCanonicalInterfaceKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
