import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletion

/-!
# Exact Håstad encoding: the DNF/term reframing (soundness foundation)

**STATUS: REAL.  THE REFRAMING THAT DISSOLVES THE FOREIGN-BLOCK FLIP.**

The `confirm`-scan selector failed because in the CNF "first-unsatisfied-clause" picture a
`ρ`-satisfied clause can sit in the skipped prefix and look like a processed clause under
`σ*`.  Håstad's canonical decoding uses the *DNF/term* picture instead, where a satisfied
term is a decision-tree leaf — so on a deep path every **prefix term is falsified**, never
satisfied.

Under the satisfying completion `σ*`, a falsified term stays *non-satisfied* (its forcing
false literal lives on a `ρ`-fixed variable, untouched by the path).  So the decoder's
selector — *first term satisfied (all literals true) under `σ*`* — lands exactly on the
first processed term, with no flip and no block-guessing.

* `litFalse`: a literal forced false;
* `termSat`: a term (AND of literals) is satisfied iff *all* its literals are true;
* `litTrue_eq_false_of_litFalse`: a forced-false literal is not true;
* `termSat_complete_eq_false_of_litFalse`: a term with a `ρ`-fixed false literal stays
  *unsatisfied* under `σ*` — the soundness foundation for the satisfaction-selector.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- A literal forced false by `σ`. -/
def litFalse (σ : Restriction n) (ℓ : Rung4Literal n) : Bool :=
  match Depth3.litFixedVal σ ℓ with | some false => true | _ => false

/-- A DNF *term* (conjunction of literals) is satisfied iff all its literals are true. -/
def termSat (σ : Restriction n) (T : Clause n) : Bool :=
  T.lits.all (Depth3.litTrue σ)

/-- A forced-false literal is not forced true. -/
theorem litTrue_eq_false_of_litFalse {σ : Restriction n} {ℓ : Rung4Literal n}
    (h : litFalse σ ℓ = true) : Depth3.litTrue σ ℓ = false := by
  have hf : Depth3.litFixedVal σ ℓ = some false := by
    unfold litFalse at h
    split at h
    · next heq => exact heq
    · simp at h
  unfold Depth3.litTrue; rw [hf]

/-- **Soundness foundation.**  A term with a `ρ`-fixed false literal stays *unsatisfied*
under the satisfying completion — so the decoder never mistakes a falsified prefix term
for a processed (satisfied) one. -/
theorem termSat_complete_eq_false_of_litFalse {ρ : Restriction n}
    {litList : List (Rung4Literal n)} {T : Clause n} {ℓ : Rung4Literal n}
    (hℓT : ℓ ∈ T.lits) (hfalse : litFalse ρ ℓ = true)
    (hnm : litVar ℓ ∉ litList.map litVar) :
    termSat (complete ρ litList) T = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  rw [termSat, List.all_eq_true] at h
  have hℓtrue := h ℓ hℓT
  rw [litTrue_complete_eq_of_not_mem ℓ litList ρ hnm,
    litTrue_eq_false_of_litFalse hfalse] at hℓtrue
  simp at hℓtrue

/-- A term (conjunction) is *falsified* if some literal is forced false. -/
def termFalsified (σ : Restriction n) (T : Clause n) : Bool :=
  T.lits.any (litFalse σ)

/-- A literal that is neither free nor false is forced true. -/
theorem litTrue_of_not_free_not_false {σ : Restriction n} {ℓ : Rung4Literal n}
    (hfree : Depth3.litFree σ ℓ = false) (hfalse : litFalse σ ℓ = false) :
    Depth3.litTrue σ ℓ = true := by
  cases hv : Depth3.litFixedVal σ ℓ with
  | none => simp [Depth3.litFree, hv] at hfree
  | some b =>
    cases b with
    | false => simp [litFalse, hv] at hfalse
    | true => unfold Depth3.litTrue; rw [hv]

/-- **Term dichotomy.**  A fully-fixed term (no free literal) is either satisfied or
falsified — if it is not satisfied, some literal is forced false.  This is what makes a
*skipped* (non-active, non-satisfied) term necessarily *falsified*, so the decoder's
`termSat` selector cannot mistake it for a processed term. -/
theorem term_falsified_of_not_sat_no_free {σ : Restriction n} {T : Clause n}
    (hsat : termSat σ T = false) (hnofree : freeLits σ T = []) :
    termFalsified σ T = true := by
  by_contra hcon
  rw [Bool.not_eq_true] at hcon
  have hall : termSat σ T = true := by
    rw [termSat, List.all_eq_true]
    intro ℓ hℓ
    refine litTrue_of_not_free_not_false ?_ ?_
    · by_contra hf
      rw [Bool.not_eq_false] at hf
      have : ℓ ∈ freeLits σ T := List.mem_filter.mpr ⟨hℓ, hf⟩
      rw [hnofree] at this; simp at this
    · by_contra hf
      rw [Bool.not_eq_false] at hf
      have : termFalsified σ T = true := by
        rw [termFalsified, List.any_eq_true]; exact ⟨ℓ, hℓ, hf⟩
      rw [this] at hcon; simp at hcon
  rw [hall] at hsat; simp at hsat

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termSat_complete_eq_false_of_litFalse
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.term_falsified_of_not_sat_no_free
