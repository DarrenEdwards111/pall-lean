import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletion
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFindAdvance

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

/-- The DNF is satisfied under `σ` (some term all-true). -/
def anyTermSat (cs : List (Clause n)) (σ : Restriction n) : Bool :=
  cs.any (termSat σ)

/-- The decision tree's active term: the first live term with a free literal — *unless*
some term is already satisfied (then the DNF is `1`, a leaf, and there is no active term). -/
def activeTerm (cs : List (Clause n)) (σ : Restriction n) : Option (Clause n) :=
  bif anyTermSat cs σ then none
  else cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length))

theorem activeTerm_anyTermSat_false {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (h : activeTerm cs σ = some T) : anyTermSat cs σ = false := by
  unfold activeTerm at h
  cases hb : anyTermSat cs σ with
  | true => rw [hb] at h; simp at h
  | false => rfl

theorem activeTerm_eq_find {cs : List (Clause n)} {σ : Restriction n}
    (h : anyTermSat cs σ = false) :
    activeTerm cs σ
      = cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length)) := by
  unfold activeTerm; rw [h, cond_false]

/-- **Prefix-falsified soundness (the crux the CNF walk lacked).**  Every term before the
active term is *falsified*: it is skipped by the decision tree, and — since no term is
satisfied (else we would be at a leaf) — the dichotomy forces it false. -/
theorem activeTerm_prefix_falsified {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (h : activeTerm cs σ = some T) :
    ∃ pre post, cs = pre ++ T :: post ∧ ∀ C' ∈ pre, termFalsified σ C' = true := by
  have hns := activeTerm_anyTermSat_false h
  have hfind : cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length))
      = some T := activeTerm_eq_find hns ▸ h
  obtain ⟨pre, post, hcs, hpre, _⟩ := find?_some_decompose hfind
  refine ⟨pre, post, hcs, fun C' hC' => ?_⟩
  have hp := hpre C' hC'
  rw [Bool.and_eq_false_iff] at hp
  rcases hp with h1 | h2
  · simpa using h1
  · have hnofree : freeLits σ C' = [] := by
      rw [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero,
        List.length_eq_zero_iff] at h2
      exact h2
    have hsat : termSat σ C' = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      have : anyTermSat cs σ = true := by
        rw [anyTermSat, List.any_eq_true]
        exact ⟨C', by rw [hcs]; exact List.mem_append_left _ hC', hc⟩
      rw [this] at hns; simp at hns
    exact term_falsified_of_not_sat_no_free hsat hnofree

/-- A forced-false literal lives on a fixed variable. -/
theorem litFalse_litVar_fixed {ρ : Restriction n} {ℓ : Rung4Literal n}
    (h : litFalse ρ ℓ = true) : ρ (litVar ℓ) ≠ none := by
  have hf : Depth3.litFixedVal ρ ℓ = some false := by
    unfold litFalse at h
    split at h
    · next heq => exact heq
    · simp at h
  cases ℓ with
  | pos i => simp only [Depth3.litFixedVal] at hf; simp only [litVar]; rw [hf]; simp
  | neg i =>
    simp only [Depth3.litFixedVal] at hf; simp only [litVar]
    intro hc; rw [hc] at hf; simp at hf

/-- **The sound-selector unlock.**  A term *falsified under `ρ`* stays *unsatisfied under
`σ*`* — its forcing false literal lives on a `ρ`-fixed variable, which is disjoint from the
(`ρ`-free) path variables, so the satisfying completion cannot un-falsify it.  This
discharges the `termSat`-selector soundness with no hypothesis on the blocks: prefix terms
(falsified by `activeTerm_prefix_falsified`) are non-`termSat` under `σ*`. -/
theorem termSat_complete_false_of_termFalsified {ρ : Restriction n}
    {litList : List (Rung4Literal n)} {T : Clause n}
    (hfals : termFalsified ρ T = true) (hfree : ∀ v ∈ litList.map litVar, ρ v = none) :
    termSat (complete ρ litList) T = false := by
  rw [termFalsified, List.any_eq_true] at hfals
  obtain ⟨ℓ, hℓT, hℓfalse⟩ := hfals
  exact termSat_complete_eq_false_of_litFalse hℓT hℓfalse
    (fun hmem => litFalse_litVar_fixed hℓfalse (hfree (litVar ℓ) hmem))

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termSat_complete_eq_false_of_litFalse
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.term_falsified_of_not_sat_no_free
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.activeTerm_prefix_falsified
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termSat_complete_false_of_termFalsified
