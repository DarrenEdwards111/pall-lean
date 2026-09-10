import GodMoveSymbolicPinnedInput
import Mathlib.Data.List.Pairwise

/-!
# Assignment coordinates form a Boolean face of the encoded SAT input

Each assignment variable occurs exactly once in the symbolic pinned-input
template. Thus pinning the remaining encoded input bits uses only constants;
it never identifies two machine input variables. The position map below is
chosen from this proved unique occurrence. No SAT answer or witness is used.
-/

namespace GodMovePinnedFaceLayout

open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer GodMoveSymbolicPinnedInput

/-- Read the assignment coordinate of a symbolic input gate, if present. -/
def variableOf {n : ℕ} : CGate n → Option (Fin n)
  | .var i => some i
  | _ => none

@[simp] theorem filterMap_none {α β : Type*} (l : List α) :
    l.filterMap (fun _ => (none : Option β)) = [] := by
  simp only [List.filterMap_eq_nil_iff, implies_true]

@[simp] theorem variableOf_eq_some_iff {n : ℕ} (g : CGate n) (i : Fin n) :
    variableOf g = some i ↔ g = .var i := by
  cases g <;> simp [variableOf]

@[simp] theorem unitTemplate_variables {n : ℕ} (i : Fin n) :
    (unitTemplate i).filterMap variableOf = [i] := by
  simp [unitTemplate, List.filterMap_map, Function.comp_def, variableOf]

/-- The variable occurrences are exactly the ordered assignment coordinates. -/
theorem inputTemplate_variables (φ : CookLevinReduction.Formula) (n : ℕ) :
    (inputTemplate φ n).filterMap variableOf = List.finRange n := by
  simp only [inputTemplate, List.filterMap_append, List.filterMap_map,
    Function.comp_def, variableOf, filterMap_none, List.nil_append,
    List.filterMap_flatten, List.map_map, unitTemplate_variables]
  simp [← List.flatMap_def]

theorem inputTemplate_variables_nodup (φ : CookLevinReduction.Formula) (n : ℕ) :
    ((inputTemplate φ n).filterMap variableOf).Nodup := by
  rw [inputTemplate_variables]
  exact List.nodup_finRange n

/-- A present value in a duplicate-free filtered list has a unique source index. -/
theorem get_eq_of_filterMap_nodup {α β : Type*} (f : α → Option β)
    (l : List α) (hl : (l.filterMap f).Nodup)
    (i j : Fin l.length) (b : β)
    (hi : f (l.get i) = some b) (hj : f (l.get j) = some b) : i = j := by
  have hp := List.pairwise_filterMap.mp hl
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim ((List.pairwise_iff_get.mp hp i j hij) b hi b hj rfl)
  · exact hij
  · exact False.elim ((List.pairwise_iff_get.mp hp j i hij) b hj b hi rfl)

theorem exists_variablePosition (φ : CookLevinReduction.Formula) {n : ℕ}
    (i : Fin n) : ∃ j : Fin (inputTemplate φ n).length,
      (inputTemplate φ n).get j = .var i := by
  have hi : i ∈ (inputTemplate φ n).filterMap variableOf := by
    rw [inputTemplate_variables]
    exact List.mem_finRange i
  obtain ⟨g, hg, hgi⟩ := List.mem_filterMap.mp hi
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
  exact ⟨j, hj.trans ((variableOf_eq_some_iff g i).mp hgi)⟩

/-- The unique encoded input coordinate carrying an assignment variable. -/
noncomputable def variablePosition (φ : CookLevinReduction.Formula) (n : ℕ)
    (i : Fin n) : Fin (inputTemplate φ n).length :=
  Classical.choose (exists_variablePosition φ i)

@[simp] theorem position_get (φ : CookLevinReduction.Formula) (n : ℕ) (i : Fin n) :
    (inputTemplate φ n).get (variablePosition φ n i) = .var i :=
  Classical.choose_spec (exists_variablePosition φ i)

/-- Pinning never merges assignment coordinates or repeats one in the input. -/
theorem template_get_var_iff (φ : CookLevinReduction.Formula) (n : ℕ)
    (j : Fin (inputTemplate φ n).length) (i : Fin n) :
    (inputTemplate φ n).get j = .var i ↔ j = variablePosition φ n i := by
  constructor
  · intro hj
    apply get_eq_of_filterMap_nodup variableOf (inputTemplate φ n)
      (inputTemplate_variables_nodup φ n) j (variablePosition φ n i) i
    · rw [hj]
      rfl
    · rw [position_get]
      rfl
  · rintro rfl
    exact position_get φ n i

theorem variablePosition_injective (φ : CookLevinReduction.Formula) (n : ℕ) :
    Function.Injective (variablePosition φ n) := by
  intro i j hij
  have h := congrArg (inputTemplate φ n).get hij
  rw [position_get, position_get] at h
  exact CGate.var.inj h

/-- Exactly the input coordinates left free by assignment pinning. -/
def pinnedKeep (φ : CookLevinReduction.Formula) (n : ℕ)
    (j : Fin (inputTemplate φ n).length) : Prop :=
  ∃ i : Fin n, variablePosition φ n i = j

noncomputable instance pinnedKeep_decidable (φ : CookLevinReduction.Formula)
    (n : ℕ) : DecidablePred (pinnedKeep φ n) :=
  fun _ => inferInstanceAs (Decidable (∃ i : Fin n, variablePosition φ n i = _))

/-- Fixed encoded bits, obtained from the template without a SAT witness. -/
def pinnedFixed (φ : CookLevinReduction.Formula) (n : ℕ)
    (j : Fin (inputTemplate φ n).length) : Bool :=
  closedEval (fun _ => false) (pinnedSubstitution φ n j)

@[simp] theorem pinnedKeep_position (φ : CookLevinReduction.Formula) (n : ℕ)
    (i : Fin n) : pinnedKeep φ n (variablePosition φ n i) := ⟨i, rfl⟩

/-- Every coordinate outside the retained positions is a fixed Boolean gate. -/
theorem pinnedSubstitution_eq_cst_of_not_keep (φ : CookLevinReduction.Formula)
    (n : ℕ) (j : Fin (inputTemplate φ n).length) (hj : ¬ pinnedKeep φ n j) :
    pinnedSubstitution φ n j = .cst (pinnedFixed φ n j) := by
  have hc := pinnedSubstitution_closed φ n j
  cases hg : pinnedSubstitution φ n j with
  | var i =>
    have hp : j = variablePosition φ n i :=
      (template_get_var_iff φ n j i).mp hg
    exact False.elim (hj ⟨i, hp.symm⟩)
  | cst b => simp [pinnedFixed, hg, closedEval]
  | un op k => simp [hg, IsClosedGate] at hc
  | bin op k l => simp [hg, IsClosedGate] at hc

/-- Assignment pinning is an ordinary Boolean face: free positions retain
their distinct ambient input bits and all other positions are constants. -/
theorem pinnedFace_eq (φ : CookLevinReduction.Formula) (n : ℕ)
    (a : Fin (inputTemplate φ n).length → Bool) :
    (fun j => if pinnedKeep φ n j then a j else pinnedFixed φ n j) =
      (fun j => closedEval (fun i => a (variablePosition φ n i))
        (pinnedSubstitution φ n j)) := by
  classical
  funext j
  by_cases hj : pinnedKeep φ n j
  · obtain ⟨i, rfl⟩ := hj
    rw [if_pos (pinnedKeep_position φ n i)]
    change a (variablePosition φ n i) =
      closedEval (fun i => a (variablePosition φ n i))
        ((inputTemplate φ n).get (variablePosition φ n i))
    rw [position_get]
    rfl
  · rw [if_neg hj, pinnedSubstitution_eq_cst_of_not_keep φ n j hj]
    rfl

end GodMovePinnedFaceLayout

#print axioms GodMovePinnedFaceLayout.inputTemplate_variables
#print axioms GodMovePinnedFaceLayout.inputTemplate_variables_nodup
#print axioms GodMovePinnedFaceLayout.position_get
#print axioms GodMovePinnedFaceLayout.template_get_var_iff
#print axioms GodMovePinnedFaceLayout.variablePosition_injective
#print axioms GodMovePinnedFaceLayout.pinnedSubstitution_eq_cst_of_not_keep
#print axioms GodMovePinnedFaceLayout.pinnedFace_eq
