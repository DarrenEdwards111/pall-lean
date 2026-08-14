import PallLean.Paper93.DeepMath.PathB.ComputationalDepthROTExtraction

/-!
# Three-bit majority lies above the dependency-cone floor

The external exact-synthesis search finds that three-bit majority needs four
binary gates.  This file certifies the first nontrivial part of that result
without circuit enumeration or `native_decide`: the read-once-tree extraction
theorem excludes every five-gate implementation.  A concrete seven-gate
implementation leaves the kernel-certified frontier `6 ≤ cbudget ≤ 7`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

/-- Three-bit majority, in a form with a verified seven-gate circuit. -/
def majorityThreeFloor (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 2 && (x 0 || x 1))

/-- All three input coordinates are essential. -/
theorem majorityThreeFloor_depSet :
    depSet majorityThreeFloor = (Finset.univ : Finset (Fin 3)) := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  fin_cases i
  · exact mem_depSet.mpr ⟨![false, true, false], true, by decide⟩
  · exact mem_depSet.mpr ⟨![true, false, false], true, by decide⟩
  · exact mem_depSet.mpr ⟨![true, false, false], true, by decide⟩

theorem majorityThreeFloor_no_split_one :
    ¬ ∃ op g : Bool → Bool → Bool,
      ∀ a b c, majorityThreeFloor ![a, b, c] = op a (g b c) := by
  decide

theorem majorityThreeFloor_no_split_two :
    ¬ ∃ op g : Bool → Bool → Bool,
      ∀ a b c, majorityThreeFloor ![a, b, c] = op b (g a c) := by
  decide

theorem majorityThreeFloor_no_split_three :
    ¬ ∃ op g : Bool → Bool → Bool,
      ∀ a b c, majorityThreeFloor ![a, b, c] = op c (g a b) := by
  decide

/-- Majority's full three-coordinate restriction is unsplittable, so the
read-once-tree floor theorem adds one gate beyond the cone bound. -/
theorem majorityThreeFloor_cbudget_lower :
    6 ≤ cbudget majorityThreeFloor := by
  apply cbudget_above_floor_of_unsplittable majorityThreeFloor
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide) (by decide)
      (fun _ => false)
  · simpa [Split1, Function.update, Fin.cases] using majorityThreeFloor_no_split_one
  · simpa [Split2, Function.update, Fin.cases] using majorityThreeFloor_no_split_two
  · simpa [Split3, Function.update, Fin.cases] using majorityThreeFloor_no_split_three

/-- A seven-gate implementation of three-bit majority. -/
def majorityThreeFloorCircuit : List (CGate 3) :=
  [CGate.var ⟨0, by omega⟩,
   CGate.var ⟨1, by omega⟩,
   CGate.var ⟨2, by omega⟩,
   CGate.bin (fun a b => a && b) 0 1,
   CGate.bin (fun a b => a || b) 0 1,
   CGate.bin (fun a b => a && b) 2 4,
   CGate.bin (fun a b => a || b) 3 5]

theorem majorityThreeFloorCircuit_computes :
    computes majorityThreeFloorCircuit majorityThreeFloor := by
  intro x
  have hx : x = ![x 0, x 1, x 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> decide

theorem majorityThreeFloor_cbudget_upper :
    cbudget majorityThreeFloor ≤ 7 := by
  have h : cbudget majorityThreeFloor ≤ majorityThreeFloorCircuit.length :=
    Nat.sInf_le ⟨majorityThreeFloorCircuit, majorityThreeFloorCircuit_computes, rfl⟩
  simpa [majorityThreeFloorCircuit] using h

/-- Kernel-certified exact-synthesis frontier.  Only six-gate circuits remain
to exclude before the external exact value `7` is fully internalized. -/
theorem majorityThreeFloor_cbudget_frontier :
    6 ≤ cbudget majorityThreeFloor ∧ cbudget majorityThreeFloor ≤ 7 :=
  ⟨majorityThreeFloor_cbudget_lower, majorityThreeFloor_cbudget_upper⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majorityThreeFloor_cbudget_lower
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majorityThreeFloor_cbudget_upper
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majorityThreeFloor_cbudget_frontier
