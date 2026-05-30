import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinCommunicationMatrix

namespace SATDepthMachine

theorem lookup_ofFn {n : Nat} (f : Fin n -> Bool) (i : Fin n) :
    RawAssignment.lookup (List.ofFn f) i.val = some (f i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero => simp [RawAssignment.lookup]
      | succ i =>
          simp [RawAssignment.lookup, ih]

end SATDepthMachine
