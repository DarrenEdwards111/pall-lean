import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameReceivedWordListDecodingBridge

/-!
# Received-word radius barrier

The received-word bridge has a hidden quantitative parameter: its Hamming
radius.  At radius `N` every length-`N` codeword is close to one fixed word, so
the projection exists for every cell map but retains the full `2^m` ambiguity.
At small radius, by contrast, every pair of codewords collapsed into one cell
must be within distance `2R`.

Thus a separated expander code does not manufacture the semantic bridge.  If
its minimum distance exceeds `2R`, the bridge already forces the amplituhedron
cell map to be injective.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge

/-! ## Metric calibration -/

/-- Hamming distance is symmetric. -/
theorem hammingDistance_comm
    {N : Nat} (x y : Assignment N) :
    hammingDistance x y = hammingDistance y x := by
  classical
  unfold hammingDistance
  congr 1
  ext i
  simp [ne_comm]

/-- Hamming distance obeys the triangle inequality. -/
theorem hammingDistance_triangle
    {N : Nat} (x y z : Assignment N) :
    hammingDistance x z <= hammingDistance x y + hammingDistance y z := by
  classical
  let xz := (Finset.univ : Finset (Fin N)).filter (fun i => x i ≠ z i)
  let xy := (Finset.univ : Finset (Fin N)).filter (fun i => x i ≠ y i)
  let yz := (Finset.univ : Finset (Fin N)).filter (fun i => y i ≠ z i)
  have hsubset : xz ⊆ xy ∪ yz := by
    intro i hi
    simp only [xz, xy, yz, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union] at hi ⊢
    by_cases hxy : x i = y i
    · right
      intro hyz
      exact hi (hxy.trans hyz)
    · exact Or.inl hxy
  calc
    hammingDistance x z = xz.card := rfl
    _ <= (xy ∪ yz).card := Finset.card_le_card hsubset
    _ <= xy.card + yz.card := Finset.card_union_le xy yz
    _ = hammingDistance x y + hammingDistance y z := rfl

/-- No length-`N` Boolean words are farther apart than `N`. -/
theorem hammingDistance_le_length
    {N : Nat} (x y : Assignment N) :
    hammingDistance x y <= N := by
  classical
  unfold hammingDistance
  calc
    ((Finset.univ : Finset (Fin N)).filter (fun i => x i ≠ y i)).card
        <= (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := by simp

/-! ## Large radius is vacuous -/

/-- The constant-zero received word gives a radius-`N` projection for every
code and every cell map, without using the cells at all. -/
noncomputable def vacuousRadiusProjection
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell) :
    CellReceivedWordProjection C cellOf N where
  received _ := fun _ => false
  trueCodewordNear _ := hammingDistance_le_length _ _

/-- At the vacuous radius, every semantic message lies in every Hamming ball. -/
theorem messageBall_length_eq_univ
    {m N : Nat} (C : RedundantContinuationCode m N)
    (received : Assignment N) :
    messageBall C received N = Finset.univ := by
  classical
  unfold messageBall
  apply Finset.filter_eq_self.mpr
  intro a _
  exact hammingDistance_le_length _ _

/-- Consequently the radius-`N` list has the full `2^m` semantic size. -/
theorem messageBall_length_card
    {m N : Nat} (C : RedundantContinuationCode m N)
    (received : Assignment N) :
    (messageBall C received N).card = 2 ^ m := by
  rw [messageBall_length_eq_univ]
  simp

/-! ## Small radius forces small cell diameter -/

/-- A received-word projection of radius `R` bounds the codeword diameter of
every cell by `2R`. -/
theorem codeword_distance_le_two_mul_radius
    {m N R : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf R)
    {a b : Assignment m} (hab : cellOf a = cellOf b) :
    hammingDistance (C.encode a) (C.encode b) <= 2 * R := by
  have ha := P.trueCodewordNear a
  have hb := P.trueCodewordNear b
  rw [hab] at ha
  have htri := hammingDistance_triangle
    (C.encode a) (P.received (cellOf b)) (C.encode b)
  rw [hammingDistance_comm (C.encode a) (P.received (cellOf b))] at htri
  omega

/-- A code has minimum distance strictly above `delta` when distinct semantic
messages have codeword distance above `delta`. -/
def MinimumDistanceAbove
    {m N : Nat} (C : RedundantContinuationCode m N) (delta : Nat) : Prop :=
  forall a b : Assignment m, a ≠ b -> delta < hammingDistance (C.encode a) (C.encode b)

/-- If the code's minimum distance exceeds twice the projection radius, the
cell map must already be injective. -/
theorem cellOf_injective_of_minDistanceAbove_two_mul
    {m N R : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf R)
    (hsep : MinimumDistanceAbove C (2 * R)) :
    Function.Injective cellOf := by
  intro a b hab
  by_contra hne
  have hfar := hsep a b hne
  have hnear := codeword_distance_le_two_mul_radius C cellOf P hab
  omega

/-- Exact radius calibration: the projection requirement ranges from automatic
and exponentially ambiguous at radius `N` to injectivity-forcing below half the
code distance. -/
theorem receivedWord_radius_calibration
    {m N R : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf R)
    (hsep : MinimumDistanceAbove C (2 * R)) :
    Nonempty (CellReceivedWordProjection C cellOf N) ∧
      (forall received : Assignment N,
        (messageBall C received N).card = 2 ^ m) ∧
      Function.Injective cellOf := by
  exact ⟨⟨vacuousRadiusProjection C cellOf⟩,
    messageBall_length_card C,
    cellOf_injective_of_minDistanceAbove_two_mul C cellOf P hsep⟩

end PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier.hammingDistance_triangle
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier.messageBall_length_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier.codeword_distance_le_two_mul_radius
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier.cellOf_injective_of_minDistanceAbove_two_mul
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier.receivedWord_radius_calibration
