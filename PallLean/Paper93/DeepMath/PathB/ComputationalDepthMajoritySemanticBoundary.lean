import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMajorityFloor

/-!
# Semantic dynamic boundary for three-input majority

This is the observer boundary before thermodynamic projection: every live wire
is represented by its complete three-input truth table.  A boundary transition
adjoins the truth table produced by one arbitrary Boolean binary operation.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- An eight-row truth table for a Boolean function of three inputs. -/
abbrev Truth3 := Fin 8 → Bool

/-- The truth-table row selected by an assignment. -/
def assignmentCode (x : Fin 3 → Bool) : Fin 8 :=
  ⟨4 * (x 0).toNat + 2 * (x 1).toNat + (x 2).toNat, by
    have h0 := Bool.toNat_le (x 0)
    have h1 := Bool.toNat_le (x 1)
    have h2 := Bool.toNat_le (x 2)
    omega⟩

def truthEval (t : Truth3) (x : Fin 3 → Bool) : Bool :=
  t (assignmentCode x)

/-- Encode a three-input Boolean function as its truth table. -/
def truthCode (f : (Fin 3 → Bool) → Bool) : Truth3 :=
  fun x => f ![x.val.testBit 2, x.val.testBit 1, x.val.testBit 0]

/-- Apply a coded binary truth table pointwise to two semantic wires. -/
def truthBin (op : Fin 16) (a b : Truth3) : Truth3 :=
  fun x => codedBin op (a x) (b x)

/-- A semantic observer state remembers the truth tables currently exposed at
the live boundary. -/
abbrev SemanticBoundary3 := Finset Truth3

def initialSemanticBoundary3 : SemanticBoundary3 :=
  {truthCode (fun x => x 0), truthCode (fun x => x 1), truthCode (fun x => x 2)}

/-- All one-gate successors of one semantic boundary. -/
def semanticSuccessors (S : SemanticBoundary3) : Finset SemanticBoundary3 :=
  S.biUnion fun a => S.biUnion fun b =>
    Finset.univ.image fun op : Fin 16 => insert (truthBin op a b) S

def semanticBoundaryLayer : Nat → Finset SemanticBoundary3
  | 0 => {initialSemanticBoundary3}
  | k + 1 => (semanticBoundaryLayer k).biUnion semanticSuccessors

/-! A packed version of the same observer state is used for finite kernel
checking.  Equality of packed truth tables is equality in `Fin 256`, avoiding
repeated extensional comparisons of eight-row functions. -/

abbrev PackedTruth3 := Fin 256
abbrev PackedSemanticBoundary3 := Finset PackedTruth3

def packTruth (t : Truth3) : PackedTruth3 :=
  Fin.ofNat 256 (∑ i : Fin 8, if t i then 2 ^ i.val else 0)

def packedTruthBin (op : Fin 16) (a b : PackedTruth3) : PackedTruth3 :=
  Fin.ofNat 256 (∑ i : Fin 8,
    if codedBin op (a.val.testBit i.val) (b.val.testBit i.val)
    then 2 ^ i.val else 0)

def initialPackedBoundary3 : PackedSemanticBoundary3 :=
  {packTruth (truthCode (fun x => x 0)), packTruth (truthCode (fun x => x 1)),
    packTruth (truthCode (fun x => x 2))}

def packedSuccessors (S : PackedSemanticBoundary3) : Finset PackedSemanticBoundary3 :=
  S.biUnion fun a => S.biUnion fun b =>
    Finset.univ.image fun op : Fin 16 => insert (packedTruthBin op a b) S

def packedBoundaryLayer : Nat → Finset PackedSemanticBoundary3
  | 0 => {initialPackedBoundary3}
  | k + 1 => (packedBoundaryLayer k).biUnion packedSuccessors

def packedMajorityThree : PackedTruth3 :=
  packTruth (truthCode majorityThreeFloor)

def packedFirstOutputs : Finset PackedTruth3 :=
  initialPackedBoundary3.biUnion fun a =>
    initialPackedBoundary3.biUnion fun b =>
      Finset.univ.image fun op : Fin 16 => packedTruthBin op a b

theorem initialPackedBoundary3_eq :
    initialPackedBoundary3 = {(240 : PackedTruth3), 204, 170} := by
  decide

theorem packedMajorityThree_eq : packedMajorityThree = (232 : PackedTruth3) := by
  decide

set_option maxRecDepth 10000 in
theorem packedFirstOutputs_eq : packedFirstOutputs =
    ({0, 3, 5, 10, 12, 15, 17, 34, 48, 51, 60, 63, 68, 80, 85, 90, 95,
      102, 119, 136, 153, 160, 165, 170, 175, 187, 192, 195, 204, 207, 221,
      238, 240, 243, 245, 250, 252, 255} : Finset PackedTruth3) := by
  decide

theorem packedFirstOutputs_card : packedFirstOutputs.card = 38 := by
  rw [packedFirstOutputs_eq]
  decide

structure ThreeTransitionProgram where
  op₀ : Fin 16
  left₀ : Fin 3
  right₀ : Fin 3
  op₁ : Fin 16
  left₁ : Fin 4
  right₁ : Fin 4
  op₂ : Fin 16
  left₂ : Fin 5
  right₂ : Fin 5

def source3 (x : Fin 3 → Bool) (i : Fin 3) : Bool := x i

def source4 (x : Fin 3 → Bool) (g₀ : Bool) (i : Fin 4) : Bool :=
  if h : i.val < 3 then x ⟨i.val, h⟩ else g₀

def source5 (x : Fin 3 → Bool) (g₀ g₁ : Bool) (i : Fin 5) : Bool :=
  if h : i.val < 3 then x ⟨i.val, h⟩ else if i.val = 3 then g₀ else g₁

def ThreeTransitionProgram.eval (p : ThreeTransitionProgram)
    (x : Fin 3 → Bool) : Bool :=
  let g₀ := codedBin p.op₀ (source3 x p.left₀) (source3 x p.right₀)
  let g₁ := codedBin p.op₁ (source4 x g₀ p.left₁) (source4 x g₀ p.right₁)
  codedBin p.op₂ (source5 x g₀ g₁ p.left₂) (source5 x g₀ g₁ p.right₂)

/- The semantic heart of the dynamic-boundary argument: no trajectory of
three arbitrary binary transitions from the three coordinate observers has
majority as its final exposed wire. -/
end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
