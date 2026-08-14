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

def reverseCodedOp (op : Fin 16) : Fin 16 :=
  Fin.ofNat 16
    ((if codedBin op false false then 1 else 0) +
     (if codedBin op true false then 2 else 0) +
     (if codedBin op false true then 4 else 0) +
     (if codedBin op true true then 8 else 0))

theorem codedBin_reverse (op : Fin 16) (a b : Bool) :
    codedBin (reverseCodedOp op) a b = codedBin op b a := by
  fin_cases op <;> cases a <;> cases b <;> decide

def permuteAssignment (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → Bool) :
    Fin 3 → Bool := fun i => x (σ i)

@[simp] theorem permuteAssignment_apply_symm (σ : Equiv.Perm (Fin 3))
    (x : Fin 3 → Bool) :
    permuteAssignment σ (permuteAssignment σ.symm x) = x := by
  funext i
  simp [permuteAssignment]

def liftSource4 (σ : Equiv.Perm (Fin 3)) (i : Fin 4) : Fin 4 :=
  if h : i.val < 3 then ⟨(σ ⟨i.val, h⟩).val, by omega⟩ else 3

def liftSource5 (σ : Equiv.Perm (Fin 3)) (i : Fin 5) : Fin 5 :=
  if h : i.val < 3 then ⟨(σ ⟨i.val, h⟩).val, by omega⟩ else i

theorem sourceFour_liftSource4 (σ : Equiv.Perm (Fin 3))
    (x : Fin 3 → Bool) (g : Bool) (i : Fin 4) :
    sourceFour x g (liftSource4 σ i) = sourceFour (permuteAssignment σ x) g i := by
  fin_cases i <;> simp [sourceFour, liftSource4, permuteAssignment]

theorem sourceFive_liftSource5 (σ : Equiv.Perm (Fin 3))
    (x : Fin 3 → Bool) (g₀ g₁ : Bool) (i : Fin 5) :
    sourceFive x g₀ g₁ (liftSource5 σ i) =
      sourceFive (permuteAssignment σ x) g₀ g₁ i := by
  fin_cases i <;> simp [sourceFive, liftSource5, permuteAssignment]

theorem majorityThreeFloor_permute (σ : Equiv.Perm (Fin 3))
    (x : Fin 3 → Bool) :
    majorityThreeFloor (permuteAssignment σ x) = majorityThreeFloor x := by
  decide +revert

theorem threeBinaryProgram_permute (σ : Equiv.Perm (Fin 3))
    (op₀ op₁ op₂ : Fin 16) (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (a₂ b₂ : Fin 5) (x : Fin 3 → Bool) :
    threeBinaryProgram op₀ op₁ op₂ (σ a₀) (σ b₀)
        (liftSource4 σ a₁) (liftSource4 σ b₁)
        (liftSource5 σ a₂) (liftSource5 σ b₂) x =
      threeBinaryProgram op₀ op₁ op₂ a₀ b₀ a₁ b₁ a₂ b₂
        (permuteAssignment σ x) := by
  simp [threeBinaryProgram, sourceThree, sourceFour_liftSource4,
    sourceFive_liftSource5, permuteAssignment]

theorem threeBinaryProgram_reverse_first
    (op₀ op₁ op₂ : Fin 16) (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (a₂ b₂ : Fin 5) (x : Fin 3 → Bool) :
    threeBinaryProgram (reverseCodedOp op₀) op₁ op₂ b₀ a₀ a₁ b₁ a₂ b₂ x =
      threeBinaryProgram op₀ op₁ op₂ a₀ b₀ a₁ b₁ a₂ b₂ x := by
  simp [threeBinaryProgram, codedBin_reverse]

theorem threeBinaryProgram_reverse_second
    (op₀ op₁ op₂ : Fin 16) (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (a₂ b₂ : Fin 5) (x : Fin 3 → Bool) :
    threeBinaryProgram op₀ (reverseCodedOp op₁) op₂ a₀ b₀ b₁ a₁ a₂ b₂ x =
      threeBinaryProgram op₀ op₁ op₂ a₀ b₀ a₁ b₁ a₂ b₂ x := by
  simp [threeBinaryProgram, codedBin_reverse]

theorem threeBinaryProgram_reverse_root
    (op₀ op₁ op₂ : Fin 16) (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (a₂ b₂ : Fin 5) (x : Fin 3 → Bool) :
    threeBinaryProgram op₀ op₁ (reverseCodedOp op₂) a₀ b₀ a₁ b₁ b₂ a₂ x =
      threeBinaryProgram op₀ op₁ op₂ a₀ b₀ a₁ b₁ a₂ b₂ x := by
  simp [threeBinaryProgram, codedBin_reverse]

def NoMajoritySchedule (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (a₂ b₂ : Fin 5) : Prop :=
  ¬ ∃ op₀ op₁ op₂ : Fin 16, ∀ x : Fin 3 → Bool,
    threeBinaryProgram op₀ op₁ op₂ a₀ b₀ a₁ b₁ a₂ b₂ x = majorityThreeFloor x

theorem NoMajoritySchedule.reverse_first {a₀ b₀ : Fin 3} {a₁ b₁ : Fin 4}
    {a₂ b₂ : Fin 5} (h : NoMajoritySchedule a₀ b₀ a₁ b₁ a₂ b₂) :
    NoMajoritySchedule b₀ a₀ a₁ b₁ a₂ b₂ := by
  rintro ⟨op₀, op₁, op₂, hcomp⟩
  apply h
  refine ⟨reverseCodedOp op₀, op₁, op₂, ?_⟩
  intro x
  rw [threeBinaryProgram_reverse_first]
  exact hcomp x

theorem NoMajoritySchedule.reverse_second {a₀ b₀ : Fin 3} {a₁ b₁ : Fin 4}
    {a₂ b₂ : Fin 5} (h : NoMajoritySchedule a₀ b₀ a₁ b₁ a₂ b₂) :
    NoMajoritySchedule a₀ b₀ b₁ a₁ a₂ b₂ := by
  rintro ⟨op₀, op₁, op₂, hcomp⟩
  apply h
  refine ⟨op₀, reverseCodedOp op₁, op₂, ?_⟩
  intro x
  rw [threeBinaryProgram_reverse_second]
  exact hcomp x

theorem NoMajoritySchedule.reverse_root {a₀ b₀ : Fin 3} {a₁ b₁ : Fin 4}
    {a₂ b₂ : Fin 5} (h : NoMajoritySchedule a₀ b₀ a₁ b₁ a₂ b₂) :
    NoMajoritySchedule a₀ b₀ a₁ b₁ b₂ a₂ := by
  rintro ⟨op₀, op₁, op₂, hcomp⟩
  apply h
  refine ⟨op₀, op₁, reverseCodedOp op₂, ?_⟩
  intro x
  rw [threeBinaryProgram_reverse_root]
  exact hcomp x

def orderedTriple (a b c : Fin 3) : Fin 3 → Fin 3 := fun i => ![a, b, c] i

theorem orderedTriple_injective {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (orderedTriple a b c) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [orderedTriple] <;> aesop

noncomputable def orderedTriplePerm (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (orderedTriple a b c)
    (orderedTriple_injective hab hac hbc).bijective_of_finite

@[simp] theorem orderedTriplePerm_zero (a b c : Fin 3) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    orderedTriplePerm a b c hab hac hbc 0 = a := rfl

@[simp] theorem orderedTriplePerm_one (a b c : Fin 3) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    orderedTriplePerm a b c hab hac hbc 1 = b := rfl

@[simp] theorem orderedTriplePerm_two (a b c : Fin 3) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    orderedTriplePerm a b c hab hac hbc 2 = c := rfl

def primarySource4 (i : Fin 3) : Fin 4 := ⟨i.val, by omega⟩

def primarySource5 (i : Fin 3) : Fin 5 := ⟨i.val, by omega⟩

def scheduleInputSeen (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (a₂ b₂ : Fin 5) (i : Fin 3) : Prop :=
  a₂.val = i.val ∨ b₂.val = i.val ∨
  a₁.val = i.val ∨ b₁.val = i.val ∨
  a₀ = i ∨ b₀ = i

instance (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5) (i : Fin 3) :
    Decidable (scheduleInputSeen a₀ b₀ a₁ b₁ a₂ b₂ i) := by
  unfold scheduleInputSeen
  infer_instance

def liveThreeTransitionSchedule (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (a₂ b₂ : Fin 5) : Prop :=
  a₀ ≠ b₀ ∧ a₁ ≠ b₁ ∧ a₂ ≠ b₂ ∧
  (a₂.val = 4 ∨ b₂.val = 4) ∧
  (a₂.val = 3 ∨ b₂.val = 3 ∨ a₁.val = 3 ∨ b₁.val = 3) ∧
  ∀ i : Fin 3, scheduleInputSeen a₀ b₀ a₁ b₁ a₂ b₂ i

instance (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5) :
    Decidable (liveThreeTransitionSchedule a₀ b₀ a₁ b₁ a₂ b₂) := by
  unfold liveThreeTransitionSchedule
  infer_instance

inductive LiveScheduleShape
  | parallel
  | chainFirstResult
  | chainPairInput
  | chainThirdInput
  deriving DecidableEq

def rootOtherSource (a₂ b₂ : Fin 5) : Fin 5 :=
  if a₂.val = 4 then b₂ else a₂

def liveScheduleShape (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (a₂ b₂ : Fin 5) : LiveScheduleShape :=
  let d := rootOtherSource a₂ b₂
  let secondReadsFirst := a₁.val = 3 ∨ b₁.val = 3
  if d.val = 3 then
    if secondReadsFirst then .chainFirstResult else .parallel
  else if d.val = a₀.val ∨ d.val = b₀.val then
    .chainPairInput
  else
    .chainThirdInput

theorem liveScheduleShape_exhaustive
    (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5)
    (_h : liveThreeTransitionSchedule a₀ b₀ a₁ b₁ a₂ b₂) :
    liveScheduleShape a₀ b₀ a₁ b₁ a₂ b₂ = .parallel ∨
    liveScheduleShape a₀ b₀ a₁ b₁ a₂ b₂ = .chainFirstResult ∨
    liveScheduleShape a₀ b₀ a₁ b₁ a₂ b₂ = .chainPairInput ∨
    liveScheduleShape a₀ b₀ a₁ b₁ a₂ b₂ = .chainThirdInput := by
  cases hshape : liveScheduleShape a₀ b₀ a₁ b₁ a₂ b₂ <;> simp

theorem liveSchedule_parallel_01_02_ne_majority :
    ¬ ∃ op₀ op₁ op₂ : Fin 16, ∀ x : Fin 3 → Bool,
      threeBinaryProgram op₀ op₁ op₂ 0 1 0 2 3 4 x = majorityThreeFloor x := by
  simpa [threeBinaryProgram, parallelThreeBinaryProgram, sourceFour, sourceFive]
    using parallelCanonical_ne_majority

theorem liveSchedule_chain_firstResult_ne_majority :
    ¬ ∃ op₀ op₁ op₂ : Fin 16, ∀ x : Fin 3 → Bool,
      threeBinaryProgram op₀ op₁ op₂ 0 1 3 2 4 3 x = majorityThreeFloor x := by
  simpa [threeBinaryProgram, chainThreeBinaryProgram, sourceFour, sourceFive]
    using chainCanonical_firstResult_ne_majority

theorem liveSchedule_chain_pairInput_ne_majority :
    ¬ ∃ op₀ op₁ op₂ : Fin 16, ∀ x : Fin 3 → Bool,
      threeBinaryProgram op₀ op₁ op₂ 0 1 3 2 4 0 x = majorityThreeFloor x := by
  simpa [threeBinaryProgram, chainThreeBinaryProgram, sourceFour, sourceFive]
    using chainCanonical_pairInput_ne_majority

theorem liveSchedule_chain_thirdInput_ne_majority :
    ¬ ∃ op₀ op₁ op₂ : Fin 16, ∀ x : Fin 3 → Bool,
      threeBinaryProgram op₀ op₁ op₂ 0 1 3 2 4 2 x = majorityThreeFloor x := by
  simpa [threeBinaryProgram, chainThreeBinaryProgram, sourceFour, sourceFive]
    using chainCanonical_thirdInput_ne_majority

theorem liveSchedule_parallel_distinct_ne_majority
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ∃ op₀ op₁ op₂ : Fin 16, ∀ x : Fin 3 → Bool,
      threeBinaryProgram op₀ op₁ op₂ a b (primarySource4 a) (primarySource4 c)
        3 4 x = majorityThreeFloor x := by
  rintro ⟨op₀, op₁, op₂, h⟩
  apply liveSchedule_parallel_01_02_ne_majority
  refine ⟨op₀, op₁, op₂, ?_⟩
  intro y
  let σ := orderedTriplePerm a b c hab hac hbc
  let x := permuteAssignment σ.symm y
  have hp := threeBinaryProgram_permute σ op₀ op₁ op₂ 0 1 0 2 3 4 x
  have hh := h x
  have hmaj := majorityThreeFloor_permute σ.symm y
  simpa [σ, x, permuteAssignment, liftSource4, liftSource5, primarySource4] using
    hp.symm.trans (hh.trans hmaj)

theorem liveSchedule_chain_firstResult_distinct_ne_majority
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ∃ op₀ op₁ op₂ : Fin 16, ∀ x : Fin 3 → Bool,
      threeBinaryProgram op₀ op₁ op₂ a b 3 (primarySource4 c) 4 3 x =
        majorityThreeFloor x := by
  rintro ⟨op₀, op₁, op₂, h⟩
  apply liveSchedule_chain_firstResult_ne_majority
  refine ⟨op₀, op₁, op₂, ?_⟩
  intro y
  let σ := orderedTriplePerm a b c hab hac hbc
  let x := permuteAssignment σ.symm y
  have hp := threeBinaryProgram_permute σ op₀ op₁ op₂ 0 1 3 2 4 3 x
  have hh := h x
  have hmaj := majorityThreeFloor_permute σ.symm y
  simpa [σ, x, permuteAssignment, liftSource4, liftSource5, primarySource4] using
    hp.symm.trans (hh.trans hmaj)

theorem liveSchedule_chain_pairInput_distinct_ne_majority
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ∃ op₀ op₁ op₂ : Fin 16, ∀ x : Fin 3 → Bool,
      threeBinaryProgram op₀ op₁ op₂ a b 3 (primarySource4 c) 4
        (primarySource5 a) x = majorityThreeFloor x := by
  rintro ⟨op₀, op₁, op₂, h⟩
  apply liveSchedule_chain_pairInput_ne_majority
  refine ⟨op₀, op₁, op₂, ?_⟩
  intro y
  let σ := orderedTriplePerm a b c hab hac hbc
  let x := permuteAssignment σ.symm y
  have hp := threeBinaryProgram_permute σ op₀ op₁ op₂ 0 1 3 2 4 0 x
  have hh := h x
  have hmaj := majorityThreeFloor_permute σ.symm y
  simpa [σ, x, permuteAssignment, liftSource4, liftSource5, primarySource4,
    primarySource5] using hp.symm.trans (hh.trans hmaj)

theorem liveSchedule_chain_thirdInput_distinct_ne_majority
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ∃ op₀ op₁ op₂ : Fin 16, ∀ x : Fin 3 → Bool,
      threeBinaryProgram op₀ op₁ op₂ a b 3 (primarySource4 c) 4
        (primarySource5 c) x = majorityThreeFloor x := by
  rintro ⟨op₀, op₁, op₂, h⟩
  apply liveSchedule_chain_thirdInput_ne_majority
  refine ⟨op₀, op₁, op₂, ?_⟩
  intro y
  let σ := orderedTriplePerm a b c hab hac hbc
  let x := permuteAssignment σ.symm y
  have hp := threeBinaryProgram_permute σ op₀ op₁ op₂ 0 1 3 2 4 2 x
  have hh := h x
  have hmaj := majorityThreeFloor_permute σ.symm y
  simpa [σ, x, permuteAssignment, liftSource4, liftSource5, primarySource4,
    primarySource5] using hp.symm.trans (hh.trans hmaj)

theorem noMajoritySchedule_parallel (a b c : Fin 3) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    NoMajoritySchedule a b (primarySource4 a) (primarySource4 c) 3 4 := by
  simpa [NoMajoritySchedule] using
    liveSchedule_parallel_distinct_ne_majority a b c hab hac hbc

theorem noMajoritySchedule_chain_firstResult (a b c : Fin 3) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    NoMajoritySchedule a b 3 (primarySource4 c) 4 3 := by
  simpa [NoMajoritySchedule] using
    liveSchedule_chain_firstResult_distinct_ne_majority a b c hab hac hbc

theorem noMajoritySchedule_chain_pairInput (a b c : Fin 3) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    NoMajoritySchedule a b 3 (primarySource4 c) 4 (primarySource5 a) := by
  simpa [NoMajoritySchedule] using
    liveSchedule_chain_pairInput_distinct_ne_majority a b c hab hac hbc

theorem noMajoritySchedule_chain_thirdInput (a b c : Fin 3) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    NoMajoritySchedule a b 3 (primarySource4 c) 4 (primarySource5 c) := by
  simpa [NoMajoritySchedule] using
    liveSchedule_chain_thirdInput_distinct_ne_majority a b c hab hac hbc


/- The semantic heart of the dynamic-boundary argument: no trajectory of
three arbitrary binary transitions from the three coordinate observers has
majority as its final exposed wire. -/
end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
