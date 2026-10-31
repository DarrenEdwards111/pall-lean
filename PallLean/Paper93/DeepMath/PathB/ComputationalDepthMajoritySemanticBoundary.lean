import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMajorityFloor

/-!
# Semantic dynamic boundary for three-input majority

This is the observer boundary before thermodynamic projection: every live wire
is represented by its complete three-input truth table.  A boundary transition
adjoins the truth table produced by one arbitrary Boolean binary operation.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

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

def codeBooleanBinary (op : Bool → Bool → Bool) : Fin 16 :=
  Fin.ofNat 16
    ((if op false false then 1 else 0) +
     (if op false true then 2 else 0) +
     (if op true false then 4 else 0) +
     (if op true true then 8 else 0))

theorem codedBin_codeBooleanBinary (op : Bool → Bool → Bool) (a b : Bool) :
    codedBin (codeBooleanBinary op) a b = op a b := by
  by_cases h00 : op false false <;> by_cases h01 : op false true <;>
    by_cases h10 : op true false <;> by_cases h11 : op true true <;>
    cases a <;> cases b <;> simp_all [codedBin, codeBooleanBinary] <;> decide

theorem majoritySix_coneVars_card_three (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6) :
    (coneVars c).card = 3 := by
  rw [majoritySix_varsEq c hcomp hlen, majorityThreeFloor_depSet,
    Finset.card_univ, Fintype.card_fin]

open Classical in theorem majoritySix_nonvarPositions_card_three (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6) :
    ((Finset.range 6).filter
      (fun w => ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i)).card = 3 := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.range 6)
    (p := fun w => ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i)
  have hvars : ((Finset.range 6).filter
      (fun w => ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i)).card = 3 := by
    rw [← majoritySix_cone_all c hcomp hlen]
    exact majoritySix_coneVars_card_three c hcomp hlen
  simp only [Finset.card_range] at hpartition
  omega

theorem majorityThreeFloor_ne_coordinate (i : Fin 3) :
    ¬ ∀ x : Fin 3 → Bool, majorityThreeFloor x = x i := by
  fin_cases i
  · intro h
    have := h ![true, false, false]
    simp [majorityThreeFloor] at this
  · intro h
    have := h ![false, true, false]
    simp [majorityThreeFloor] at this
  · intro h
    have := h ![false, false, true]
    simp [majorityThreeFloor] at this

theorem majoritySix_first_is_var (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6) :
    ∃ i : Fin 3, c.getD 0 (.cst false) = CGate.var i := by
  rcases majoritySix_gate_dichotomy c hcomp hlen 0 (by omega) with hvar | hbin
  · exact hvar
  · obtain ⟨op, j, k, -, hj, hk, -⟩ := hbin
    omega

theorem majoritySix_root_is_bin (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6) :
    ∃ (op : Bool → Bool → Bool) (j k : ℕ),
      c.getD 5 (.cst false) = CGate.bin op j k ∧ j < 5 ∧ k < 5 ∧ j ≠ k := by
  rcases majoritySix_gate_dichotomy c hcomp hlen 5 (by omega) with hvar | hbin
  · obtain ⟨i, hg⟩ := hvar
    exfalso
    apply majorityThreeFloor_ne_coordinate i
    intro x
    have hw := wire_eq c x (show 5 < c.length by omega)
    rw [hg] at hw
    simp only [evalGate] at hw
    have hc := hcomp x
    rw [output_eq_wire, hlen] at hc
    exact hc.symm.trans hw
  · exact hbin

open Classical in theorem majoritySix_internalBinaryPositions_card_two
    (c : List (CGate 3)) (hcomp : computes c majorityThreeFloor)
    (hlen : c.length = 6) :
    ((((Finset.range 6).filter
      (fun w => ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i)).erase 0).erase 5).card = 2 := by
  let S := (Finset.range 6).filter
    (fun w => ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i)
  have hScard : S.card = 3 := majoritySix_nonvarPositions_card_three c hcomp hlen
  obtain ⟨i₀, hg₀⟩ := majoritySix_first_is_var c hcomp hlen
  have h0 : 0 ∉ S := by
    intro hm
    change 0 ∈ (Finset.range 6).filter
      (fun w => ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i) at hm
    rw [Finset.mem_filter] at hm
    exact hm.2 ⟨i₀, hg₀⟩
  obtain ⟨op, j, k, hg₅, -, -, -⟩ := majoritySix_root_is_bin c hcomp hlen
  have h5 : 5 ∈ S := by
    change 5 ∈ (Finset.range 6).filter
      (fun w => ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i)
    rw [Finset.mem_filter]
    refine ⟨by simp, ?_⟩
    rintro ⟨i, hi⟩
    rw [hg₅] at hi
    cases hi
  change ((S.erase 0).erase 5).card = 2
  rw [Finset.erase_eq_self.mpr h0, Finset.card_erase_of_mem h5]
  omega

structure SixBinaryChronology (c : List (CGate 3)) where
  first : ℕ
  second : ℕ
  first_pos : 0 < first
  ordered : first < second
  second_before_root : second < 5
  first_nonvar : ¬ ∃ i : Fin 3, c.getD first (.cst false) = CGate.var i
  second_nonvar : ¬ ∃ i : Fin 3, c.getD second (.cst false) = CGate.var i
  exhaustive : ∀ w, w < 6 → w ≠ 0 → w ≠ 5 →
    (¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i) →
    w = first ∨ w = second

open Classical in theorem majoritySix_binaryChronology
    (c : List (CGate 3)) (hcomp : computes c majorityThreeFloor)
    (hlen : c.length = 6) : Nonempty (SixBinaryChronology c) := by
  let T := (((Finset.range 6).filter
    (fun w => ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i)).erase 0).erase 5
  have hcard : T.card = 2 := majoritySix_internalBinaryPositions_card_two c hcomp hlen
  obtain ⟨p, q, hpq, hT⟩ := Finset.card_eq_two.mp hcard
  have hp : p ∈ T := by rw [hT]; simp
  have hq : q ∈ T := by rw [hT]; simp
  have hp5 : p ≠ 5 := (Finset.mem_erase.mp hp).1
  have hpInner := (Finset.mem_erase.mp hp).2
  have hp0 : p ≠ 0 := (Finset.mem_erase.mp hpInner).1
  have hpBase := (Finset.mem_erase.mp hpInner).2
  have hpFilter := Finset.mem_filter.mp hpBase
  have hp6 : p < 6 := by
    exact Finset.mem_range.mp hpFilter.1
  have hpNonvar := hpFilter.2
  have hq5 : q ≠ 5 := (Finset.mem_erase.mp hq).1
  have hqInner := (Finset.mem_erase.mp hq).2
  have hq0 : q ≠ 0 := (Finset.mem_erase.mp hqInner).1
  have hqBase := (Finset.mem_erase.mp hqInner).2
  have hqFilter := Finset.mem_filter.mp hqBase
  have hq6 : q < 6 := by
    exact Finset.mem_range.mp hqFilter.1
  have hqNonvar := hqFilter.2
  have hexhaust : ∀ w, w < 6 → w ≠ 0 → w ≠ 5 →
      (¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i) → w = p ∨ w = q := by
    intro w hw hw0 hw5 hnvar
    have hwT : w ∈ T := by
      apply Finset.mem_erase.mpr
      refine ⟨hw5, Finset.mem_erase.mpr ⟨hw0, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw, hnvar⟩
    rw [hT] at hwT
    simpa [eq_comm] using hwT
  rcases lt_or_gt_of_ne hpq with hpqlt | hqplt
  · exact ⟨⟨p, q, by omega, hpqlt, by omega, hpNonvar, hqNonvar, hexhaust⟩⟩
  · exact ⟨⟨q, p, by omega, hqplt, by omega, hqNonvar, hpNonvar,
      fun w hw hw0 hw5 hnvar =>
        (hexhaust w hw hw0 hw5 hnvar).elim Or.inr Or.inl⟩⟩

structure SixBinaryGateData (c : List (CGate 3)) extends SixBinaryChronology c where
  op₀ : Bool → Bool → Bool
  j₀ : ℕ
  k₀ : ℕ
  gate₀ : c.getD first (.cst false) = CGate.bin op₀ j₀ k₀
  j₀_lt : j₀ < first
  k₀_lt : k₀ < first
  j₀_ne_k₀ : j₀ ≠ k₀
  op₁ : Bool → Bool → Bool
  j₁ : ℕ
  k₁ : ℕ
  gate₁ : c.getD second (.cst false) = CGate.bin op₁ j₁ k₁
  j₁_lt : j₁ < second
  k₁_lt : k₁ < second
  j₁_ne_k₁ : j₁ ≠ k₁
  op₂ : Bool → Bool → Bool
  j₂ : ℕ
  k₂ : ℕ
  gate₂ : c.getD 5 (.cst false) = CGate.bin op₂ j₂ k₂
  j₂_lt : j₂ < 5
  k₂_lt : k₂ < 5
  j₂_ne_k₂ : j₂ ≠ k₂

open Classical in theorem majoritySix_binaryGateData
    (c : List (CGate 3)) (hcomp : computes c majorityThreeFloor)
    (hlen : c.length = 6) : Nonempty (SixBinaryGateData c) := by
  obtain ⟨chron⟩ := majoritySix_binaryChronology c hcomp hlen
  have hsecond6 : chron.second < 6 :=
    lt_trans chron.second_before_root (by omega)
  have hfirst6 : chron.first < 6 := lt_trans chron.ordered hsecond6
  rcases majoritySix_gate_dichotomy c hcomp hlen chron.first hfirst6 with hvar₀ | hbin₀
  · obtain ⟨i, hi⟩ := hvar₀
    exact False.elim (chron.first_nonvar ⟨i, hi⟩)
  · obtain ⟨op₀, j₀, k₀, gate₀, j₀_lt, k₀_lt, j₀_ne_k₀⟩ := hbin₀
    rcases majoritySix_gate_dichotomy c hcomp hlen chron.second hsecond6 with hvar₁ | hbin₁
    · obtain ⟨i, hi⟩ := hvar₁
      exact False.elim (chron.second_nonvar ⟨i, hi⟩)
    · obtain ⟨op₁, j₁, k₁, gate₁, j₁_lt, k₁_lt, j₁_ne_k₁⟩ := hbin₁
      obtain ⟨op₂, j₂, k₂, gate₂, j₂_lt, k₂_lt, j₂_ne_k₂⟩ :=
        majoritySix_root_is_bin c hcomp hlen
      exact ⟨⟨chron, op₀, j₀, k₀, gate₀, j₀_lt, k₀_lt, j₀_ne_k₀,
        op₁, j₁, k₁, gate₁, j₁_lt, k₁_lt, j₁_ne_k₁,
        op₂, j₂, k₂, gate₂, j₂_lt, k₂_lt, j₂_ne_k₂⟩⟩

theorem majoritySix_source_before_first_is_var (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixBinaryGateData c) {w : ℕ} (hw : w < d.first) :
    ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i := by
  have hw6 : w < 6 := by
    exact lt_trans hw (lt_trans d.ordered (lt_trans d.second_before_root (by omega)))
  rcases majoritySix_gate_dichotomy c hcomp hlen w hw6 with hvar | hbin
  · exact hvar
  · obtain ⟨op, j, k, hg, hj, hk, hjk⟩ := hbin
    have hnvar : ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i := by
      rintro ⟨i, hi⟩
      rw [hg] at hi
      cases hi
    by_cases hw0 : w = 0
    · subst hw0
      omega
    have hfirst5 : d.first < 5 := lt_trans d.ordered d.second_before_root
    have hw5 : w ≠ 5 := Nat.ne_of_lt (lt_trans hw hfirst5)
    rcases d.exhaustive w hw6 hw0 hw5 hnvar with hfirst | hsecond
    · subst w
      exact False.elim ((Nat.lt_irrefl d.first) hw)
    · subst w
      exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt d.ordered)) hw)

theorem majoritySix_source_before_second (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixBinaryGateData c) {w : ℕ} (hw : w < d.second) :
    (∃ i : Fin 3, c.getD w (.cst false) = CGate.var i) ∨ w = d.first := by
  have hw6 : w < 6 := lt_trans hw (lt_trans d.second_before_root (by omega))
  rcases majoritySix_gate_dichotomy c hcomp hlen w hw6 with hvar | hbin
  · exact Or.inl hvar
  · obtain ⟨op, j, k, hg, hj, hk, hjk⟩ := hbin
    have hnvar : ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i := by
      rintro ⟨i, hi⟩
      rw [hg] at hi
      cases hi
    by_cases hw0 : w = 0
    · subst hw0
      omega
    have hw5 : w ≠ 5 := Nat.ne_of_lt (lt_trans hw d.second_before_root)
    rcases d.exhaustive w hw6 hw0 hw5 hnvar with hfirst | hsecond
    · exact Or.inr hfirst
    · subst w
      exact False.elim ((Nat.lt_irrefl d.second) hw)

theorem majoritySix_source_before_root (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixBinaryGateData c) {w : ℕ} (hw : w < 5) :
    (∃ i : Fin 3, c.getD w (.cst false) = CGate.var i) ∨
      w = d.first ∨ w = d.second := by
  have hw6 : w < 6 := lt_trans hw (by omega)
  rcases majoritySix_gate_dichotomy c hcomp hlen w hw6 with hvar | hbin
  · exact Or.inl hvar
  · obtain ⟨op, j, k, hg, hj, hk, hjk⟩ := hbin
    have hnvar : ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i := by
      rintro ⟨i, hi⟩
      rw [hg] at hi
      cases hi
    by_cases hw0 : w = 0
    · subst hw0
      omega
    exact Or.inr (d.exhaustive w hw6 hw0 (by omega) hnvar)

theorem wire_eq_of_var_gate (c : List (CGate 3)) (x : Fin 3 → Bool)
    {p : ℕ} (hp : p < c.length) {i : Fin 3}
    (hg : c.getD p (.cst false) = CGate.var i) : wire c x p = x i := by
  rw [wire_eq c x hp, hg]
  rfl

theorem wire_eq_of_bin_gate (c : List (CGate 3)) (x : Fin 3 → Bool)
    {p j k : ℕ} (hp : p < c.length) (hj : j < p) (hk : k < p)
    {op : Bool → Bool → Bool}
    (hg : c.getD p (.cst false) = CGate.bin op j k) :
    wire c x p = op (wire c x j) (wire c x k) := by
  rw [wire_eq c x hp, hg]
  simp only [evalGate]
  rw [wire_prefix c x hj (le_of_lt hp), wire_prefix c x hk (le_of_lt hp)]

def RepresentsSource4 (c : List (CGate 3)) (d : SixBinaryGateData c)
    (w : ℕ) (s : Fin 4) : Prop :=
  (∃ i : Fin 3, s.val = i.val ∧ c.getD w (.cst false) = CGate.var i) ∨
    (s.val = 3 ∧ w = d.first)

def RepresentsSource5 (c : List (CGate 3)) (d : SixBinaryGateData c)
    (w : ℕ) (s : Fin 5) : Prop :=
  (∃ i : Fin 3, s.val = i.val ∧ c.getD w (.cst false) = CGate.var i) ∨
    (s.val = 3 ∧ w = d.first) ∨ (s.val = 4 ∧ w = d.second)

structure SixCompressedSourceData (c : List (CGate 3)) extends SixBinaryGateData c where
  a₀ : Fin 3
  b₀ : Fin 3
  a₁ : Fin 4
  b₁ : Fin 4
  a₂ : Fin 5
  b₂ : Fin 5
  source_a₀ : ∀ x, sourceThree x a₀ = wire c x j₀
  source_b₀ : ∀ x, sourceThree x b₀ = wire c x k₀
  represents_a₀ : c.getD j₀ (.cst false) = CGate.var a₀
  represents_b₀ : c.getD k₀ (.cst false) = CGate.var b₀
  source_a₁ : ∀ x, sourceFour x (wire c x first) a₁ = wire c x j₁
  source_b₁ : ∀ x, sourceFour x (wire c x first) b₁ = wire c x k₁
  represents_a₁ : RepresentsSource4 c toSixBinaryGateData j₁ a₁
  represents_b₁ : RepresentsSource4 c toSixBinaryGateData k₁ b₁
  source_a₂ : ∀ x, sourceFive x (wire c x first) (wire c x second) a₂ = wire c x j₂
  source_b₂ : ∀ x, sourceFive x (wire c x first) (wire c x second) b₂ = wire c x k₂
  represents_a₂ : RepresentsSource5 c toSixBinaryGateData j₂ a₂
  represents_b₂ : RepresentsSource5 c toSixBinaryGateData k₂ b₂

open Classical in theorem majoritySix_compressedSourceData
    (c : List (CGate 3)) (hcomp : computes c majorityThreeFloor)
    (hlen : c.length = 6) : Nonempty (SixCompressedSourceData c) := by
  obtain ⟨d⟩ := majoritySix_binaryGateData c hcomp hlen
  have hlen6 : ∀ p, p < 6 → p < c.length := by intro p hp; omega
  obtain ⟨a₀, ha₀⟩ := majoritySix_source_before_first_is_var c hcomp hlen d d.j₀_lt
  obtain ⟨b₀, hb₀⟩ := majoritySix_source_before_first_is_var c hcomp hlen d d.k₀_lt
  have hsa₀ : ∀ x, sourceThree x a₀ = wire c x d.j₀ := by
    intro x
    exact (wire_eq_of_var_gate c x (hlen6 _ (lt_trans d.j₀_lt
      (lt_trans d.ordered (lt_trans d.second_before_root (by omega))))) ha₀).symm
  have hsb₀ : ∀ x, sourceThree x b₀ = wire c x d.k₀ := by
    intro x
    exact (wire_eq_of_var_gate c x (hlen6 _ (lt_trans d.k₀_lt
      (lt_trans d.ordered (lt_trans d.second_before_root (by omega))))) hb₀).symm
  have enc4 : ∀ {w}, w < d.second → ∃ s : Fin 4,
      (∀ x, sourceFour x (wire c x d.first) s = wire c x w) ∧
      RepresentsSource4 c d w s := by
    intro w hw
    rcases majoritySix_source_before_second c hcomp hlen d hw with hvar | hfirst
    · obtain ⟨i, hi⟩ := hvar
      refine ⟨⟨i.val, by omega⟩, ?_, Or.inl ⟨i, rfl, hi⟩⟩
      intro x
      simp only [sourceFour, dif_pos i.isLt]
      exact (wire_eq_of_var_gate c x (hlen6 _ (lt_trans hw
        (lt_trans d.second_before_root (by omega)))) hi).symm
    · subst w
      exact ⟨3, by intro x; simp [sourceFour], Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨a₁, hsa₁, hra₁⟩ := enc4 d.j₁_lt
  obtain ⟨b₁, hsb₁, hrb₁⟩ := enc4 d.k₁_lt
  have enc5 : ∀ {w}, w < 5 → ∃ s : Fin 5,
      (∀ x, sourceFive x (wire c x d.first) (wire c x d.second) s = wire c x w) ∧
      RepresentsSource5 c d w s := by
    intro w hw
    rcases majoritySix_source_before_root c hcomp hlen d hw with hvar | hfirst | hsecond
    · obtain ⟨i, hi⟩ := hvar
      refine ⟨⟨i.val, by omega⟩, ?_, Or.inl ⟨i, rfl, hi⟩⟩
      intro x
      simp only [sourceFive, dif_pos i.isLt]
      exact (wire_eq_of_var_gate c x (hlen6 _ (lt_trans hw (by omega))) hi).symm
    · subst w
      exact ⟨3, by intro x; simp [sourceFive], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · subst w
      exact ⟨4, by intro x; simp [sourceFive], Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  obtain ⟨a₂, hsa₂, hra₂⟩ := enc5 d.j₂_lt
  obtain ⟨b₂, hsb₂, hrb₂⟩ := enc5 d.k₂_lt
  exact ⟨⟨d, a₀, b₀, a₁, b₁, a₂, b₂, hsa₀, hsb₀, ha₀, hb₀,
    hsa₁, hsb₁, hra₁, hrb₁, hsa₂, hsb₂, hra₂, hrb₂⟩⟩

theorem majoritySix_read_consumer_position (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixBinaryGateData c) {w j : ℕ} (hw : w < 6)
    (hj : j ∈ gateReads (c.getD w (.cst false))) (_hjw : j < w) :
    w = d.first ∨ w = d.second ∨ w = 5 := by
  rcases majoritySix_gate_dichotomy c hcomp hlen w hw with hvar | hbin
  · obtain ⟨i, hi⟩ := hvar
    rw [hi] at hj
    simp [gateReads] at hj
  · obtain ⟨op, a, b, hg, ha, hb, hab⟩ := hbin
    by_cases hw5 : w = 5
    · exact Or.inr (Or.inr hw5)
    have hnvar : ¬ ∃ i : Fin 3, c.getD w (.cst false) = CGate.var i := by
      rintro ⟨i, hi⟩
      rw [hg] at hi
      cases hi
    have hw0 : w ≠ 0 := by omega
    exact (d.exhaustive w hw hw0 hw5 hnvar).elim Or.inl (fun h => Or.inr (Or.inl h))

theorem majoritySix_cone_wire_has_binary_parent (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixBinaryGateData c) {p : ℕ} (hp : p < 5) (hcone : InCone c p) :
    ∃ w, (w = d.first ∨ w = d.second ∨ w = 5) ∧
      p ∈ gateReads (c.getD w (.cst false)) ∧ p < w := by
  cases hcone with
  | root => omega
  | step hw hread hpw =>
      have hwlen := inCone_lt (by omega) hw
      rw [hlen] at hwlen
      exact ⟨_, majoritySix_read_consumer_position c hcomp hlen d hwlen hread hpw,
        hread, hpw⟩

theorem majoritySix_second_read_by_root (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixBinaryGateData c) : d.j₂ = d.second ∨ d.k₂ = d.second := by
  have hmem : d.second ∈ cone c := by
    rw [majoritySix_cone_all c hcomp hlen, Finset.mem_range]
    exact lt_trans d.second_before_root (by omega)
  obtain ⟨w, hwpos, hread, hlt⟩ := majoritySix_cone_wire_has_binary_parent c hcomp hlen d
    d.second_before_root (mem_cone.mp hmem).2
  rcases hwpos with hfirst | hsecond | hroot
  · subst w
    exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt d.ordered)) hlt)
  · subst w
    exact False.elim ((Nat.lt_irrefl d.second) hlt)
  · subst w
    rw [d.gate₂] at hread
    simpa [gateReads, eq_comm] using hread

theorem majoritySix_first_read_later (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixBinaryGateData c) :
    d.j₁ = d.first ∨ d.k₁ = d.first ∨ d.j₂ = d.first ∨ d.k₂ = d.first := by
  have hmem : d.first ∈ cone c := by
    rw [majoritySix_cone_all c hcomp hlen, Finset.mem_range]
    exact lt_trans d.ordered (lt_trans d.second_before_root (by omega))
  have hfirst5 : d.first < 5 := lt_trans d.ordered d.second_before_root
  obtain ⟨w, hwpos, hread, hlt⟩ := majoritySix_cone_wire_has_binary_parent c hcomp hlen d
    hfirst5 (mem_cone.mp hmem).2
  rcases hwpos with hfirst | hsecond | hroot
  · subst w
    exact False.elim ((Nat.lt_irrefl d.first) hlt)
  · subst w
    rw [d.gate₁] at hread
    have : d.first = d.j₁ ∨ d.first = d.k₁ := by simpa [gateReads] using hread
    exact this.elim (fun h => Or.inl h.symm) (fun h => Or.inr (Or.inl h.symm))
  · subst w
    rw [d.gate₂] at hread
    have : d.first = d.j₂ ∨ d.first = d.k₂ := by simpa [gateReads] using hread
    exact this.elim (fun h => Or.inr (Or.inr (Or.inl h.symm)))
      (fun h => Or.inr (Or.inr (Or.inr h.symm)))

theorem representsSource4_injective (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixBinaryGateData c) {w v : ℕ} {s : Fin 4}
    (hw6 : w < 6) (hv6 : v < 6)
    (hw : RepresentsSource4 c d w s) (hv : RepresentsSource4 c d v s) : w = v := by
  rcases hw with ⟨i, hsi, hwi⟩ | ⟨hs3, hfirst⟩ <;>
    rcases hv with ⟨i', hsi', hvi⟩ | ⟨hs3', hfirst'⟩
  · have hii : i = i' := Fin.ext (hsi.symm.trans hsi')
    subst i'
    exact majoritySix_var_inj c hcomp hlen hw6 hv6 hwi hvi
  · omega
  · omega
  · omega

theorem representsSource5_injective (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixBinaryGateData c) {w v : ℕ} {s : Fin 5}
    (hw6 : w < 6) (hv6 : v < 6)
    (hw : RepresentsSource5 c d w s) (hv : RepresentsSource5 c d v s) : w = v := by
  rcases hw with ⟨i, hsi, hwi⟩ | (⟨hs3, hfirst⟩ | ⟨hs4, hsecond⟩) <;>
    rcases hv with ⟨i', hsi', hvi⟩ | (⟨hs3', hfirst'⟩ | ⟨hs4', hsecond'⟩)
  · have hii : i = i' := Fin.ext (hsi.symm.trans hsi')
    subst i'
    exact majoritySix_var_inj c hcomp hlen hw6 hv6 hwi hvi
  all_goals omega

theorem representsSource4_first_value (c : List (CGate 3))
    (d : SixBinaryGateData c) {w : ℕ} {s : Fin 4}
    (hr : RepresentsSource4 c d w s) (hw : w = d.first) : s.val = 3 := by
  rcases hr with ⟨i, hsi, hgate⟩ | ⟨hs, -⟩
  · subst w
    exact False.elim (d.first_nonvar ⟨i, hgate⟩)
  · exact hs

theorem representsSource5_first_value (c : List (CGate 3))
    (d : SixBinaryGateData c) {w : ℕ} {s : Fin 5}
    (hr : RepresentsSource5 c d w s) (hw : w = d.first) : s.val = 3 := by
  rcases hr with ⟨i, hsi, hgate⟩ | (⟨hs, -⟩ | ⟨hs, hsecond⟩)
  · subst w
    exact False.elim (d.first_nonvar ⟨i, hgate⟩)
  · exact hs
  · exact False.elim ((Nat.ne_of_lt d.ordered) (hw.symm.trans hsecond))

theorem representsSource5_second_value (c : List (CGate 3))
    (d : SixBinaryGateData c) {w : ℕ} {s : Fin 5}
    (hr : RepresentsSource5 c d w s) (hw : w = d.second) : s.val = 4 := by
  rcases hr with ⟨i, hsi, hgate⟩ | (⟨hs, hfirst⟩ | ⟨hs, -⟩)
  · subst w
    exact False.elim (d.second_nonvar ⟨i, hgate⟩)
  · exact False.elim ((Nat.ne_of_lt d.ordered) (hfirst.symm.trans hw))
  · exact hs

theorem majoritySix_compressed_distinct (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixCompressedSourceData c) :
    d.a₀ ≠ d.b₀ ∧ d.a₁ ≠ d.b₁ ∧ d.a₂ ≠ d.b₂ := by
  refine ⟨?_, ?_, ?_⟩
  · intro hab
    have hj06 : d.j₀ < 6 := lt_trans d.j₀_lt
      (lt_trans d.ordered (lt_trans d.second_before_root (by omega)))
    have hk06 : d.k₀ < 6 := lt_trans d.k₀_lt
      (lt_trans d.ordered (lt_trans d.second_before_root (by omega)))
    have hgate : c.getD d.j₀ (.cst false) = CGate.var d.b₀ := by
      rw [← hab]
      exact d.represents_a₀
    exact d.j₀_ne_k₀ (majoritySix_var_inj c hcomp hlen hj06 hk06
      hgate d.represents_b₀)
  · intro hab
    have hj16 : d.j₁ < 6 := lt_trans d.j₁_lt
      (lt_trans d.second_before_root (by omega))
    have hk16 : d.k₁ < 6 := lt_trans d.k₁_lt
      (lt_trans d.second_before_root (by omega))
    have hra := d.represents_a₁
    rw [hab] at hra
    exact d.j₁_ne_k₁ (representsSource4_injective c hcomp hlen d.toSixBinaryGateData
      hj16 hk16 hra d.represents_b₁)
  · intro hab
    have hj26 : d.j₂ < 6 := lt_trans d.j₂_lt (by omega)
    have hk26 : d.k₂ < 6 := lt_trans d.k₂_lt (by omega)
    have hra := d.represents_a₂
    rw [hab] at hra
    exact d.j₂_ne_k₂ (representsSource5_injective c hcomp hlen d.toSixBinaryGateData
      hj26 hk26 hra d.represents_b₂)

theorem majoritySix_compressed_intermediates_seen (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixCompressedSourceData c) :
    (d.a₂.val = 4 ∨ d.b₂.val = 4) ∧
    (d.a₂.val = 3 ∨ d.b₂.val = 3 ∨ d.a₁.val = 3 ∨ d.b₁.val = 3) := by
  constructor
  · rcases majoritySix_second_read_by_root c hcomp hlen d.toSixBinaryGateData with hj | hk
    · exact Or.inl (representsSource5_second_value c d.toSixBinaryGateData
        d.represents_a₂ hj)
    · exact Or.inr (representsSource5_second_value c d.toSixBinaryGateData
        d.represents_b₂ hk)
  · rcases majoritySix_first_read_later c hcomp hlen d.toSixBinaryGateData with
      hj₁ | hk₁ | hj₂ | hk₂
    · exact Or.inr (Or.inr (Or.inl (representsSource4_first_value c
        d.toSixBinaryGateData d.represents_a₁ hj₁)))
    · exact Or.inr (Or.inr (Or.inr (representsSource4_first_value c
        d.toSixBinaryGateData d.represents_b₁ hk₁)))
    · exact Or.inl (representsSource5_first_value c d.toSixBinaryGateData
        d.represents_a₂ hj₂)
    · exact Or.inr (Or.inl (representsSource5_first_value c d.toSixBinaryGateData
        d.represents_b₂ hk₂))

theorem representsSource4_var_value (c : List (CGate 3))
    (d : SixBinaryGateData c) {w : ℕ} {s : Fin 4} {i : Fin 3}
    (hr : RepresentsSource4 c d w s)
    (hg : c.getD w (.cst false) = CGate.var i) : s.val = i.val := by
  rcases hr with ⟨i', hs, hg'⟩ | ⟨hs, hw⟩
  · have : i' = i := CGate.var.inj (hg'.symm.trans hg)
    simpa [this] using hs
  · subst w
    exact False.elim (d.first_nonvar ⟨i, hg⟩)

theorem representsSource5_var_value (c : List (CGate 3))
    (d : SixBinaryGateData c) {w : ℕ} {s : Fin 5} {i : Fin 3}
    (hr : RepresentsSource5 c d w s)
    (hg : c.getD w (.cst false) = CGate.var i) : s.val = i.val := by
  rcases hr with ⟨i', hs, hg'⟩ | (⟨hs, hw⟩ | ⟨hs, hw⟩)
  · have : i' = i := CGate.var.inj (hg'.symm.trans hg)
    simpa [this] using hs
  · subst w
    exact False.elim (d.first_nonvar ⟨i, hg⟩)
  · subst w
    exact False.elim (d.second_nonvar ⟨i, hg⟩)

theorem majoritySix_compressed_inputs_seen (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixCompressedSourceData c) :
    ∀ i : Fin 3, d.a₂.val = i.val ∨ d.b₂.val = i.val ∨
      d.a₁.val = i.val ∨ d.b₁.val = i.val ∨ d.a₀ = i ∨ d.b₀ = i := by
  intro i
  have hi : i ∈ depSet majorityThreeFloor := by
    rw [majorityThreeFloor_depSet]
    exact Finset.mem_univ i
  obtain ⟨p, hpcone, hpgate⟩ := var_position_exists majorityThreeFloor c hcomp
    (by omega) i hi
  have hp6 := (mem_cone.mp hpcone).1
  have hp5 : p < 5 := by
    by_contra h
    have : p = 5 := by omega
    subst p
    rw [d.gate₂] at hpgate
    cases hpgate
  obtain ⟨w, hwpos, hread, hpw⟩ := majoritySix_cone_wire_has_binary_parent
    c hcomp hlen d.toSixBinaryGateData hp5 (mem_cone.mp hpcone).2
  rcases hwpos with hfirst | hsecond | hroot
  · subst w
    rw [d.gate₀] at hread
    have hpjk : p = d.j₀ ∨ p = d.k₀ := by simpa [gateReads] using hread
    rcases hpjk with hpj | hpk
    · have hai : d.a₀ = i := CGate.var.inj (by rw [← d.represents_a₀, ← hpj]; exact hpgate)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hai))))
    · have hbi : d.b₀ = i := CGate.var.inj (by rw [← d.represents_b₀, ← hpk]; exact hpgate)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbi))))
  · subst w
    rw [d.gate₁] at hread
    have hpjk : p = d.j₁ ∨ p = d.k₁ := by simpa [gateReads] using hread
    rcases hpjk with hpj | hpk
    · exact Or.inr (Or.inr (Or.inl (representsSource4_var_value c
        d.toSixBinaryGateData d.represents_a₁ (by rw [← hpj]; exact hpgate))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (representsSource4_var_value c
        d.toSixBinaryGateData d.represents_b₁ (by rw [← hpk]; exact hpgate)))))
  · subst w
    rw [d.gate₂] at hread
    have hpjk : p = d.j₂ ∨ p = d.k₂ := by simpa [gateReads] using hread
    rcases hpjk with hpj | hpk
    · exact Or.inl (representsSource5_var_value c d.toSixBinaryGateData
        d.represents_a₂ (by rw [← hpj]; exact hpgate))
    · exact Or.inr (Or.inl (representsSource5_var_value c d.toSixBinaryGateData
        d.represents_b₂ (by rw [← hpk]; exact hpgate)))

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

theorem majoritySix_compressed_live (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (d : SixCompressedSourceData c) :
    liveThreeTransitionSchedule d.a₀ d.b₀ d.a₁ d.b₁ d.a₂ d.b₂ := by
  obtain ⟨h₀, h₁, h₂⟩ := majoritySix_compressed_distinct c hcomp hlen d
  obtain ⟨hsecond, hfirst⟩ := majoritySix_compressed_intermediates_seen c hcomp hlen d
  refine ⟨h₀, h₁, h₂, hsecond, hfirst, ?_⟩
  intro i
  simpa [scheduleInputSeen] using majoritySix_compressed_inputs_seen c hcomp hlen d i

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

theorem noMajoritySchedule_pairClosed_rootThird_zero :
    NoMajoritySchedule 0 1 3 0 4 2 := by
  rintro ⟨op₀, op₁, op₂, hcomp⟩
  apply majorityThreeFloor_no_split_three
  refine ⟨(fun c z => codedBin op₂ z c),
    (fun a b => codedBin op₁ (codedBin op₀ a b) a), ?_⟩
  intro a b c
  simpa [threeBinaryProgram, sourceThree, sourceFour, sourceFive] using
    (hcomp ![a, b, c]).symm

theorem noMajoritySchedule_pairClosed_rootThird_one :
    NoMajoritySchedule 0 1 3 1 4 2 := by
  rintro ⟨op₀, op₁, op₂, hcomp⟩
  apply majorityThreeFloor_no_split_three
  refine ⟨(fun c z => codedBin op₂ z c),
    (fun a b => codedBin op₁ (codedBin op₀ a b) b), ?_⟩
  intro a b c
  simpa [threeBinaryProgram, sourceThree, sourceFour, sourceFive] using
    (hcomp ![a, b, c]).symm

theorem noMajoritySchedule_pairClosed_rootThird_left
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    NoMajoritySchedule a b 3 (primarySource4 a) 4 (primarySource5 c) := by
  rintro ⟨op₀, op₁, op₂, h⟩
  apply noMajoritySchedule_pairClosed_rootThird_zero
  refine ⟨op₀, op₁, op₂, ?_⟩
  intro y
  let σ := orderedTriplePerm a b c hab hac hbc
  let x := permuteAssignment σ.symm y
  have hp := threeBinaryProgram_permute σ op₀ op₁ op₂ 0 1 3 0 4 2 x
  have hh := h x
  have hmaj := majorityThreeFloor_permute σ.symm y
  simpa [σ, x, permuteAssignment, liftSource4, liftSource5, primarySource4,
    primarySource5] using hp.symm.trans (hh.trans hmaj)

theorem noMajoritySchedule_pairClosed_rootThird_right
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    NoMajoritySchedule a b 3 (primarySource4 b) 4 (primarySource5 c) := by
  rintro ⟨op₀, op₁, op₂, h⟩
  apply noMajoritySchedule_pairClosed_rootThird_one
  refine ⟨op₀, op₁, op₂, ?_⟩
  intro y
  let σ := orderedTriplePerm a b c hab hac hbc
  let x := permuteAssignment σ.symm y
  have hp := threeBinaryProgram_permute σ op₀ op₁ op₂ 0 1 3 1 4 2 x
  have hh := h x
  have hmaj := majorityThreeFloor_permute σ.symm y
  simpa [σ, x, permuteAssignment, liftSource4, liftSource5, primarySource4,
    primarySource5] using hp.symm.trans (hh.trans hmaj)


set_option maxHeartbeats 1000000 in
theorem liveSchedule_0_1_noMajority
    (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5)
    (hlive : liveThreeTransitionSchedule 0 1 a₁ b₁ a₂ b₂) :
    NoMajoritySchedule 0 1 a₁ b₁ a₂ b₂ := by
  fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂
  all_goals first
  | exfalso; revert hlive; decide
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_parallel 0 1 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 0 1 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_left 0 1 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 0 1 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 1 0 2 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 1 0 2 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_right 0 1 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 0 1 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 0 1 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 0 1 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 1 0 2 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_parallel 1 0 2 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 0 1 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_chain_pairInput 1 0 2 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_thirdInput 0 1 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_firstResult 0 1 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 0 1 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 1 0 2 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 0 1 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 0 1 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 0 1 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_left 0 1 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 0 1 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_right 0 1 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 0 1 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 1 0 2 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 0 1 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 0 1 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_pairInput 0 1 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 1 0 2 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_thirdInput 0 1 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_firstResult 0 1 2 (by decide) (by decide) (by decide)

set_option maxHeartbeats 1000000 in
theorem liveSchedule_0_2_noMajority
    (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5)
    (hlive : liveThreeTransitionSchedule 0 2 a₁ b₁ a₂ b₂) :
    NoMajoritySchedule 0 2 a₁ b₁ a₂ b₂ := by
  fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂
  all_goals first
  | exfalso; revert hlive; decide
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_parallel 0 2 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 0 2 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_left 0 2 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 0 2 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 0 2 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 0 2 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 2 0 1 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_parallel 2 0 1 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 0 2 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_thirdInput 0 2 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_chain_pairInput 2 0 1 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_firstResult 0 2 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 0 2 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 0 2 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 2 0 1 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 0 2 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 2 0 1 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 2 0 1 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_right 0 2 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 0 2 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 0 2 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_left 0 2 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 0 2 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 0 2 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 2 0 1 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 0 2 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_pairInput 0 2 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_thirdInput 0 2 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 2 0 1 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_firstResult 0 2 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 0 2 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_right 0 2 1 (by decide) (by decide) (by decide)

set_option maxHeartbeats 1000000 in
theorem liveSchedule_1_0_noMajority
    (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5)
    (hlive : liveThreeTransitionSchedule 1 0 a₁ b₁ a₂ b₂) :
    NoMajoritySchedule 1 0 a₁ b₁ a₂ b₂ := by
  fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂
  all_goals first
  | exfalso; revert hlive; decide
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 0 1 2 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 0 1 2 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_right 1 0 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 1 0 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_parallel 1 0 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 1 0 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_left 1 0 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 1 0 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 0 1 2 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_parallel 0 1 2 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 1 0 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 1 0 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_chain_pairInput 0 1 2 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 1 0 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_thirdInput 1 0 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_firstResult 1 0 2 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 0 1 2 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 1 0 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 1 0 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 1 0 2 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 1 0 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_right 1 0 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 1 0 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_left 1 0 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 0 1 2 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 1 0 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 1 0 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 1 0 2 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 0 1 2 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_pairInput 1 0 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_thirdInput 1 0 2 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_firstResult 1 0 2 (by decide) (by decide) (by decide)

set_option maxHeartbeats 1000000 in
theorem liveSchedule_1_2_noMajority
    (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5)
    (hlive : liveThreeTransitionSchedule 1 2 a₁ b₁ a₂ b₂) :
    NoMajoritySchedule 1 2 a₁ b₁ a₂ b₂ := by
  fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂
  all_goals first
  | exfalso; revert hlive; decide
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 1 2 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 1 2 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 2 1 0 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_parallel 2 1 0 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_thirdInput 1 2 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 1 2 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_chain_pairInput 2 1 0 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_firstResult 1 2 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 1 2 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 1 2 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 2 1 0 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 1 2 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_parallel 1 2 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 1 2 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_left 1 2 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 1 2 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 2 1 0 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 2 1 0 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_right 1 2 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 1 2 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 1 2 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 1 2 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 2 1 0 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 1 2 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_thirdInput 1 2 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_pairInput 1 2 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 2 1 0 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_firstResult 1 2 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 1 2 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_left 1 2 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 1 2 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_right 1 2 0 (by decide) (by decide) (by decide)

set_option maxHeartbeats 1000000 in
theorem liveSchedule_2_0_noMajority
    (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5)
    (hlive : liveThreeTransitionSchedule 2 0 a₁ b₁ a₂ b₂) :
    NoMajoritySchedule 2 0 a₁ b₁ a₂ b₂ := by
  fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂
  all_goals first
  | exfalso; revert hlive; decide
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 0 2 1 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 0 2 1 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_right 2 0 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 2 0 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 0 2 1 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_parallel 0 2 1 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 2 0 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 2 0 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_chain_pairInput 0 2 1 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_thirdInput 2 0 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 2 0 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_firstResult 2 0 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 0 2 1 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 2 0 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 2 0 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 2 0 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_parallel 2 0 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 2 0 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_left 2 0 1 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 2 0 1 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 2 0 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_right 2 0 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 0 2 1 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 2 0 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 2 0 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 2 0 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 0 2 1 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_thirdInput 2 0 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_pairInput 2 0 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_firstResult 2 0 1 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 2 0 1 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_left 2 0 1 (by decide) (by decide) (by decide)

set_option maxHeartbeats 1000000 in
theorem liveSchedule_2_1_noMajority
    (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5)
    (hlive : liveThreeTransitionSchedule 2 1 a₁ b₁ a₂ b₂) :
    NoMajoritySchedule 2 1 a₁ b₁ a₂ b₂ := by
  fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂
  all_goals first
  | exfalso; revert hlive; decide
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 1 2 0 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_parallel 1 2 0 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 2 1 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 2 1 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_thirdInput 2 1 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (((noMajoritySchedule_chain_pairInput 1 2 0 (by decide) (by decide) (by decide)).reverse_first).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 2 1 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_firstResult 2 1 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 2 1 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 1 2 0 (by decide) (by decide) (by decide)).reverse_first).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 2 1 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 2 1 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 1 2 0 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_parallel 1 2 0 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_right 2 1 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 2 1 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_parallel 2 1 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_parallel 2 1 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_pairClosed_rootThird_left 2 1 0 (by decide) (by decide) (by decide)).reverse_second).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 2 1 0 (by decide) (by decide) (by decide)).reverse_second
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_thirdInput 2 1 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using ((noMajoritySchedule_chain_pairInput 1 2 0 (by decide) (by decide) (by decide)).reverse_first).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 2 1 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_firstResult 2 1 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_thirdInput 2 1 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_chain_pairInput 1 2 0 (by decide) (by decide) (by decide)).reverse_first
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_pairInput 2 1 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_chain_firstResult 2 1 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_right 2 1 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_right 2 1 0 (by decide) (by decide) (by decide)
  | simpa [primarySource4, primarySource5] using (noMajoritySchedule_pairClosed_rootThird_left 2 1 0 (by decide) (by decide) (by decide)).reverse_root
  | simpa [primarySource4, primarySource5] using noMajoritySchedule_pairClosed_rootThird_left 2 1 0 (by decide) (by decide) (by decide)

theorem liveThreeTransitionSchedule_noMajority
    (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4) (a₂ b₂ : Fin 5)
    (hlive : liveThreeTransitionSchedule a₀ b₀ a₁ b₁ a₂ b₂) :
    NoMajoritySchedule a₀ b₀ a₁ b₁ a₂ b₂ := by
  fin_cases a₀ <;> fin_cases b₀
  all_goals first
  | exact (hlive.1 rfl).elim
  | exact liveSchedule_0_1_noMajority a₁ b₁ a₂ b₂ hlive
  | exact liveSchedule_0_2_noMajority a₁ b₁ a₂ b₂ hlive
  | exact liveSchedule_1_0_noMajority a₁ b₁ a₂ b₂ hlive
  | exact liveSchedule_1_2_noMajority a₁ b₁ a₂ b₂ hlive
  | exact liveSchedule_2_0_noMajority a₁ b₁ a₂ b₂ hlive
  | exact liveSchedule_2_1_noMajority a₁ b₁ a₂ b₂ hlive

theorem liveThreeTransition_semantic_exclusion :
    ¬ ∃ (op₀ op₁ op₂ : Fin 16) (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
        (a₂ b₂ : Fin 5),
      liveThreeTransitionSchedule a₀ b₀ a₁ b₁ a₂ b₂ ∧
      ∀ x : Fin 3 → Bool,
        threeBinaryProgram op₀ op₁ op₂ a₀ b₀ a₁ b₁ a₂ b₂ x =
          majorityThreeFloor x := by
  rintro ⟨op₀, op₁, op₂, a₀, b₀, a₁, b₁, a₂, b₂, hlive, hcomp⟩
  exact liveThreeTransitionSchedule_noMajority a₀ b₀ a₁ b₁ a₂ b₂ hlive
    ⟨op₀, op₁, op₂, hcomp⟩

theorem majoritySix_compressed_realizes (c : List (CGate 3))
    (hlen : c.length = 6) (d : SixCompressedSourceData c)
    (x : Fin 3 → Bool) :
    threeBinaryProgram (codeBooleanBinary d.op₀) (codeBooleanBinary d.op₁)
      (codeBooleanBinary d.op₂) d.a₀ d.b₀ d.a₁ d.b₁ d.a₂ d.b₂ x = output c x := by
  have hsecond6 : d.second < c.length := by
    rw [hlen]
    exact lt_trans d.second_before_root (by omega)
  have hfirst6 : d.first < c.length := lt_trans d.ordered hsecond6
  have hroot6 : 5 < c.length := by omega
  have hfirst := wire_eq_of_bin_gate c x hfirst6 d.j₀_lt d.k₀_lt d.gate₀
  have hsecond := wire_eq_of_bin_gate c x hsecond6 d.j₁_lt d.k₁_lt d.gate₁
  have hroot := wire_eq_of_bin_gate c x hroot6 d.j₂_lt d.k₂_lt d.gate₂
  rw [output_eq_wire, hlen]
  unfold threeBinaryProgram
  simp only [codedBin_codeBooleanBinary]
  rw [d.source_a₀, d.source_b₀, ← hfirst]
  rw [d.source_a₁, d.source_b₁, ← hsecond]
  rw [d.source_a₂, d.source_b₂, ← hroot]

/-- The concrete transport object from a six-wire `CGate` circuit into the
semantic observer trajectory. -/
structure SixCircuitSemanticScheduleCertificate (c : List (CGate 3)) where
  op₀ : Fin 16
  op₁ : Fin 16
  op₂ : Fin 16
  a₀ : Fin 3
  b₀ : Fin 3
  a₁ : Fin 4
  b₁ : Fin 4
  a₂ : Fin 5
  b₂ : Fin 5
  live : liveThreeTransitionSchedule a₀ b₀ a₁ b₁ a₂ b₂
  realizes : ∀ x : Fin 3 → Bool,
    threeBinaryProgram op₀ op₁ op₂ a₀ b₀ a₁ b₁ a₂ b₂ x = output c x

theorem no_sixCircuitSemanticScheduleCertificate
    (c : List (CGate 3)) (hcomp : computes c majorityThreeFloor) :
    ¬ Nonempty (SixCircuitSemanticScheduleCertificate c) := by
  rintro ⟨cert⟩
  apply liveThreeTransition_semantic_exclusion
  exact ⟨cert.op₀, cert.op₁, cert.op₂, cert.a₀, cert.b₀, cert.a₁, cert.b₁,
    cert.a₂, cert.b₂, cert.live, fun x => (cert.realizes x).trans (hcomp x)⟩

/-- The sole remaining circuit-to-boundary transport obligation. -/
def MajoritySixSemanticScheduleExtractor : Prop :=
  ∀ (c : List (CGate 3)), computes c majorityThreeFloor → c.length = 6 →
    Nonempty (SixCircuitSemanticScheduleCertificate c)

theorem majorityThreeFloor_cbudget_eq_seven_of_semanticScheduleExtractor
    (hextract : MajoritySixSemanticScheduleExtractor) :
    cbudget majorityThreeFloor = 7 := by
  have hlo := majorityThreeFloor_cbudget_lower
  have hhi := majorityThreeFloor_cbudget_upper
  by_contra hne
  have hbudget : cbudget majorityThreeFloor = 6 := by omega
  obtain ⟨c, hcomp, hclen⟩ :=
    Nat.sInf_mem (cbudget_set_nonempty majorityThreeFloor)
  have hlen : c.length = 6 := hclen.trans hbudget
  exact no_sixCircuitSemanticScheduleCertificate c hcomp
    (hextract c hcomp hlen)

theorem majoritySixSemanticScheduleExtractor_proved :
    MajoritySixSemanticScheduleExtractor := by
  intro c hcomp hlen
  obtain ⟨d⟩ := majoritySix_compressedSourceData c hcomp hlen
  exact ⟨{
    op₀ := codeBooleanBinary d.op₀
    op₁ := codeBooleanBinary d.op₁
    op₂ := codeBooleanBinary d.op₂
    a₀ := d.a₀
    b₀ := d.b₀
    a₁ := d.a₁
    b₁ := d.b₁
    a₂ := d.a₂
    b₂ := d.b₂
    live := majoritySix_compressed_live c hcomp hlen d
    realizes := majoritySix_compressed_realizes c hlen d
  }⟩

/-- Exact kernel-certified circuit budget of three-bit majority. -/
theorem majorityThreeFloor_cbudget_eq_seven :
    cbudget majorityThreeFloor = 7 :=
  majorityThreeFloor_cbudget_eq_seven_of_semanticScheduleExtractor
    majoritySixSemanticScheduleExtractor_proved


/- The semantic heart of the dynamic-boundary argument: no trajectory of
three arbitrary binary transitions from the three coordinate observers has
majority as its final exposed wire. -/
end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.liveThreeTransition_semantic_exclusion
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majorityThreeFloor_cbudget_eq_seven
