import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade
import Mathlib.Tactic

/-!
# Explicit binary addition using the existing Boolean circuit gates

Each bit of this ripple adder emits five binary gates and shares its XOR
intermediate. Input and output words are lists of absolute wire indices in
little-endian order. The final carry is retained, so the arithmetic theorem
is exact natural-number addition and needs no overflow assumption.
-/

namespace GodMoveBinaryAdder

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

def wordValue (vals : List Bool) : List ℕ → ℕ
  | [] => 0
  | i :: is => (vals.getD i false).toNat + 2 * wordValue vals is

def sumBit (a b carry : Bool) : Bool := (a ^^ b) ^^ carry

def carryBit (a b carry : Bool) : Bool := (a && b) || ((a ^^ b) && carry)

theorem fullAdder_arithmetic (a b carry : Bool) :
    (sumBit a b carry).toNat + 2 * (carryBit a b carry).toNat =
      a.toNat + b.toNat + carry.toNat := by
  cases a <;> cases b <;> cases carry <;> decide

def fullAdder {n : ℕ} (start x y carry : ℕ) : List (CGate n) :=
  [.bin Bool.xor x y,
   .bin Bool.and x y,
   .bin Bool.xor start carry,
   .bin Bool.and start carry,
   .bin Bool.or (start + 1) (start + 3)]

@[simp] theorem fullAdder_length {n : ℕ} (start x y carry : ℕ) :
    (fullAdder (n := n) start x y carry).length = 5 := rfl

theorem runFrom_length {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (c : List (CGate n)) : (runFrom a vals c).length = vals.length + c.length := by
  induction c generalizing vals with
  | nil => simp [runFrom]
  | cons g gs ih => simp [runFrom, ih, Nat.add_assoc, Nat.add_comm]

theorem runFrom_extends {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (c : List (CGate n)) : ∃ extra, runFrom a vals c = vals ++ extra := by
  induction c generalizing vals with
  | nil => exact ⟨[], by simp [runFrom]⟩
  | cons g gs ih =>
      obtain ⟨extra, he⟩ := ih (vals ++ [evalGate a vals g])
      exact ⟨evalGate a vals g :: extra, by simpa [runFrom, List.append_assoc] using he⟩

theorem read_runFrom_old {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (c : List (CGate n)) (i : ℕ) (hi : i < vals.length) :
    (runFrom a vals c).getD i false = vals.getD i false := by
  obtain ⟨extra, he⟩ := runFrom_extends a vals c
  rw [he]
  exact List.getD_append _ _ _ _ hi

theorem wordValue_runFrom_old {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (c : List (CGate n)) (word : List ℕ) (hword : ∀ i ∈ word, i < vals.length) :
    wordValue (runFrom a vals c) word = wordValue vals word := by
  induction word with
  | nil => rfl
  | cons i is ih =>
      simp only [wordValue]
      rw [read_runFrom_old a vals c i (hword i (by simp)), ih]
      exact fun j hj => hword j (by simp [hj])

theorem read_append_new (vals more : List Bool) (k : ℕ) :
    (vals ++ more).getD (vals.length + k) false = more.getD k false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem read_append_start (vals more : List Bool) :
    (vals ++ more).getD vals.length false = more.getD 0 false := by
  simpa using read_append_new vals more 0

theorem runFrom_fullAdder {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y carry : ℕ) (hx : x < vals.length) (hy : y < vals.length)
    (hc : carry < vals.length) :
    runFrom a vals (fullAdder vals.length x y carry) = vals ++
      [vals.getD x false ^^ vals.getD y false,
       vals.getD x false && vals.getD y false,
       sumBit (vals.getD x false) (vals.getD y false) (vals.getD carry false),
       (vals.getD x false ^^ vals.getD y false) && vals.getD carry false,
       carryBit (vals.getD x false) (vals.getD y false) (vals.getD carry false)] := by
  have hreadx (more : List Bool) : (vals ++ more).getD x false = vals.getD x false :=
    List.getD_append _ _ _ _ hx
  have hready (more : List Bool) : (vals ++ more).getD y false = vals.getD y false :=
    List.getD_append _ _ _ _ hy
  have hreadc (more : List Bool) : (vals ++ more).getD carry false = vals.getD carry false :=
    List.getD_append _ _ _ _ hc
  simp only [fullAdder, runFrom, evalGate, List.append_assoc, List.cons_append, List.nil_append,
    sumBit, carryBit, hreadx, hready, hreadc, read_append_new, read_append_start,
    List.getD_cons_zero, List.getD_cons_succ]

/-- Paired input references permit independent reuse of either input word. -/
def addBits {n : ℕ} (start : ℕ) : List (ℕ × ℕ) → ℕ → List (CGate n) × List ℕ
  | [], carry => ([], [carry])
  | (x, y) :: rest, carry =>
      let next := addBits (start + 5) rest (start + 4)
      (fullAdder start x y carry ++ next.1, (start + 2) :: next.2)

theorem addBits_gate_count {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) (carry : ℕ) :
    (addBits (n := n) start pairs carry).1.length = 5 * pairs.length := by
  induction pairs generalizing start carry with
  | nil => simp [addBits]
  | cons p ps ih => simp [addBits, ih, Nat.mul_add, Nat.add_comm]

theorem addBits_word_length {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) (carry : ℕ) :
    (addBits (n := n) start pairs carry).2.length = pairs.length + 1 := by
  induction pairs generalizing start carry with
  | nil => simp [addBits]
  | cons p ps ih => simp [addBits, ih, Nat.add_assoc]

theorem addBits_refs_lt {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) (carry : ℕ)
    (hc : carry < start) :
    ∀ i ∈ (addBits (n := n) start pairs carry).2, i < start + 5 * pairs.length := by
  induction pairs generalizing start carry with
  | nil => simpa [addBits] using hc
  | cons p ps ih =>
      intro i hi
      simp only [addBits, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp only [List.length_cons]; omega
      · have h := ih (start + 5) (start + 4) (by omega) i hi
        simp only [List.length_cons]
        omega

/-- Exact addition, including the final carry, for any current wire values.
The two input words can share references arbitrarily. -/
theorem addBits_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (pairs : List (ℕ × ℕ)) (carry : ℕ)
    (hpairs : ∀ p ∈ pairs, p.1 < vals.length ∧ p.2 < vals.length)
    (hc : carry < vals.length) :
    wordValue (runFrom a vals (addBits vals.length pairs carry).1)
      (addBits (n := n) vals.length pairs carry).2 =
      wordValue vals (pairs.map Prod.fst) + wordValue vals (pairs.map Prod.snd) +
        (vals.getD carry false).toNat := by
  induction pairs generalizing vals carry with
  | nil => simp [addBits, runFrom, wordValue]
  | cons p ps ih =>
      obtain ⟨hx, hy⟩ := hpairs p (by simp)
      have hps : ∀ q ∈ ps, q.1 < vals.length ∧ q.2 < vals.length :=
        fun q hq => hpairs q (by simp [hq])
      let nextVals := runFrom a vals (fullAdder vals.length p.1 p.2 carry)
      have hlen : nextVals.length = vals.length + 5 := by
        simp only [nextVals, runFrom_length, fullAdder_length]
      have hnext : ∀ q ∈ ps, q.1 < nextVals.length ∧ q.2 < nextVals.length := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := hps q hq
        rw [hlen]
        constructor <;> omega
      have ht := ih nextVals (vals.length + 4) hnext (by rw [hlen]; omega)
      rw [hlen] at ht
      have hsum : nextVals.getD (vals.length + 2) false =
          sumBit (vals.getD p.1 false) (vals.getD p.2 false) (vals.getD carry false) := by
        dsimp only [nextVals]
        rw [runFrom_fullAdder a vals p.1 p.2 carry hx hy hc]
        simp only [read_append_new, List.getD_cons_succ, List.getD_cons_zero]
      have hcarry : nextVals.getD (vals.length + 4) false =
          carryBit (vals.getD p.1 false) (vals.getD p.2 false) (vals.getD carry false) := by
        dsimp only [nextVals]
        rw [runFrom_fullAdder a vals p.1 p.2 carry hx hy hc]
        simp only [read_append_new, List.getD_cons_succ, List.getD_cons_zero]
      have hfst : wordValue nextVals (ps.map Prod.fst) = wordValue vals (ps.map Prod.fst) := by
        apply wordValue_runFrom_old
        intro i hi
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
        exact (hps q hq).1
      have hsnd : wordValue nextVals (ps.map Prod.snd) = wordValue vals (ps.map Prod.snd) := by
        apply wordValue_runFrom_old
        intro i hi
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
        exact (hps q hq).2
      simp only [addBits, runFrom_append, List.map_cons, wordValue]
      change ((runFrom a nextVals (addBits (n := n) (vals.length + 5) ps
          (vals.length + 4)).1).getD (vals.length + 2) false).toNat +
        2 * wordValue (runFrom a nextVals (addBits (n := n) (vals.length + 5) ps
          (vals.length + 4)).1) (addBits (n := n) (vals.length + 5) ps (vals.length + 4)).2 = _
      rw [read_runFrom_old a nextVals _ _ (by rw [hlen]; omega), ht, hsum, hcarry, hfst, hsnd]
      have harith := fullAdder_arithmetic
        (vals.getD p.1 false) (vals.getD p.2 false) (vals.getD carry false)
      omega

theorem binary_ne (a b : Bool) (x y : ℕ) :
    decide (a.toNat + 2 * x ≠ b.toNat + 2 * y) = ((a ^^ b) || decide (x ≠ y)) := by
  cases a <;> cases b <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

def differentBitsFrom {n : ℕ} (start : ℕ) :
    List (ℕ × ℕ) → ℕ → List (CGate n) × ℕ
  | [], acc => ([], acc)
  | (x, y) :: rest, acc =>
      let next := differentBitsFrom (start + 2) rest (start + 1)
      ([.bin Bool.xor x y, .bin Bool.or start acc] ++ next.1, next.2)

/-- Test whether two equal-width words differ, with a fresh false accumulator. -/
def differentBits {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) : List (CGate n) × ℕ :=
  let next := differentBitsFrom (start + 1) pairs start
  (.cst false :: next.1, next.2)

theorem differentBitsFrom_gate_count {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) (acc : ℕ) :
    (differentBitsFrom (n := n) start pairs acc).1.length = 2 * pairs.length := by
  induction pairs generalizing start acc with
  | nil => simp [differentBitsFrom]
  | cons p ps ih =>
      simp only [differentBitsFrom, List.length_append, List.length_cons, List.length_nil, ih]
      omega

theorem differentBits_gate_count {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) :
    (differentBits (n := n) start pairs).1.length = 2 * pairs.length + 1 := by
  simp [differentBits, differentBitsFrom_gate_count]

theorem differentBitsFrom_ref_lt {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) (acc : ℕ)
    (ha : acc < start) :
    (differentBitsFrom (n := n) start pairs acc).2 < start + 2 * pairs.length := by
  induction pairs generalizing start acc with
  | nil => simpa [differentBitsFrom] using ha
  | cons p ps ih =>
      have h := ih (start + 2) (start + 1) (by omega)
      simpa [differentBitsFrom, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using h

theorem differentBits_ref_lt {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) :
    (differentBits (n := n) start pairs).2 < start + (differentBits (n := n) start pairs).1.length := by
  have h := differentBitsFrom_ref_lt (n := n) (start + 1) pairs start (by omega)
  simpa [differentBits, differentBitsFrom_gate_count, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using h

theorem runFrom_differentBit {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y acc : ℕ) (_hx : x < vals.length) (_hy : y < vals.length)
    (hc : acc < vals.length) :
    runFrom a vals ([.bin Bool.xor x y, .bin Bool.or vals.length acc] : List (CGate n)) =
      vals ++ [vals.getD x false ^^ vals.getD y false,
        (vals.getD x false ^^ vals.getD y false) || vals.getD acc false] := by
  have hread (more : List Bool) : (vals ++ more).getD acc false = vals.getD acc false :=
    List.getD_append _ _ _ _ hc
  simp only [runFrom, evalGate, List.append_assoc, List.cons_append, List.nil_append,
    hread, read_append_start, List.getD_cons_zero]

theorem differentBitsFrom_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (pairs : List (ℕ × ℕ)) (acc : ℕ)
    (hpairs : ∀ p ∈ pairs, p.1 < vals.length ∧ p.2 < vals.length)
    (hc : acc < vals.length) :
    (runFrom a vals (differentBitsFrom vals.length pairs acc).1).getD
      (differentBitsFrom (n := n) vals.length pairs acc).2 false =
      (vals.getD acc false ||
        decide (wordValue vals (pairs.map Prod.fst) ≠ wordValue vals (pairs.map Prod.snd))) := by
  induction pairs generalizing vals acc with
  | nil => simp [differentBitsFrom, runFrom, wordValue]
  | cons p ps ih =>
      obtain ⟨hx, hy⟩ := hpairs p (by simp)
      have hps : ∀ q ∈ ps, q.1 < vals.length ∧ q.2 < vals.length :=
        fun q hq => hpairs q (by simp [hq])
      let gates : List (CGate n) := [.bin Bool.xor p.1 p.2, .bin Bool.or vals.length acc]
      let nextVals := runFrom a vals gates
      have hlen : nextVals.length = vals.length + 2 := by
        simp [nextVals, runFrom_length, gates]
      have hnext : ∀ q ∈ ps, q.1 < nextVals.length ∧ q.2 < nextVals.length := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := hps q hq
        rw [hlen]
        constructor <;> omega
      have ht := ih nextVals (vals.length + 1) hnext (by rw [hlen]; omega)
      rw [hlen] at ht
      have hacc : nextVals.getD (vals.length + 1) false =
          ((vals.getD p.1 false ^^ vals.getD p.2 false) || vals.getD acc false) := by
        dsimp only [nextVals, gates]
        rw [runFrom_differentBit a vals p.1 p.2 acc hx hy hc]
        simp only [read_append_new, List.getD_cons_succ, List.getD_cons_zero]
      have hfst : wordValue nextVals (ps.map Prod.fst) = wordValue vals (ps.map Prod.fst) := by
        apply wordValue_runFrom_old
        intro i hi
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
        exact (hps q hq).1
      have hsnd : wordValue nextVals (ps.map Prod.snd) = wordValue vals (ps.map Prod.snd) := by
        apply wordValue_runFrom_old
        intro i hi
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
        exact (hps q hq).2
      simp only [differentBitsFrom, runFrom_append, List.map_cons, wordValue]
      change (runFrom a nextVals (differentBitsFrom (n := n) (vals.length + 2) ps
        (vals.length + 1)).1).getD (differentBitsFrom (n := n) (vals.length + 2) ps
        (vals.length + 1)).2 false = _
      rw [ht, hacc, hfst, hsnd, binary_ne]
      simp [Bool.or_assoc, Bool.or_comm]

/-- The comparator exactly detects inequality of the two natural-number
values represented by its paired input words. -/
theorem differentBits_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (pairs : List (ℕ × ℕ))
    (hpairs : ∀ p ∈ pairs, p.1 < vals.length ∧ p.2 < vals.length) :
    (runFrom a vals (differentBits vals.length pairs).1).getD
      (differentBits (n := n) vals.length pairs).2 false =
      decide (wordValue vals (pairs.map Prod.fst) ≠ wordValue vals (pairs.map Prod.snd)) := by
  let nextVals := vals ++ [false]
  have hlen : nextVals.length = vals.length + 1 := by simp [nextVals]
  have hnext : ∀ p ∈ pairs, p.1 < nextVals.length ∧ p.2 < nextVals.length := by
    intro p hp
    obtain ⟨h1, h2⟩ := hpairs p hp
    rw [hlen]
    constructor <;> omega
  have h := differentBitsFrom_spec a nextVals pairs vals.length hnext (by rw [hlen]; omega)
  rw [hlen] at h
  have hfalse : nextVals.getD vals.length false = false := by
    simp only [nextVals, read_append_start, List.getD_cons_zero]
  have hfst : wordValue nextVals (pairs.map Prod.fst) = wordValue vals (pairs.map Prod.fst) := by
    apply wordValue_runFrom_old a vals [.cst false]
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    exact (hpairs p hp).1
  have hsnd : wordValue nextVals (pairs.map Prod.snd) = wordValue vals (pairs.map Prod.snd) := by
    apply wordValue_runFrom_old a vals [.cst false]
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    exact (hpairs p hp).2
  simpa only [differentBits, runFrom, evalGate, hfalse, hfst, hsnd, Bool.false_or] using h

end GodMoveBinaryAdder

#print axioms GodMoveBinaryAdder.fullAdder_arithmetic
#print axioms GodMoveBinaryAdder.runFrom_fullAdder
#print axioms GodMoveBinaryAdder.addBits_gate_count
#print axioms GodMoveBinaryAdder.addBits_word_length
#print axioms GodMoveBinaryAdder.addBits_refs_lt
#print axioms GodMoveBinaryAdder.addBits_spec
#print axioms GodMoveBinaryAdder.differentBits_gate_count
#print axioms GodMoveBinaryAdder.differentBits_ref_lt
#print axioms GodMoveBinaryAdder.differentBits_spec
