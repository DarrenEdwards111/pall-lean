import GodMoveBinaryAdder

/-!
# Binary subtraction with a derived Boolean-gate cost

Each bit complements the subtrahend and incoming borrow, uses the existing
five-gate full adder, and complements the outgoing carry. The emitted circuit
therefore has exactly eight gates per bit. The final borrow detects ordering,
and the numerical identity retains the complete underflow information.

This is an explicit binary backend primitive. It has not been substituted into
the rational builder, and it does not measure Lean's external integer runtime,
circuit construction, wire lookup, or allocation.
-/

namespace GodMoveBinarySubtract

open GodMoveBinaryAdder
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

def differenceBit (a b borrow : Bool) : Bool := sumBit a (!b) (!borrow)

def borrowBit (a b borrow : Bool) : Bool := !(carryBit a (!b) (!borrow))

theorem fullSubtract_arithmetic (a b borrow : Bool) :
    (differenceBit a b borrow).toNat + b.toNat + borrow.toNat =
      a.toNat + 2 * (borrowBit a b borrow).toNat := by
  cases a <;> cases b <;> cases borrow <;> decide

def fullSubtract {n : ℕ} (start x y borrow : ℕ) : List (CGate n) :=
  [.un Bool.not y, .un Bool.not borrow] ++
    fullAdder (start + 2) x start (start + 1) ++ [.un Bool.not (start + 6)]

@[simp] theorem fullSubtract_length {n : ℕ} (start x y borrow : ℕ) :
    (fullSubtract (n := n) start x y borrow).length = 8 := rfl

theorem runFrom_fullSubtract {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y borrow : ℕ) (hx : x < vals.length) (_hy : y < vals.length)
    (hb : borrow < vals.length) :
    runFrom a vals (fullSubtract vals.length x y borrow) = vals ++
      [!vals.getD y false, !vals.getD borrow false,
       vals.getD x false ^^ !vals.getD y false,
       vals.getD x false && !vals.getD y false,
       differenceBit (vals.getD x false) (vals.getD y false) (vals.getD borrow false),
       (vals.getD x false ^^ !vals.getD y false) && !vals.getD borrow false,
       carryBit (vals.getD x false) (!vals.getD y false) (!vals.getD borrow false),
       borrowBit (vals.getD x false) (vals.getD y false) (vals.getD borrow false)] := by
  have hreadx (more : List Bool) : (vals ++ more).getD x false = vals.getD x false :=
    List.getD_append _ _ _ _ hx
  have hreadb (more : List Bool) : (vals ++ more).getD borrow false = vals.getD borrow false :=
    List.getD_append _ _ _ _ hb
  simp only [fullSubtract, fullAdder, runFrom, evalGate, List.append_assoc,
    List.cons_append, List.nil_append, differenceBit, borrowBit, sumBit, carryBit,
    hreadx, hreadb, Nat.add_assoc, read_append_new, read_append_start,
    List.getD_cons_zero, List.getD_cons_succ]

/-- The output pair contains the little-endian difference word and final borrow.
Both input words may share references with each other or with the borrow input. -/
def subtractBits {n : ℕ} (start : ℕ) :
    List (ℕ × ℕ) → ℕ → List (CGate n) × (List ℕ × ℕ)
  | [], borrow => ([], ([], borrow))
  | (x, y) :: rest, borrow =>
      let next := subtractBits (start + 8) rest (start + 7)
      (fullSubtract start x y borrow ++ next.1, ((start + 4) :: next.2.1, next.2.2))

theorem subtractBits_gate_count {n : ℕ} (start : ℕ)
    (pairs : List (ℕ × ℕ)) (borrow : ℕ) :
    (subtractBits (n := n) start pairs borrow).1.length = 8 * pairs.length := by
  induction pairs generalizing start borrow with
  | nil => simp [subtractBits]
  | cons p ps ih => simp [subtractBits, ih, Nat.mul_add, Nat.add_comm]

theorem subtractBits_word_length {n : ℕ} (start : ℕ)
    (pairs : List (ℕ × ℕ)) (borrow : ℕ) :
    (subtractBits (n := n) start pairs borrow).2.1.length = pairs.length := by
  induction pairs generalizing start borrow with
  | nil => rfl
  | cons p ps ih => simp only [subtractBits, List.length_cons, ih]

theorem subtractBits_refs_lt {n : ℕ} (start : ℕ)
    (pairs : List (ℕ × ℕ)) (borrow : ℕ) (hb : borrow < start) :
    (∀ i ∈ (subtractBits (n := n) start pairs borrow).2.1,
      i < start + 8 * pairs.length) ∧
      (subtractBits (n := n) start pairs borrow).2.2 < start + 8 * pairs.length := by
  induction pairs generalizing start borrow with
  | nil => simpa [subtractBits] using hb
  | cons p ps ih =>
      have ht := ih (start + 8) (start + 7) (by omega)
      constructor
      · intro i hi
        simp only [subtractBits, List.mem_cons] at hi
        rcases hi with rfl | hi
        · simp only [List.length_cons]; omega
        · have h := ht.1 i hi
          simp only [List.length_cons]; omega
      · simpa only [subtractBits, List.length_cons, Nat.mul_add, Nat.mul_one,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht.2

theorem wordValue_lt_two_pow_length (vals : List Bool) (word : List ℕ) :
    wordValue vals word < 2 ^ word.length := by
  induction word with
  | nil => simp [wordValue]
  | cons i is ih =>
      have hb : (vals.getD i false).toNat ≤ 1 := by cases vals.getD i false <;> decide
      simp only [wordValue, List.length_cons, Nat.pow_succ]
      omega

/-- Exact unsigned subtraction with an incoming borrow and retained underflow. -/
theorem subtractBits_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (pairs : List (ℕ × ℕ)) (borrow : ℕ)
    (hpairs : ∀ p ∈ pairs, p.1 < vals.length ∧ p.2 < vals.length)
    (hb : borrow < vals.length) :
    wordValue (runFrom a vals (subtractBits vals.length pairs borrow).1)
        (subtractBits (n := n) vals.length pairs borrow).2.1 +
        wordValue vals (pairs.map Prod.snd) + (vals.getD borrow false).toNat =
      wordValue vals (pairs.map Prod.fst) + 2 ^ pairs.length *
        ((runFrom a vals (subtractBits vals.length pairs borrow).1).getD
          (subtractBits (n := n) vals.length pairs borrow).2.2 false).toNat := by
  induction pairs generalizing vals borrow with
  | nil => simp [subtractBits, runFrom, wordValue]
  | cons p ps ih =>
      obtain ⟨hx, hy⟩ := hpairs p (by simp)
      have hps : ∀ q ∈ ps, q.1 < vals.length ∧ q.2 < vals.length :=
        fun q hq => hpairs q (by simp [hq])
      let nextVals := runFrom a vals (fullSubtract vals.length p.1 p.2 borrow)
      have hlen : nextVals.length = vals.length + 8 := by
        simp only [nextVals, runFrom_length, fullSubtract_length]
      have hnext : ∀ q ∈ ps, q.1 < nextVals.length ∧ q.2 < nextVals.length := by
        intro q hq
        obtain ⟨h1, h2⟩ := hps q hq
        rw [hlen]
        constructor <;> omega
      have ht := ih nextVals (vals.length + 7) hnext (by rw [hlen]; omega)
      rw [hlen] at ht
      have hdifference : nextVals.getD (vals.length + 4) false =
          differenceBit (vals.getD p.1 false) (vals.getD p.2 false)
            (vals.getD borrow false) := by
        dsimp only [nextVals]
        rw [runFrom_fullSubtract a vals p.1 p.2 borrow hx hy hb]
        simp only [read_append_new, List.getD_cons_succ, List.getD_cons_zero]
      have hborrow : nextVals.getD (vals.length + 7) false =
          borrowBit (vals.getD p.1 false) (vals.getD p.2 false)
            (vals.getD borrow false) := by
        dsimp only [nextVals]
        rw [runFrom_fullSubtract a vals p.1 p.2 borrow hx hy hb]
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
      rw [hborrow, hfst, hsnd] at ht
      have harith := fullSubtract_arithmetic
        (vals.getD p.1 false) (vals.getD p.2 false) (vals.getD borrow false)
      simp only [subtractBits, runFrom_append, List.map_cons, wordValue,
        List.length_cons, Nat.pow_succ]
      change ((runFrom a nextVals (subtractBits (n := n) (vals.length + 8) ps
        (vals.length + 7)).1).getD (vals.length + 4) false).toNat +
        2 * wordValue (runFrom a nextVals (subtractBits (n := n) (vals.length + 8) ps
          (vals.length + 7)).1) (subtractBits (n := n) (vals.length + 8) ps
          (vals.length + 7)).2.1 +
        ((vals.getD p.2 false).toNat + 2 * wordValue vals (ps.map Prod.snd)) +
        (vals.getD borrow false).toNat =
        (vals.getD p.1 false).toNat + 2 * wordValue vals (ps.map Prod.fst) +
        2 ^ ps.length * 2 *
          ((runFrom a nextVals (subtractBits (n := n) (vals.length + 8) ps
            (vals.length + 7)).1).getD (subtractBits (n := n) (vals.length + 8) ps
              (vals.length + 7)).2.2 false).toNat
      rw [read_runFrom_old a nextVals _ _ (by rw [hlen]; omega), hdifference]
      nlinarith

/-- The actual final borrow bit is exactly unsigned comparison, including the
incoming borrow. Setting that input to false yields the ordinary `<` test. -/
theorem subtractBits_borrow_iff {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (pairs : List (ℕ × ℕ)) (borrow : ℕ)
    (hpairs : ∀ p ∈ pairs, p.1 < vals.length ∧ p.2 < vals.length)
    (hb : borrow < vals.length) :
    (runFrom a vals (subtractBits vals.length pairs borrow).1).getD
        (subtractBits (n := n) vals.length pairs borrow).2.2 false = true ↔
      wordValue vals (pairs.map Prod.fst) <
        wordValue vals (pairs.map Prod.snd) + (vals.getD borrow false).toNat := by
  have hs := subtractBits_spec a vals pairs borrow hpairs hb
  have hr := wordValue_lt_two_pow_length
    (runFrom a vals (subtractBits vals.length pairs borrow).1)
    (subtractBits (n := n) vals.length pairs borrow).2.1
  rw [subtractBits_word_length] at hr
  cases hout : (runFrom a vals (subtractBits vals.length pairs borrow).1).getD
      (subtractBits (n := n) vals.length pairs borrow).2.2 false with
  | false =>
      simp only [hout, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hs
      constructor
      · intro h; cases h
      · intro h; omega
  | true =>
      simp only [hout, Bool.toNat_true, Nat.mul_one] at hs
      constructor
      · intro _; omega
      · intro _; rfl

private def subtractThree (x y : List Bool) (borrow : Bool) : ℕ × Bool :=
  let vals := x ++ y ++ [borrow]
  let code := subtractBits (n := 0) vals.length [(0, 3), (1, 4), (2, 5)] 6
  let result := runFrom (fun i => Fin.elim0 i) vals code.1
  (wordValue result code.2.1, result.getD code.2.2 false)

/-- Kernel checks cover ordinary subtraction, underflow, and incoming borrow. -/
example : subtractThree [true, false, true] [true, true, false] false = (2, false) := by decide
example : subtractThree [true, true, false] [true, false, true] false = (6, true) := by decide
example : subtractThree [false, false, false] [false, false, false] true = (7, true) := by decide

end GodMoveBinarySubtract

#print axioms GodMoveBinarySubtract.fullSubtract_arithmetic
#print axioms GodMoveBinarySubtract.runFrom_fullSubtract
#print axioms GodMoveBinarySubtract.subtractBits_gate_count
#print axioms GodMoveBinarySubtract.subtractBits_word_length
#print axioms GodMoveBinarySubtract.subtractBits_refs_lt
#print axioms GodMoveBinarySubtract.wordValue_lt_two_pow_length
#print axioms GodMoveBinarySubtract.subtractBits_spec
#print axioms GodMoveBinarySubtract.subtractBits_borrow_iff
