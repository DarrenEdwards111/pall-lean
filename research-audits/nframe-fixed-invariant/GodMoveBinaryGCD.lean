import GodMoveBinaryDivision
import GodMoveEuclideanBitIterations

/-!
# Euclidean gcd built from emitted Boolean gates

The circuit unrolls a bit-length-bounded Euclidean iteration. Each round uses
the restoring divider and Boolean selectors; once the divisor is zero the
state is retained. Natural remainder and gcd occur only in the specification,
not as primitives in the generated circuit.

The size bound counts emitted Boolean gates. It does not by itself bound Lean
compiler time, wire lookup, allocation, or a host machine implementation.
-/

namespace GodMoveBinaryGCD

open GodMoveBinaryAdder GodMoveBinaryDivision GodMoveEuclideanBitIterations
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- A Boolean zero test using an actual constant wire and difference gates. -/
def nonzeroWord {n : ℕ} (start : ℕ) (word : List ℕ) : List (CGate n) × ℕ :=
  let test := differentBits (start + 1) (word.map fun i => (i, start))
  ([.cst false] ++ test.1, test.2)

theorem nonzeroWord_gate_count {n : ℕ} (start : ℕ) (word : List ℕ) :
    (nonzeroWord (n := n) start word).1.length = 2 * word.length + 2 := by
  simp [nonzeroWord, differentBits_gate_count]

theorem nonzeroWord_ref_lt {n : ℕ} (start : ℕ) (word : List ℕ) :
    (nonzeroWord (n := n) start word).2 <
      start + (nonzeroWord (n := n) start word).1.length := by
  have h := differentBits_ref_lt (n := n) (start + 1) (word.map fun i => (i, start))
  simpa only [nonzeroWord, List.length_append, List.length_singleton, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using h

private theorem wordValue_map_zero (vals : List Bool) (word : List ℕ) (z : ℕ)
    (hz : vals.getD z false = false) : wordValue vals (word.map fun _ => z) = 0 := by
  induction word with
  | nil => rfl
  | cons i is ih => simp only [List.map_cons, wordValue, hz, ih, Bool.toNat_false,
      Nat.mul_zero, Nat.add_zero]

theorem nonzeroWord_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool) (word : List ℕ)
    (hw : ∀ i ∈ word, i < vals.length) :
    (runFrom a vals (nonzeroWord vals.length word).1).getD
        (nonzeroWord (n := n) vals.length word).2 false =
      decide (wordValue vals word ≠ 0) := by
  let nextVals := vals ++ [false]
  have hlen : nextVals.length = vals.length + 1 := by simp [nextVals]
  have hp : ∀ p ∈ word.map (fun i => (i, vals.length)),
      p.1 < nextVals.length ∧ p.2 < nextVals.length := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have h := hw i hi
    rw [hlen]
    constructor <;> omega
  have ht := differentBits_spec a nextVals (word.map fun i => (i, vals.length)) hp
  have hzero : nextVals.getD vals.length false = false := by
    simp only [nextVals, read_append_start, List.getD_cons_zero]
  have hwold : wordValue nextVals word = wordValue vals word :=
    wordValue_runFrom_old a vals [.cst false] word hw
  have hfst : (word.map fun i => (i, vals.length)).map Prod.fst = word := by
    rw [List.map_map]
    exact List.map_id word
  have hsnd : (word.map fun i => (i, vals.length)).map Prod.snd =
      word.map (fun _ => vals.length) := by rw [List.map_map]; rfl
  rw [hfst, hsnd] at ht
  rw [wordValue_map_zero nextVals word vals.length hzero, hwold, hlen] at ht
  simpa only [nonzeroWord, runFrom_append, runFrom, evalGate] using ht

/-- The specification freezes both state words after a zero divisor. -/
def frozenEuclid : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, a, b => (a, b)
  | fuel + 1, a, b =>
      if b = 0 then frozenEuclid fuel a b else frozenEuclid fuel b (a % b)

@[simp] theorem frozenEuclid_zero (fuel a : ℕ) : frozenEuclid fuel a 0 = (a, 0) := by
  induction fuel <;> simp [frozenEuclid, *]

theorem frozenEuclid_fst (fuel a b : ℕ) :
    (frozenEuclid fuel a b).1 = (euclid fuel a b).value := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ fuel ih =>
      by_cases hb : b = 0
      · simp [hb]
      · simp [frozenEuclid, euclid, hb, ih]

theorem frozenEuclid_gcd (w a b : ℕ) (hb : b.size ≤ w) :
    (frozenEuclid (2 * w + 1) a b).1 = Nat.gcd a b := by
  rw [frozenEuclid_fst]
  exact (euclid_correct_of_size_le w a b hb).1

/-- Select one of two equally wide words without changing its width. -/
def chooseWords {n : ℕ} (start sel : ℕ) (xs ys : List ℕ) :
    List (CGate n) × List ℕ := muxBits start sel (xs.zip ys)

theorem chooseWords_gate_count {n : ℕ} (start sel : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (chooseWords (n := n) start sel xs ys).1.length = 3 * xs.length := by
  simp [chooseWords, muxBits_gate_count, hlen]

theorem chooseWords_word_length {n : ℕ} (start sel : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (chooseWords (n := n) start sel xs ys).2.length = xs.length := by
  simp [chooseWords, muxBits_word_length, hlen]

theorem chooseWords_refs_lt {n : ℕ} (start sel : ℕ) (xs ys : List ℕ) :
    ∀ i ∈ (chooseWords (n := n) start sel xs ys).2,
      i < start + (chooseWords (n := n) start sel xs ys).1.length := by
  simpa only [chooseWords, muxBits_gate_count] using
    muxBits_refs_lt (n := n) start sel (xs.zip ys)

theorem chooseWords_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (sel : ℕ) (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hs : sel < vals.length) (hx : ∀ i ∈ xs, i < vals.length)
    (hy : ∀ i ∈ ys, i < vals.length) :
    wordValue (runFrom a vals (chooseWords vals.length sel xs ys).1)
        (chooseWords (n := n) vals.length sel xs ys).2 =
      if vals.getD sel false then wordValue vals xs else wordValue vals ys := by
  have hp : ∀ p ∈ xs.zip ys, p.1 < vals.length ∧ p.2 < vals.length := by
    intro p hp
    exact ⟨hx p.1 (List.of_mem_zip hp).1, hy p.2 (List.of_mem_zip hp).2⟩
  simpa only [chooseWords, List.map_fst_zip hlen.le, List.map_snd_zip hlen.ge] using
    muxBits_spec a vals sel (xs.zip ys) hs hp

/-- Select the next Euclidean state, retaining both current words at zero. -/
def freezeWords {n : ℕ} (start : ℕ) (xs ys rs : List ℕ) :
    List (CGate n) × (List ℕ × List ℕ) :=
  let nz := nonzeroWord start ys
  let mx := chooseWords (start + nz.1.length) nz.2 ys xs
  let my := chooseWords (start + nz.1.length + mx.1.length) nz.2 rs ys
  (nz.1 ++ mx.1 ++ my.1, (mx.2, my.2))

theorem freezeWords_lengths {n : ℕ} (start : ℕ) (xs ys rs : List ℕ)
    (hlen : xs.length = ys.length) (hrlen : rs.length = ys.length) :
    (freezeWords (n := n) start xs ys rs).2.1.length = xs.length ∧
      (freezeWords (n := n) start xs ys rs).2.2.length = xs.length := by
  simp only [freezeWords, chooseWords_word_length _ _ _ _ hlen.symm,
    chooseWords_word_length _ _ _ _ hrlen, hlen, hrlen, and_self]

theorem freezeWords_gate_count {n : ℕ} (start : ℕ) (xs ys rs : List ℕ)
    (hlen : xs.length = ys.length) (hrlen : rs.length = ys.length) :
    (freezeWords (n := n) start xs ys rs).1.length = 8 * xs.length + 2 := by
  simp only [freezeWords, List.length_append, nonzeroWord_gate_count,
    chooseWords_gate_count _ _ _ _ hlen.symm,
    chooseWords_gate_count _ _ _ _ hrlen, hlen, hrlen]
  omega

theorem freezeWords_refs_lt {n : ℕ} (start : ℕ) (xs ys rs : List ℕ) :
    (∀ i ∈ (freezeWords (n := n) start xs ys rs).2.1,
      i < start + (freezeWords (n := n) start xs ys rs).1.length) ∧
    (∀ i ∈ (freezeWords (n := n) start xs ys rs).2.2,
      i < start + (freezeWords (n := n) start xs ys rs).1.length) := by
  let nz := nonzeroWord (n := n) start ys
  let mx := chooseWords (n := n) (start + nz.1.length) nz.2 ys xs
  let my := chooseWords (n := n) (start + nz.1.length + mx.1.length) nz.2 rs ys
  change (∀ i ∈ mx.2, i < start + (nz.1 ++ mx.1 ++ my.1).length) ∧
    (∀ i ∈ my.2, i < start + (nz.1 ++ mx.1 ++ my.1).length)
  simp only [List.length_append]
  constructor
  · intro i hi
    have h := chooseWords_refs_lt (n := n) (start + nz.1.length) nz.2 ys xs i hi
    change i < start + nz.1.length + mx.1.length at h
    omega
  · intro i hi
    have h := chooseWords_refs_lt (n := n) (start + nz.1.length + mx.1.length) nz.2 rs ys i hi
    change i < start + nz.1.length + mx.1.length + my.1.length at h
    omega

theorem freezeWords_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys rs : List ℕ) (hlen : xs.length = ys.length) (hrlen : rs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length)
    (hr : ∀ i ∈ rs, i < vals.length) :
    wordValue (runFrom a vals (freezeWords vals.length xs ys rs).1)
        (freezeWords (n := n) vals.length xs ys rs).2.1 =
        (if wordValue vals ys = 0 then wordValue vals xs else wordValue vals ys) ∧
      wordValue (runFrom a vals (freezeWords vals.length xs ys rs).1)
        (freezeWords (n := n) vals.length xs ys rs).2.2 =
        (if wordValue vals ys = 0 then wordValue vals ys else wordValue vals rs) := by
  let nz := nonzeroWord (n := n) vals.length ys
  let v1 := runFrom a vals nz.1
  have hl1 : v1.length = vals.length + nz.1.length := runFrom_length _ _ _
  let mx := chooseWords (n := n) v1.length nz.2 ys xs
  let v2 := runFrom a v1 mx.1
  have hl2 : v2.length = v1.length + mx.1.length := runFrom_length _ _ _
  let my := chooseWords (n := n) v2.length nz.2 rs ys
  have hs1 : nz.2 < v1.length := by
    rw [hl1]
    exact nonzeroWord_ref_lt _ _
  have hs2 : nz.2 < v2.length := by rw [hl2]; omega
  have hx1 : ∀ i ∈ xs, i < v1.length := by
    intro i hi; have h := hx i hi; rw [hl1]; omega
  have hy1 : ∀ i ∈ ys, i < v1.length := by
    intro i hi; have h := hy i hi; rw [hl1]; omega
  have hr1 : ∀ i ∈ rs, i < v1.length := by
    intro i hi; have h := hr i hi; rw [hl1]; omega
  have hy2 : ∀ i ∈ ys, i < v2.length := by
    intro i hi; have h := hy1 i hi; rw [hl2]; omega
  have hr2 : ∀ i ∈ rs, i < v2.length := by
    intro i hi; have h := hr1 i hi; rw [hl2]; omega
  have hmx := chooseWords_spec a v1 nz.2 ys xs hlen.symm hs1 hy1 hx1
  have hmy := chooseWords_spec a v2 nz.2 rs ys hrlen hs2 hr2 hy2
  have hnz : v1.getD nz.2 false = decide (wordValue vals ys ≠ 0) :=
    nonzeroWord_spec a vals ys hy
  have hread : v2.getD nz.2 false = v1.getD nz.2 false :=
    read_runFrom_old a v1 mx.1 nz.2 hs1
  have hmxref : ∀ i ∈ mx.2, i < v2.length := by
    rw [hl2]
    exact chooseWords_refs_lt _ _ _ _
  have hkeep : wordValue (runFrom a v2 my.1) mx.2 = wordValue v2 mx.2 :=
    wordValue_runFrom_old a v2 my.1 mx.2 hmxref
  have hyold : wordValue v1 ys = wordValue vals ys := wordValue_runFrom_old _ _ _ _ hy
  have hxold : wordValue v1 xs = wordValue vals xs := wordValue_runFrom_old _ _ _ _ hx
  have hyold2 : wordValue v2 ys = wordValue vals ys :=
    (wordValue_runFrom_old _ _ _ _ hy1).trans hyold
  have hrold2 : wordValue v2 rs = wordValue vals rs :=
    (wordValue_runFrom_old _ _ _ _ hr1).trans (wordValue_runFrom_old _ _ _ _ hr)
  rw [hnz, hyold, hxold] at hmx
  rw [hread, hnz, hyold2, hrold2] at hmy
  have hspec : wordValue (runFrom a v2 my.1) mx.2 =
      (if wordValue vals ys = 0 then wordValue vals xs else wordValue vals ys) ∧
      wordValue (runFrom a v2 my.1) my.2 =
      (if wordValue vals ys = 0 then wordValue vals ys else wordValue vals rs) := by
    rw [hkeep]
    constructor
    · simpa only [decide_eq_true_eq, ite_not] using hmx
    · simpa only [decide_eq_true_eq, ite_not] using hmy
  simpa only [mx, my, v1, v2, nz, runFrom_length, freezeWords, runFrom_append] using hspec

/-- One emitted division circuit followed by the two freezing selectors. -/
def euclideanStep {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    List (CGate n) × (List ℕ × List ℕ) :=
  let d := divideWords start xs ys
  let next := freezeWords (start + d.1.length) xs ys d.2.2
  (d.1 ++ next.1, next.2)

theorem euclideanStep_lengths {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (euclideanStep (n := n) start xs ys).2.1.length = xs.length ∧
      (euclideanStep (n := n) start xs ys).2.2.length = xs.length := by
  exact freezeWords_lengths _ _ _ _ hlen
    ((divideWords_lengths (n := n) start xs ys hlen).2.trans hlen)

theorem euclideanStep_gate_count {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (euclideanStep (n := n) start xs ys).1.length =
      11 * xs.length ^ 2 + 25 * xs.length + 4 := by
  simp only [euclideanStep, List.length_append,
    freezeWords_gate_count _ _ _ _ hlen
      ((divideWords_lengths (n := n) start xs ys hlen).2.trans hlen),
    divideWords_gate_count_exact _ _ _ hlen]
  omega

theorem euclideanStep_refs_lt {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    (∀ i ∈ (euclideanStep (n := n) start xs ys).2.1,
      i < start + (euclideanStep (n := n) start xs ys).1.length) ∧
    (∀ i ∈ (euclideanStep (n := n) start xs ys).2.2,
      i < start + (euclideanStep (n := n) start xs ys).1.length) := by
  have h := freezeWords_refs_lt (n := n)
    (start + (divideWords (n := n) start xs ys).1.length) xs ys
      (divideWords (n := n) start xs ys).2.2
  simpa only [euclideanStep, List.length_append, Nat.add_assoc] using h

theorem euclideanStep_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    wordValue (runFrom a vals (euclideanStep vals.length xs ys).1)
        (euclideanStep (n := n) vals.length xs ys).2.1 =
        (if wordValue vals ys = 0 then wordValue vals xs else wordValue vals ys) ∧
      wordValue (runFrom a vals (euclideanStep vals.length xs ys).1)
        (euclideanStep (n := n) vals.length xs ys).2.2 =
        (if wordValue vals ys = 0 then wordValue vals ys
          else wordValue vals xs % wordValue vals ys) := by
  let d := divideWords (n := n) vals.length xs ys
  let v1 := runFrom a vals d.1
  have hl1 : v1.length = vals.length + d.1.length := runFrom_length _ _ _
  have hx1 : ∀ i ∈ xs, i < v1.length := by
    intro i hi; have h := hx i hi; rw [hl1]; omega
  have hy1 : ∀ i ∈ ys, i < v1.length := by
    intro i hi; have h := hy i hi; rw [hl1]; omega
  have hr1 : ∀ i ∈ d.2.2, i < v1.length := by
    rw [hl1]
    exact (divideWords_refs_lt _ _ _ hlen hx hy).2
  have hrlen : d.2.2.length = ys.length :=
    (divideWords_lengths _ _ _ hlen).2.trans hlen
  have hspec := freezeWords_spec a v1 xs ys d.2.2 hlen hrlen hx1 hy1 hr1
  have hxold : wordValue v1 xs = wordValue vals xs := wordValue_runFrom_old _ _ _ _ hx
  have hyold : wordValue v1 ys = wordValue vals ys := wordValue_runFrom_old _ _ _ _ hy
  have hr : wordValue v1 d.2.2 = wordValue vals xs % wordValue vals ys :=
    (divideWords_spec a vals xs ys hlen hx hy).2
  rw [hxold, hyold, hr] at hspec
  simpa only [euclideanStep, d, v1, runFrom_append, runFrom_length] using hspec

/-- Unrolling depends only on the supplied width and fuel, not input values. -/
def euclidWords {n : ℕ} : ℕ → ℕ → List ℕ → List ℕ →
    List (CGate n) × (List ℕ × List ℕ)
  | 0, _, xs, ys => ([], (xs, ys))
  | fuel + 1, start, xs, ys =>
      let step := euclideanStep start xs ys
      let rest := euclidWords fuel (start + step.1.length) step.2.1 step.2.2
      (step.1 ++ rest.1, rest.2)

theorem euclidWords_lengths {n : ℕ} (fuel start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (euclidWords (n := n) fuel start xs ys).2.1.length = xs.length ∧
      (euclidWords (n := n) fuel start xs ys).2.2.length = xs.length := by
  induction fuel generalizing start xs ys with
  | zero => exact ⟨rfl, hlen.symm⟩
  | succ fuel ih =>
      have hs := euclideanStep_lengths (n := n) start xs ys hlen
      have ht := ih (start + (euclideanStep (n := n) start xs ys).1.length)
        (euclideanStep (n := n) start xs ys).2.1
        (euclideanStep (n := n) start xs ys).2.2 (hs.1.trans hs.2.symm)
      exact ⟨ht.1.trans hs.1, ht.2.trans hs.1⟩

theorem euclidWords_gate_count {n : ℕ} (fuel start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (euclidWords (n := n) fuel start xs ys).1.length =
      fuel * (11 * xs.length ^ 2 + 25 * xs.length + 4) := by
  induction fuel generalizing start xs ys with
  | zero => simp [euclidWords]
  | succ fuel ih =>
      have hs := euclideanStep_lengths (n := n) start xs ys hlen
      simp only [euclidWords, List.length_append,
        ih _ _ _ (hs.1.trans hs.2.symm), hs.1, euclideanStep_gate_count _ _ _ hlen]
      ring

theorem euclidWords_refs_lt {n : ℕ} (fuel start : ℕ) (xs ys : List ℕ)
    (hx : ∀ i ∈ xs, i < start) (hy : ∀ i ∈ ys, i < start) :
    (∀ i ∈ (euclidWords (n := n) fuel start xs ys).2.1,
      i < start + (euclidWords (n := n) fuel start xs ys).1.length) ∧
    (∀ i ∈ (euclidWords (n := n) fuel start xs ys).2.2,
      i < start + (euclidWords (n := n) fuel start xs ys).1.length) := by
  induction fuel generalizing start xs ys with
  | zero => exact ⟨hx, hy⟩
  | succ fuel ih =>
      have hs := euclideanStep_refs_lt (n := n) start xs ys
      have ht := ih (start + (euclideanStep (n := n) start xs ys).1.length)
        (euclideanStep (n := n) start xs ys).2.1
        (euclideanStep (n := n) start xs ys).2.2 hs.1 hs.2
      simpa only [euclidWords, List.length_append, Nat.add_assoc] using ht

theorem euclidWords_spec {n : ℕ} (a : Fin n → Bool) (fuel : ℕ) (vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    (wordValue (runFrom a vals (euclidWords fuel vals.length xs ys).1)
        (euclidWords (n := n) fuel vals.length xs ys).2.1,
      wordValue (runFrom a vals (euclidWords fuel vals.length xs ys).1)
        (euclidWords (n := n) fuel vals.length xs ys).2.2) =
      frozenEuclid fuel (wordValue vals xs) (wordValue vals ys) := by
  induction fuel generalizing vals xs ys with
  | zero => rfl
  | succ fuel ih =>
      let step := euclideanStep (n := n) vals.length xs ys
      let nextVals := runFrom a vals step.1
      have hl : nextVals.length = vals.length + step.1.length := runFrom_length _ _ _
      have hslen := euclideanStep_lengths (n := n) vals.length xs ys hlen
      have hsref := euclideanStep_refs_lt (n := n) vals.length xs ys
      have hx' : ∀ i ∈ step.2.1, i < nextVals.length := by rw [hl]; exact hsref.1
      have hy' : ∀ i ∈ step.2.2, i < nextVals.length := by rw [hl]; exact hsref.2
      have ht := ih nextVals step.2.1 step.2.2 (hslen.1.trans hslen.2.symm) hx' hy'
      have hs := euclideanStep_spec a vals xs ys hlen hx hy
      change wordValue nextVals step.2.1 = _ ∧ wordValue nextVals step.2.2 = _ at hs
      rw [hs.1, hs.2] at ht
      have hstep : frozenEuclid fuel
          (if wordValue vals ys = 0 then wordValue vals xs else wordValue vals ys)
          (if wordValue vals ys = 0 then wordValue vals ys
            else wordValue vals xs % wordValue vals ys) =
          frozenEuclid (fuel + 1) (wordValue vals xs) (wordValue vals ys) := by
        by_cases hb : wordValue vals ys = 0 <;> simp only [frozenEuclid, hb, ↓reduceIte]
      rw [hstep] at ht
      simpa only [euclidWords, step, nextVals, runFrom_length, runFrom_append] using ht

/-- The first word after `2 * width + 1` rounds is the exact gcd. -/
def gcdWords {n : ℕ} (start : ℕ) (xs ys : List ℕ) : List (CGate n) × List ℕ :=
  let result := euclidWords (2 * xs.length + 1) start xs ys
  (result.1, result.2.1)

theorem gcdWords_word_length {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (gcdWords (n := n) start xs ys).2.length = xs.length :=
  (euclidWords_lengths _ _ _ _ hlen).1

theorem gcdWords_refs_lt {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (_hlen : xs.length = ys.length) (hx : ∀ i ∈ xs, i < start)
    (hy : ∀ i ∈ ys, i < start) :
    ∀ i ∈ (gcdWords (n := n) start xs ys).2,
      i < start + (gcdWords (n := n) start xs ys).1.length :=
  (euclidWords_refs_lt _ _ _ _ hx hy).1

theorem gcdWords_gate_count_exact {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (gcdWords (n := n) start xs ys).1.length =
      (2 * xs.length + 1) * (11 * xs.length ^ 2 + 25 * xs.length + 4) :=
  euclidWords_gate_count _ _ _ _ hlen

theorem gcdWords_gate_count {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (gcdWords (n := n) start xs ys).1.length ≤ 64 * (xs.length + 1) ^ 3 := by
  rw [gcdWords_gate_count_exact _ _ _ hlen]
  nlinarith [Nat.zero_le xs.length, Nat.zero_le (xs.length ^ 2), Nat.zero_le (xs.length ^ 3)]

theorem gcdWords_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    wordValue (runFrom a vals (gcdWords vals.length xs ys).1)
        (gcdWords (n := n) vals.length xs ys).2 =
      Nat.gcd (wordValue vals xs) (wordValue vals ys) := by
  have hs := congrArg Prod.fst (euclidWords_spec a (2 * xs.length + 1) vals xs ys hlen hx hy)
  have hb : (wordValue vals ys).size ≤ xs.length := by
    apply Nat.size_le.mpr
    rw [hlen]
    exact GodMoveBinarySubtract.wordValue_lt_two_pow_length _ _
  exact hs.trans (frozenEuclid_gcd _ _ _ hb)

private def gcdTwo (x y : List Bool) : ℕ :=
  let vals := x ++ y
  let code := gcdWords (n := 0) vals.length [0, 1] [2, 3]
  wordValue (runFrom (fun i => Fin.elim0 i) vals code.1) code.2

set_option maxRecDepth 20000 in
example : gcdTwo [true, true] [false, true] = 1 := by decide

set_option maxRecDepth 20000 in
example : gcdTwo [true, true] [false, false] = 3 := by decide

set_option maxRecDepth 20000 in
example : gcdTwo [false, false] [false, false] = 0 := by decide

end GodMoveBinaryGCD

#print axioms GodMoveBinaryGCD.nonzeroWord_spec
#print axioms GodMoveBinaryGCD.freezeWords_spec
#print axioms GodMoveBinaryGCD.euclideanStep_spec
#print axioms GodMoveBinaryGCD.euclidWords_spec
#print axioms GodMoveBinaryGCD.gcdWords_word_length
#print axioms GodMoveBinaryGCD.gcdWords_refs_lt
#print axioms GodMoveBinaryGCD.gcdWords_gate_count_exact
#print axioms GodMoveBinaryGCD.gcdWords_gate_count
#print axioms GodMoveBinaryGCD.gcdWords_spec
