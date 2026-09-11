import GodMoveBinarySubtract

/-!
# Explicit binary selection and restoring division

This backend uses emitted Boolean gates for subtraction and selection. It does
not charge an opaque natural division or remainder operation as a unit step.
The gate bound does not account for the compiler, wire lookup, or allocation,
and this backend has not yet been substituted into the rational construction.
-/

namespace GodMoveBinaryDivision

open GodMoveBinaryAdder GodMoveBinarySubtract
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

def muxBit {n : ℕ} (start sel x y : ℕ) : List (CGate n) :=
  [.bin Bool.and sel x, .bin (fun b v => !b && v) sel y, .bin Bool.or start (start + 1)]

@[simp] theorem muxBit_length {n : ℕ} (start sel x y : ℕ) :
    (muxBit (n := n) start sel x y).length = 3 := rfl

theorem runFrom_muxBit {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (sel x y : ℕ) (hs : sel < vals.length) (_hx : x < vals.length)
    (hy : y < vals.length) :
    runFrom a vals (muxBit vals.length sel x y) = vals ++
      [vals.getD sel false && vals.getD x false,
       !vals.getD sel false && vals.getD y false,
       if vals.getD sel false then vals.getD x false else vals.getD y false] := by
  have hreads (more : List Bool) : (vals ++ more).getD sel false = vals.getD sel false :=
    List.getD_append _ _ _ _ hs
  have hready (more : List Bool) : (vals ++ more).getD y false = vals.getD y false :=
    List.getD_append _ _ _ _ hy
  simp only [muxBit, runFrom, evalGate, List.append_assoc, List.cons_append,
    List.nil_append, hreads, hready, read_append_start, read_append_new,
    List.getD_cons_zero, List.getD_cons_succ]
  cases vals.getD sel false <;> simp

def muxBits {n : ℕ} (start sel : ℕ) : List (ℕ × ℕ) → List (CGate n) × List ℕ
  | [] => ([], [])
  | (x, y) :: rest =>
      let next := muxBits (start + 3) sel rest
      (muxBit start sel x y ++ next.1, (start + 2) :: next.2)

theorem muxBits_gate_count {n : ℕ} (start sel : ℕ) (pairs : List (ℕ × ℕ)) :
    (muxBits (n := n) start sel pairs).1.length = 3 * pairs.length := by
  induction pairs generalizing start with
  | nil => rfl
  | cons p ps ih => simp [muxBits, ih, Nat.mul_add, Nat.add_comm]

theorem muxBits_word_length {n : ℕ} (start sel : ℕ) (pairs : List (ℕ × ℕ)) :
    (muxBits (n := n) start sel pairs).2.length = pairs.length := by
  induction pairs generalizing start with
  | nil => rfl
  | cons p ps ih => simp [muxBits, ih]

theorem muxBits_refs_lt {n : ℕ} (start sel : ℕ) (pairs : List (ℕ × ℕ)) :
    ∀ i ∈ (muxBits (n := n) start sel pairs).2, i < start + 3 * pairs.length := by
  induction pairs generalizing start with
  | nil => simp [muxBits]
  | cons p ps ih =>
      intro i hi
      simp only [muxBits, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp only [List.length_cons]; omega
      · have ht := ih (start + 3) i hi
        simp only [List.length_cons]; omega

theorem muxBits_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (sel : ℕ) (pairs : List (ℕ × ℕ)) (hs : sel < vals.length)
    (hpairs : ∀ p ∈ pairs, p.1 < vals.length ∧ p.2 < vals.length) :
    wordValue (runFrom a vals (muxBits vals.length sel pairs).1)
      (muxBits (n := n) vals.length sel pairs).2 =
      if vals.getD sel false then wordValue vals (pairs.map Prod.fst)
      else wordValue vals (pairs.map Prod.snd) := by
  induction pairs generalizing vals with
  | nil => simp [muxBits, runFrom, wordValue]
  | cons p ps ih =>
      obtain ⟨hx, hy⟩ := hpairs p (by simp)
      have hps : ∀ q ∈ ps, q.1 < vals.length ∧ q.2 < vals.length :=
        fun q hq => hpairs q (by simp [hq])
      let nextVals := runFrom a vals (muxBit vals.length sel p.1 p.2)
      have hlen : nextVals.length = vals.length + 3 := by
        simp only [nextVals, runFrom_length, muxBit_length]
      have hnext : ∀ q ∈ ps, q.1 < nextVals.length ∧ q.2 < nextVals.length := by
        intro q hq
        obtain ⟨h1, h2⟩ := hps q hq
        rw [hlen]
        constructor <;> omega
      have ht := ih nextVals (by rw [hlen]; omega) hnext
      rw [hlen] at ht
      have hsel : nextVals.getD sel false = vals.getD sel false :=
        read_runFrom_old a vals _ _ hs
      have hbit : nextVals.getD (vals.length + 2) false =
          if vals.getD sel false then vals.getD p.1 false else vals.getD p.2 false := by
        dsimp only [nextVals]
        rw [runFrom_muxBit a vals sel p.1 p.2 hs hx hy]
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
      rw [hsel, hfst, hsnd] at ht
      simp only [muxBits, runFrom_append, List.map_cons, wordValue]
      change ((runFrom a nextVals (muxBits (n := n) (vals.length + 3) sel ps).1).getD
        (vals.length + 2) false).toNat +
        2 * wordValue (runFrom a nextVals (muxBits (n := n) (vals.length + 3) sel ps).1)
          (muxBits (n := n) (vals.length + 3) sel ps).2 = _
      rw [read_runFrom_old a nextVals _ _ (by rw [hlen]; omega), hbit, ht]
      cases vals.getD sel false <;> rfl

theorem wordValue_take_eq_of_lt (vals : List Bool) (w : ℕ) (word : List ℕ)
    (h : wordValue vals word < 2 ^ w) :
    wordValue vals (word.take w) = wordValue vals word := by
  induction w generalizing word with
  | zero => simp only [List.take_zero, wordValue]; simpa using (show wordValue vals word = 0 by simpa using h).symm
  | succ w ih =>
      cases word with
      | nil => rfl
      | cons i is =>
          have ht : wordValue vals is < 2 ^ w := by
            simp only [wordValue, Nat.pow_succ] at h
            omega
          simp only [List.take_succ_cons, wordValue, ih is ht]

theorem wordValue_append (vals : List Bool) (xs ys : List ℕ) :
    wordValue vals (xs ++ ys) = wordValue vals xs + 2 ^ xs.length * wordValue vals ys := by
  induction xs with
  | nil => simp [wordValue]
  | cons x xs ih => simp only [List.cons_append, wordValue, ih, List.length_cons, Nat.pow_succ]; ring

theorem wordValue_replicate_zero (vals : List Bool) (z : ℕ) (hz : vals.getD z false = false)
    (w : ℕ) : wordValue vals (List.replicate w z) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [List.replicate_succ, wordValue, hz, Bool.toNat_false,
      ih, Nat.mul_zero, Nat.add_zero]

def restoreWide {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ) :
    List (CGate n) × (ℕ × List ℕ) :=
  let sub := subtractBits start (xs.zip ys) z
  let q := start + sub.1.length
  let mux := muxBits (q + 1) q (sub.2.1.zip xs)
  (sub.1 ++ [.un Bool.not sub.2.2] ++ mux.1, (q, mux.2))

theorem restoreWide_gate_count {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (z : ℕ) (hlen : xs.length = ys.length) :
    (restoreWide (n := n) start xs ys z).1.length = 11 * xs.length + 1 := by
  simp only [restoreWide, List.length_append, List.length_singleton,
    subtractBits_gate_count, muxBits_gate_count, List.length_zip,
    subtractBits_word_length, hlen, min_self]
  omega

theorem restoreWide_word_length {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (z : ℕ) (hlen : xs.length = ys.length) :
    (restoreWide (n := n) start xs ys z).2.2.length = xs.length := by
  simp only [restoreWide, muxBits_word_length, List.length_zip,
    subtractBits_word_length, hlen, min_self]

theorem restoreWide_refs_lt {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ)
    (hlen : xs.length = ys.length) :
    (restoreWide (n := n) start xs ys z).2.1 <
        start + (restoreWide (n := n) start xs ys z).1.length ∧
      ∀ i ∈ (restoreWide (n := n) start xs ys z).2.2,
        i < start + (restoreWide (n := n) start xs ys z).1.length := by
  have hm := muxBits_refs_lt (n := n)
    (start + (subtractBits (n := n) start (xs.zip ys) z).1.length + 1)
    (start + (subtractBits (n := n) start (xs.zip ys) z).1.length)
    ((subtractBits (n := n) start (xs.zip ys) z).2.1.zip xs)
  simp only [subtractBits_gate_count, subtractBits_word_length, List.length_zip,
    hlen, min_self] at hm
  rw [restoreWide_gate_count start xs ys z hlen]
  constructor
  · simp only [restoreWide, subtractBits_gate_count, List.length_zip, hlen, min_self]; omega
  · intro i hi
    simp only [restoreWide, subtractBits_gate_count, List.length_zip, hlen, min_self] at hi
    have hh := hm i hi
    omega

/-- One restoring step either retains the candidate or subtracts the divisor.
Its quotient flag and numerical outputs are derived from the subtractor and mux. -/
theorem restoreWide_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys : List ℕ) (z : ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length)
    (hz : z < vals.length) (hzero : vals.getD z false = false) :
    let code := restoreWide (n := n) vals.length xs ys z
    let out := runFrom a vals code.1
    let q := (out.getD code.2.1 false).toNat
    let r := wordValue out code.2.2
    wordValue vals xs = q * wordValue vals ys + r ∧
      r ≤ wordValue vals xs ∧
      (wordValue vals xs < 2 * wordValue vals ys → r < wordValue vals ys) := by
  let pairs := xs.zip ys
  let sub := subtractBits (n := n) vals.length pairs z
  let v1 := runFrom a vals sub.1
  let q := vals.length + sub.1.length
  let v2 := v1 ++ [!v1.getD sub.2.2 false]
  let ps := sub.2.1.zip xs
  let mux := muxBits (n := n) (q + 1) q ps
  have hpairlen : pairs.length = xs.length := by simp [pairs, List.length_zip, hlen]
  have hpairs : ∀ p ∈ pairs, p.1 < vals.length ∧ p.2 < vals.length := by
    intro p hp
    exact ⟨hx _ (List.of_mem_zip hp).1, hy _ (List.of_mem_zip hp).2⟩
  have hf : pairs.map Prod.fst = xs := List.map_fst_zip (by omega)
  have hg : pairs.map Prod.snd = ys := List.map_snd_zip (by omega)
  have hsub := subtractBits_spec a vals pairs z hpairs hz
  have hborrow := subtractBits_borrow_iff a vals pairs z hpairs hz
  rw [hf, hg, hzero, Bool.toNat_false, Nat.add_zero] at hsub hborrow
  have hlen1 : v1.length = q := runFrom_length a vals sub.1
  have hlen2 : v2.length = q + 1 := by simp only [v2, List.length_append, List.length_singleton, hlen1]
  have href := subtractBits_refs_lt (n := n) vals.length pairs z hz
  have hslen : sub.2.1.length = xs.length := (subtractBits_word_length _ _ _).trans hpairlen
  have hpsf : ps.map Prod.fst = sub.2.1 := List.map_fst_zip (by omega)
  have hpss : ps.map Prod.snd = xs := List.map_snd_zip (by omega)
  have hqread : v2.getD q false = !v1.getD sub.2.2 false := by
    rw [← hlen1]
    exact read_append_start v1 _
  have hdiff : wordValue v2 sub.2.1 = wordValue v1 sub.2.1 := by
    apply wordValue_runFrom_old a v1 [.un Bool.not sub.2.2]
    intro i hi
    have hh := href.1 i hi
    simpa only [v1, runFrom_length, sub, subtractBits_gate_count] using hh
  have hxread : wordValue v2 xs = wordValue vals xs := by
    have he : runFrom a vals (sub.1 ++ [.un Bool.not sub.2.2]) = v2 := by
      rw [runFrom_append]
      rfl
    rw [← he]
    exact wordValue_runFrom_old a vals _ xs hx
  have hps : ∀ p ∈ ps, p.1 < v2.length ∧ p.2 < v2.length := by
    intro p hp
    obtain ⟨h1, h2⟩ := List.of_mem_zip hp
    constructor
    · have hh := href.1 p.1 h1
      rw [hlen2]
      dsimp [q, sub]
      rw [subtractBits_gate_count]
      omega
    · have hh := hx p.2 h2
      rw [hlen2]
      dsimp [q]
      omega
  have hm := muxBits_spec a v2 q ps (by rw [hlen2]; omega) hps
  rw [hlen2, hpsf, hpss, hqread, hdiff, hxread] at hm
  have hqout : (runFrom a v2 mux.1).getD q false = !v1.getD sub.2.2 false := by
    rw [read_runFrom_old a v2 _ _ (by rw [hlen2]; omega), hqread]
  have hphase : runFrom a vals (restoreWide (n := n) vals.length xs ys z).1 =
      runFrom a v2 mux.1 := by
    change runFrom a vals (sub.1 ++ [.un Bool.not sub.2.2] ++ mux.1) = _
    rw [runFrom_append, runFrom_append]
    rfl
  dsimp only
  rw [hphase]
  change wordValue vals xs =
      ((runFrom a v2 mux.1).getD q false).toNat * wordValue vals ys +
        wordValue (runFrom a v2 mux.1) mux.2 ∧
    wordValue (runFrom a v2 mux.1) mux.2 ≤ wordValue vals xs ∧
    (wordValue vals xs < 2 * wordValue vals ys →
      wordValue (runFrom a v2 mux.1) mux.2 < wordValue vals ys)
  rw [hqout, hm]
  cases hb : v1.getD sub.2.2 false with
  | false =>
      change wordValue v1 sub.2.1 + wordValue vals ys =
        wordValue vals xs + 2 ^ pairs.length * (v1.getD sub.2.2 false).toNat at hsub
      simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hsub
      simp only [Bool.not_false, ↓reduceIte, Bool.toNat_true, Nat.one_mul]
      omega
  | true =>
      have hlt : wordValue vals xs < wordValue vals ys := hborrow.mp hb
      simp only [Bool.not_true, Bool.toNat_false, Nat.zero_mul, Nat.zero_add]
      exact ⟨rfl, le_rfl, fun _ => hlt⟩

/-- Consume numerator bits from most significant to least significant. -/
def restoreLoop {n : ℕ} (start : ℕ) :
    List ℕ → List ℕ → List ℕ → List ℕ → ℕ → List (CGate n) × (List ℕ × List ℕ)
  | [], quot, rem, _, _ => ([], (quot, rem))
  | bit :: bits, quot, rem, den, z =>
      let step := restoreWide start (bit :: rem) (den ++ [z]) z
      let rest := restoreLoop (start + step.1.length) bits (step.2.1 :: quot)
        (step.2.2.take rem.length) den z
      (step.1 ++ rest.1, rest.2)

theorem restoreLoop_lengths {n : ℕ} (start : ℕ) (bits quot rem den : List ℕ) (z : ℕ)
    (hlen : rem.length = den.length) :
    (restoreLoop (n := n) start bits quot rem den z).1.length =
        (11 * (rem.length + 1) + 1) * bits.length ∧
      (restoreLoop (n := n) start bits quot rem den z).2.1.length = quot.length + bits.length ∧
      (restoreLoop (n := n) start bits quot rem den z).2.2.length = rem.length := by
  induction bits generalizing start quot rem with
  | nil => simp [restoreLoop]
  | cons bit bits ih =>
      have hs : (bit :: rem).length = (den ++ [z]).length := by simp [hlen]
      have hw := restoreWide_word_length (n := n) start (bit :: rem) (den ++ [z]) z hs
      have ht : ((restoreWide (n := n) start (bit :: rem) (den ++ [z]) z).2.2.take
          rem.length).length = rem.length := by rw [List.length_take, hw]; simp
      have hi := ih (start + (restoreWide (n := n) start (bit :: rem) (den ++ [z]) z).1.length)
        ((restoreWide (n := n) start (bit :: rem) (den ++ [z]) z).2.1 :: quot)
        ((restoreWide (n := n) start (bit :: rem) (den ++ [z]) z).2.2.take rem.length)
        (ht.trans hlen)
      simp only [ht, restoreWide_gate_count start (bit :: rem) (den ++ [z]) z hs,
        List.length_cons] at hi
      simp only [restoreLoop, List.length_append,
        restoreWide_gate_count start (bit :: rem) (den ++ [z]) z hs, List.length_cons]
      exact ⟨by rw [hi.1]; ring, by rw [hi.2.1]; omega, hi.2.2⟩

theorem restoreLoop_refs_lt {n : ℕ} (start : ℕ) (bits quot rem den : List ℕ) (z : ℕ)
    (hlen : rem.length = den.length)
    (hbits : ∀ i ∈ bits, i < start) (hq : ∀ i ∈ quot, i < start)
    (hr : ∀ i ∈ rem, i < start) (hd : ∀ i ∈ den, i < start) (hz : z < start) :
    (∀ i ∈ (restoreLoop (n := n) start bits quot rem den z).2.1,
      i < start + (restoreLoop (n := n) start bits quot rem den z).1.length) ∧
    (∀ i ∈ (restoreLoop (n := n) start bits quot rem den z).2.2,
      i < start + (restoreLoop (n := n) start bits quot rem den z).1.length) := by
  induction bits generalizing start quot rem with
  | nil => simpa only [restoreLoop, List.length_nil, Nat.add_zero] using And.intro hq hr
  | cons bit bits ih =>
      let step := restoreWide (n := n) start (bit :: rem) (den ++ [z]) z
      have hs : (bit :: rem).length = (den ++ [z]).length := by simp [hlen]
      have hsrefs := restoreWide_refs_lt (n := n) start (bit :: rem) (den ++ [z]) z hs
      have hslen := restoreWide_word_length (n := n) start (bit :: rem) (den ++ [z]) z hs
      have ht : (step.2.2.take rem.length).length = rem.length := by
        rw [List.length_take, hslen]; simp
      have hbits' : ∀ i ∈ bits, i < start + step.1.length :=
        fun i hi => (hbits i (List.mem_cons_of_mem bit hi)).trans_le (Nat.le_add_right _ _)
      have hq' : ∀ i ∈ step.2.1 :: quot, i < start + step.1.length := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hsrefs.1
        · exact (hq i hi).trans_le (Nat.le_add_right _ _)
      have hr' : ∀ i ∈ step.2.2.take rem.length, i < start + step.1.length :=
        fun i hi => hsrefs.2 i (List.mem_of_mem_take hi)
      have hd' : ∀ i ∈ den, i < start + step.1.length :=
        fun i hi => (hd i hi).trans_le (Nat.le_add_right _ _)
      have hz' : z < start + step.1.length := hz.trans_le (Nat.le_add_right _ _)
      have hi := ih (start + step.1.length) (step.2.1 :: quot) (step.2.2.take rem.length)
        (ht.trans hlen) hbits' hq' hr' hd' hz'
      simpa only [restoreLoop, List.length_append, Nat.add_assoc] using hi

def foldBits (vals : List Bool) : ℕ → List ℕ → ℕ
  | p, [] => p
  | p, i :: is => foldBits vals (2 * p + (vals.getD i false).toNat) is

theorem foldBits_ge (vals : List Bool) (p : ℕ) (bits : List ℕ) :
    p ≤ foldBits vals p bits := by
  induction bits generalizing p with
  | nil => exact le_rfl
  | cons i is ih => exact (by omega : p ≤ 2 * p + (vals.getD i false).toNat).trans (ih _)

theorem foldBits_eq (vals : List Bool) (p : ℕ) (bits : List ℕ) :
    foldBits vals p bits = p * 2 ^ bits.length + wordValue vals bits.reverse := by
  induction bits generalizing p with
  | nil => simp [foldBits, wordValue]
  | cons i is ih =>
      simp only [foldBits, ih, List.length_cons, List.reverse_cons, wordValue_append,
        List.length_reverse, wordValue, Nat.mul_zero, Nat.add_zero, Nat.pow_succ]
      ring

theorem foldBits_runFrom_old {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (code : List (CGate n)) (p : ℕ) (bits : List ℕ)
    (hbits : ∀ i ∈ bits, i < vals.length) :
    foldBits (runFrom a vals code) p bits = foldBits vals p bits := by
  rw [foldBits_eq, foldBits_eq]
  rw [wordValue_runFrom_old a vals code bits.reverse]
  exact fun i hi => hbits i (List.mem_reverse.mp hi)

theorem restoreLoop_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (bits quot rem den : List ℕ) (z : ℕ) (hlen : rem.length = den.length)
    (hbits : ∀ i ∈ bits, i < vals.length) (hq : ∀ i ∈ quot, i < vals.length)
    (hr : ∀ i ∈ rem, i < vals.length) (hd : ∀ i ∈ den, i < vals.length)
    (hz : z < vals.length) (hzero : vals.getD z false = false)
    (hbound : foldBits vals (wordValue vals quot * wordValue vals den + wordValue vals rem) bits <
      2 ^ rem.length)
    (hinv : 0 < wordValue vals den → wordValue vals rem < wordValue vals den) :
    let code := restoreLoop (n := n) vals.length bits quot rem den z
    let out := runFrom a vals code.1
    wordValue out code.2.1 * wordValue vals den + wordValue out code.2.2 =
        foldBits vals (wordValue vals quot * wordValue vals den + wordValue vals rem) bits ∧
      (0 < wordValue vals den → wordValue out code.2.2 < wordValue vals den) := by
  induction bits generalizing vals quot rem with
  | nil =>
      simp only [restoreLoop, runFrom, foldBits]
      exact ⟨trivial, hinv⟩
  | cons bit bits ih =>
      let step := restoreWide (n := n) vals.length (bit :: rem) (den ++ [z]) z
      let v1 := runFrom a vals step.1
      let rem' := step.2.2.take rem.length
      let quot' := step.2.1 :: quot
      have hs : (bit :: rem).length = (den ++ [z]).length := by simp [hlen]
      have hxs : ∀ i ∈ bit :: rem, i < vals.length := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hbits i List.mem_cons_self
        · exact hr i hi
      have hys : ∀ i ∈ den ++ [z], i < vals.length := by
        intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact hd i hi
        · rcases List.mem_singleton.mp hi with rfl
          exact hz
      have hstep := restoreWide_spec a vals (bit :: rem) (den ++ [z]) z hs hxs hys hz hzero
      have hyval : wordValue vals (den ++ [z]) = wordValue vals den := by
        simp only [wordValue_append, wordValue, hzero, Bool.toNat_false,
          Nat.mul_zero, Nat.add_zero]
      simp only [hyval, wordValue] at hstep
      have hlen1 : v1.length = vals.length + step.1.length := runFrom_length a vals step.1
      have href := restoreWide_refs_lt (n := n) vals.length (bit :: rem) (den ++ [z]) z hs
      have hw := restoreWide_word_length (n := n) vals.length (bit :: rem) (den ++ [z]) z hs
      have hrem' : rem'.length = rem.length := by
        rw [List.length_take, hw]; simp
      have hbit : (vals.getD bit false).toNat ≤ 1 := by cases vals.getD bit false <;> decide
      have hge := foldBits_ge vals
        (2 * (wordValue vals quot * wordValue vals den + wordValue vals rem) +
          (vals.getD bit false).toNat) bits
      have hcandidate : (vals.getD bit false).toNat + 2 * wordValue vals rem < 2 ^ rem.length := by
        change foldBits vals (2 * (wordValue vals quot * wordValue vals den + wordValue vals rem) +
          (vals.getD bit false).toNat) bits < 2 ^ rem.length at hbound
        nlinarith
      have htrunc : wordValue v1 rem' = wordValue v1 step.2.2 :=
        wordValue_take_eq_of_lt v1 rem.length step.2.2 (hstep.2.1.trans_lt hcandidate)
      have hdval : wordValue v1 den = wordValue vals den := wordValue_runFrom_old a vals _ den hd
      have hqval : wordValue v1 quot = wordValue vals quot := wordValue_runFrom_old a vals _ quot hq
      have hnextvalue : wordValue v1 quot' * wordValue v1 den + wordValue v1 rem' =
          2 * (wordValue vals quot * wordValue vals den + wordValue vals rem) +
            (vals.getD bit false).toNat := by
        dsimp only [quot']
        rw [wordValue, hdval, hqval, htrunc]
        nlinarith [hstep.1]
      have hbits' : ∀ i ∈ bits, i < v1.length := by
        intro i hi
        have hh := hbits i (List.mem_cons_of_mem bit hi)
        rw [hlen1]; omega
      have hq' : ∀ i ∈ quot', i < v1.length := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · simpa only [hlen1] using href.1
        · have hh := hq i hi; rw [hlen1]; omega
      have hr' : ∀ i ∈ rem', i < v1.length := by
        intro i hi
        simpa only [hlen1] using href.2 i (List.mem_of_mem_take hi)
      have hd' : ∀ i ∈ den, i < v1.length := by
        intro i hi
        have hh := hd i hi; rw [hlen1]; omega
      have hz' : z < v1.length := by rw [hlen1]; omega
      have hzero' : v1.getD z false = false := (read_runFrom_old a vals _ z hz).trans hzero
      have htotal : foldBits v1 (wordValue v1 quot' * wordValue v1 den + wordValue v1 rem') bits =
          foldBits vals (wordValue vals quot * wordValue vals den + wordValue vals rem) (bit :: bits) := by
        rw [hnextvalue, foldBits_runFrom_old a vals step.1 _ bits]
        rfl
        exact fun i hi => hbits i (List.mem_cons_of_mem bit hi)
      have hinv' : 0 < wordValue v1 den → wordValue v1 rem' < wordValue v1 den := by
        rw [hdval, htrunc]
        intro hpos
        apply hstep.2.2
        have hh := hinv hpos
        omega
      have hrest := ih v1 quot' rem' (hrem'.trans hlen) hbits' hq' hr' hd' hz' hzero'
        (by rw [htotal, hrem']; exact hbound) hinv'
      dsimp only at hrest ⊢
      rw [htotal, hdval] at hrest
      simpa only [restoreLoop, runFrom_append, hlen1] using hrest

/-- Equal-width unsigned division. A final Boolean mask makes division by zero
return quotient zero and the original numerator as remainder. -/
def divideWords {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    List (CGate n) × (List ℕ × List ℕ) :=
  let zeros := List.replicate xs.length start
  let core := restoreLoop (start + 1) xs.reverse [] zeros ys start
  let nz := differentBits (start + 1 + core.1.length) (ys.zip zeros)
  let mask := muxBits (start + 1 + core.1.length + nz.1.length) nz.2 (core.2.1.zip zeros)
  ([.cst false] ++ core.1 ++ nz.1 ++ mask.1, (mask.2, core.2.2))

theorem divideWords_lengths {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (divideWords (n := n) start xs ys).2.1.length = xs.length ∧
      (divideWords (n := n) start xs ys).2.2.length = xs.length := by
  have hc := restoreLoop_lengths (n := n) (start + 1) xs.reverse []
    (List.replicate xs.length start) ys start (by simpa using hlen)
  simp only [List.length_reverse, List.length_nil, Nat.zero_add, List.length_replicate] at hc
  constructor
  · simp only [divideWords, muxBits_word_length, List.length_zip,
      hc.2.1, List.length_replicate, min_self]
  · exact hc.2.2

theorem divideWords_gate_count_exact {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (divideWords (n := n) start xs ys).1.length = 11 * xs.length ^ 2 + 17 * xs.length + 2 := by
  have hc := restoreLoop_lengths (n := n) (start + 1) xs.reverse []
    (List.replicate xs.length start) ys start (by simpa using hlen)
  simp only [List.length_reverse, List.length_nil, Nat.zero_add, List.length_replicate] at hc
  simp only [divideWords, List.length_append, List.length_singleton,
    muxBits_gate_count, differentBits_gate_count, List.length_zip,
    List.length_replicate, hc.1, hc.2.1, ← hlen, min_self]
  ring

theorem divideWords_gate_count {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (divideWords (n := n) start xs ys).1.length ≤ 16 * (xs.length + 1) ^ 2 := by
  rw [divideWords_gate_count_exact start xs ys hlen]
  nlinarith

theorem divideWords_refs_lt {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) (hx : ∀ i ∈ xs, i < start) (hy : ∀ i ∈ ys, i < start) :
    (∀ i ∈ (divideWords (n := n) start xs ys).2.1,
      i < start + (divideWords (n := n) start xs ys).1.length) ∧
    (∀ i ∈ (divideWords (n := n) start xs ys).2.2,
      i < start + (divideWords (n := n) start xs ys).1.length) := by
  let zeros := List.replicate xs.length start
  let core := restoreLoop (n := n) (start + 1) xs.reverse [] zeros ys start
  let nz := differentBits (n := n) (start + 1 + core.1.length) (ys.zip zeros)
  let mask := muxBits (n := n) (start + 1 + core.1.length + nz.1.length) nz.2 (core.2.1.zip zeros)
  have hzeros : ∀ i ∈ zeros, i < start + 1 := by
    intro i hi
    have he : i = start := (List.mem_replicate.mp hi).2
    omega
  have hcore := restoreLoop_refs_lt (n := n) (start + 1) xs.reverse [] zeros ys start
    (by simpa only [zeros, List.length_replicate] using hlen)
    (fun i hi => (hx i (List.mem_reverse.mp hi)).trans_le (Nat.le_succ _))
    (by simp) hzeros (fun i hi => (hy i hi).trans_le (Nat.le_succ _)) (Nat.lt_succ_self _)
  have hmask := muxBits_refs_lt (n := n)
    (start + 1 + core.1.length + nz.1.length) nz.2 (core.2.1.zip zeros)
  have hmcount := muxBits_gate_count (n := n)
    (start + 1 + core.1.length + nz.1.length) nz.2 (core.2.1.zip zeros)
  change (∀ i ∈ mask.2, i < start + ([CGate.cst (n := n) false] ++ core.1 ++ nz.1 ++ mask.1).length) ∧
    (∀ i ∈ core.2.2, i < start + ([CGate.cst (n := n) false] ++ core.1 ++ nz.1 ++ mask.1).length)
  simp only [List.length_append, List.length_singleton]
  constructor
  · intro i hi
    have hh := hmask i hi
    change mask.1.length = _ at hmcount
    omega
  · intro i hi
    have hh := hcore.2 i hi
    change i < start + 1 + core.1.length at hh
    omega

set_option maxHeartbeats 2000000 in
/-- Exact quotient and remainder of the two input words. This theorem covers
zero divisors as well as the ordinary positive-divisor Euclidean specification. -/
theorem divideWords_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    let code := divideWords (n := n) vals.length xs ys
    let out := runFrom a vals code.1
    wordValue out code.2.1 = wordValue vals xs / wordValue vals ys ∧
      wordValue out code.2.2 = wordValue vals xs % wordValue vals ys := by
  let z := vals.length
  let zeros := List.replicate xs.length z
  let v0 := vals ++ [false]
  let core := restoreLoop (n := n) (z + 1) xs.reverse [] zeros ys z
  let v1 := runFrom a v0 core.1
  let nz := differentBits (n := n) (z + 1 + core.1.length) (ys.zip zeros)
  let v2 := runFrom a v1 nz.1
  let mask := muxBits (n := n) (z + 1 + core.1.length + nz.1.length) nz.2 (core.2.1.zip zeros)
  let v3 := runFrom a v2 mask.1
  have hl0 : v0.length = z + 1 := by simp only [v0, List.length_append, List.length_singleton]; rfl
  have hl1 : v1.length = z + 1 + core.1.length := by rw [runFrom_length, hl0]
  have hl2 : v2.length = z + 1 + core.1.length + nz.1.length := by rw [runFrom_length, hl1]
  have hz0 : z < v0.length := by rw [hl0]; omega
  have hzval : v0.getD z false = false := read_append_start vals [false]
  have hxs0 : ∀ i ∈ xs, i < v0.length := by
    intro i hi
    have hh := hx i hi
    rw [hl0]; dsimp [z]; omega
  have hys0 : ∀ i ∈ ys, i < v0.length := by
    intro i hi
    have hh := hy i hi
    rw [hl0]; dsimp [z]; omega
  have hzs0 : ∀ i ∈ zeros, i < v0.length := by
    intro i hi
    have he := (List.mem_replicate.mp hi).2
    exact he ▸ hz0
  have hxsval : wordValue v0 xs = wordValue vals xs := wordValue_runFrom_old a vals [.cst false] xs hx
  have hysval : wordValue v0 ys = wordValue vals ys := wordValue_runFrom_old a vals [.cst false] ys hy
  have hzsval : wordValue v0 zeros = 0 := wordValue_replicate_zero v0 z hzval xs.length
  have hwidth : zeros.length = ys.length := by simpa only [zeros, List.length_replicate] using hlen
  have hfold : foldBits v0 (wordValue v0 [] * wordValue v0 ys + wordValue v0 zeros) xs.reverse =
      wordValue vals xs := by
    simp only [wordValue, hzsval, Nat.zero_mul, Nat.zero_add, foldBits_eq,
      List.reverse_reverse, hxsval]
  have hbound : foldBits v0 (wordValue v0 [] * wordValue v0 ys + wordValue v0 zeros) xs.reverse <
      2 ^ zeros.length := by
    rw [hfold]
    simpa only [zeros, List.length_replicate] using wordValue_lt_two_pow_length vals xs
  have hc := restoreLoop_spec a v0 xs.reverse [] zeros ys z hwidth
    (fun i hi => hxs0 i (List.mem_reverse.mp hi)) (by simp) hzs0 hys0 hz0 hzval hbound
    (by rw [hzsval]; exact fun h => h)
  dsimp only at hc
  rw [hfold, hysval, hl0] at hc
  have hcl := restoreLoop_lengths (n := n) (z + 1) xs.reverse [] zeros ys z hwidth
  have hquotlen : core.2.1.length = xs.length := by
    simpa only [List.length_nil, Nat.zero_add, List.length_reverse] using hcl.2.1
  have hcrefs := restoreLoop_refs_lt (n := n) (z + 1) xs.reverse [] zeros ys z hwidth
    (by rw [← hl0]; exact fun i hi => hxs0 i (List.mem_reverse.mp hi))
    (by simp) (by rw [← hl0]; exact hzs0) (by rw [← hl0]; exact hys0)
    (Nat.lt_succ_self z)
  have hqrefs : ∀ i ∈ core.2.1, i < v1.length := by rw [hl1]; exact hcrefs.1
  have hrrefs : ∀ i ∈ core.2.2, i < v1.length := by rw [hl1]; exact hcrefs.2
  have hys1 : ∀ i ∈ ys, i < v1.length := by
    intro i hi
    have hh := hys0 i hi
    rw [hl1]; rw [hl0] at hh; omega
  have hzs1 : ∀ i ∈ zeros, i < v1.length := by
    intro i hi
    have hh := hzs0 i hi
    rw [hl1]; rw [hl0] at hh; omega
  have hysval1 : wordValue v1 ys = wordValue vals ys :=
    (wordValue_runFrom_old a v0 core.1 ys hys0).trans hysval
  have hzsval1 : wordValue v1 zeros = 0 :=
    (wordValue_runFrom_old a v0 core.1 zeros hzs0).trans hzsval
  have hnzpairs : ∀ p ∈ ys.zip zeros, p.1 < v1.length ∧ p.2 < v1.length := by
    intro p hp
    exact ⟨hys1 _ (List.of_mem_zip hp).1, hzs1 _ (List.of_mem_zip hp).2⟩
  have hnz := differentBits_spec a v1 (ys.zip zeros) hnzpairs
  rw [List.map_fst_zip hwidth.ge, List.map_snd_zip hwidth.le, hysval1, hzsval1, hl1] at hnz
  have hnzref : nz.2 < v2.length := by
    rw [hl2]
    exact differentBits_ref_lt (n := n) (z + 1 + core.1.length) (ys.zip zeros)
  have hqrefs2 : ∀ i ∈ core.2.1, i < v2.length := by
    intro i hi
    have hh := hqrefs i hi
    rw [hl2]; rw [hl1] at hh; omega
  have hzs2 : ∀ i ∈ zeros, i < v2.length := by
    intro i hi
    have hh := hzs1 i hi
    rw [hl2]; rw [hl1] at hh; omega
  have hqval2 : wordValue v2 core.2.1 = wordValue v1 core.2.1 :=
    wordValue_runFrom_old a v1 nz.1 core.2.1 hqrefs
  have hzsval2 : wordValue v2 zeros = 0 :=
    (wordValue_runFrom_old a v1 nz.1 zeros hzs1).trans hzsval1
  have hmpairs : ∀ p ∈ core.2.1.zip zeros, p.1 < v2.length ∧ p.2 < v2.length := by
    intro p hp
    exact ⟨hqrefs2 _ (List.of_mem_zip hp).1, hzs2 _ (List.of_mem_zip hp).2⟩
  have hm := muxBits_spec a v2 nz.2 (core.2.1.zip zeros) hnzref hmpairs
  have hmwidth : core.2.1.length = zeros.length := by simpa only [zeros, List.length_replicate] using hquotlen
  rw [List.map_fst_zip hmwidth.le, List.map_snd_zip hmwidth.ge,
    hqval2, hzsval2, hnz, hl2] at hm
  have hrval3 : wordValue v3 core.2.2 = wordValue v1 core.2.2 := by
    have he : runFrom a v1 (nz.1 ++ mask.1) = v3 := runFrom_append a v1 nz.1 mask.1
    rw [← he]
    exact wordValue_runFrom_old a v1 _ core.2.2 hrrefs
  have hphase : runFrom a vals (divideWords (n := n) vals.length xs ys).1 = v3 := by
    change runFrom a vals ([.cst false] ++ core.1 ++ nz.1 ++ mask.1) = _
    rw [runFrom_append, runFrom_append, runFrom_append]
    rfl
  dsimp only
  rw [hphase]
  change wordValue v3 mask.2 = wordValue vals xs / wordValue vals ys ∧
    wordValue v3 core.2.2 = wordValue vals xs % wordValue vals ys
  rw [hm, hrval3]
  by_cases hd0 : wordValue vals ys = 0
  · simp only [hd0, Nat.mul_zero, Nat.zero_add] at hc
    simpa [hd0] using And.intro (Eq.refl (0 : ℕ)) hc.1
  · have hdpos : 0 < wordValue vals ys := Nat.pos_of_ne_zero hd0
    have hquot : wordValue vals xs / wordValue vals ys = wordValue v1 core.2.1 :=
      Nat.div_eq_of_lt_le (by nlinarith [hc.1]) (by nlinarith [hc.1, hc.2 hdpos])
    have hrem : wordValue vals xs % wordValue vals ys = wordValue v1 core.2.2 := by
      rw [← hc.1]
      simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt (hc.2 hdpos)]
      rfl
    simpa [hd0] using
      And.intro hquot.symm hrem.symm

private def divideThree (x y : List Bool) : ℕ × ℕ :=
  let vals := x ++ y
  let code := divideWords (n := 0) vals.length [0, 1, 2] [3, 4, 5]
  let result := runFrom (fun i => Fin.elim0 i) vals code.1
  (wordValue result code.2.1, wordValue result code.2.2)

set_option maxRecDepth 100000 in
example : divideThree [true, true, true] [true, true, false] = (2, 1) := by decide

set_option maxRecDepth 100000 in
example : divideThree [true, false, true] [false, false, false] = (0, 5) := by decide

set_option maxRecDepth 100000 in
example : divideThree [false, false, false] [false, true, true] = (0, 0) := by decide

set_option maxRecDepth 100000 in
example : divideThree [true, true, true] [true, false, false] = (7, 0) := by decide

end GodMoveBinaryDivision

#print axioms GodMoveBinaryDivision.muxBits_spec
#print axioms GodMoveBinaryDivision.muxBits_gate_count
#print axioms GodMoveBinaryDivision.restoreWide_spec
#print axioms GodMoveBinaryDivision.restoreLoop_spec
#print axioms GodMoveBinaryDivision.divideWords_lengths
#print axioms GodMoveBinaryDivision.divideWords_gate_count_exact
#print axioms GodMoveBinaryDivision.divideWords_gate_count
#print axioms GodMoveBinaryDivision.divideWords_refs_lt
#print axioms GodMoveBinaryDivision.divideWords_spec
