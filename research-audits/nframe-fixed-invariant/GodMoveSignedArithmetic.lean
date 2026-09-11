import GodMoveBinaryDivision
import GodMoveRationalWireEncoding

/-!
# Signed magnitude addition and subtraction by emitted Boolean gates

A true sign bit denotes a negative magnitude. Zero need not have a canonical
sign. The builders retain an extra magnitude bit and therefore have exact
integer semantics without an overflow assumption. Gate counts concern the
emitted backend, not Lean's native integer operations or circuit generation.
-/

namespace GodMoveSignedArithmetic

open GodMoveBinaryAdder GodMoveBinarySubtract GodMoveBinaryDivision
open GodMoveRationalWireEncoding
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Return the comparison sign and the absolute unsigned difference. -/
def absDifference {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ) :
    List (CGate n) × (ℕ × List ℕ) :=
  let d := subtractBits start (xs.zip ys) z
  let e := subtractBits (start + d.1.length) (ys.zip xs) z
  let m := muxBits (start + d.1.length + e.1.length) d.2.2 (e.2.1.zip d.2.1)
  (d.1 ++ e.1 ++ m.1, (d.2.2, m.2))

theorem absDifference_gate_count {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ)
    (hlen : xs.length = ys.length) :
    (absDifference (n := n) start xs ys z).1.length = 19 * xs.length := by
  simp only [absDifference, List.length_append, subtractBits_gate_count,
    muxBits_gate_count, subtractBits_word_length, List.length_zip, hlen, min_self]
  omega

theorem absDifference_word_length {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ)
    (hlen : xs.length = ys.length) :
    (absDifference (n := n) start xs ys z).2.2.length = xs.length := by
  simp only [absDifference, muxBits_word_length, subtractBits_word_length,
    List.length_zip, hlen, min_self]

theorem absDifference_refs_lt {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ)
    (hlen : xs.length = ys.length) (hz : z < start) :
    (absDifference (n := n) start xs ys z).2.1 <
        start + (absDifference (n := n) start xs ys z).1.length ∧
      ∀ i ∈ (absDifference (n := n) start xs ys z).2.2,
        i < start + (absDifference (n := n) start xs ys z).1.length := by
  have hd := (subtractBits_refs_lt (n := n) start (xs.zip ys) z hz).2
  have hm := muxBits_refs_lt (n := n)
    (start + (subtractBits (n := n) start (xs.zip ys) z).1.length +
      (subtractBits (n := n) (start + (subtractBits (n := n) start (xs.zip ys) z).1.length)
        (ys.zip xs) z).1.length)
    (subtractBits (n := n) start (xs.zip ys) z).2.2
    ((subtractBits (n := n) (start + (subtractBits (n := n) start (xs.zip ys) z).1.length)
      (ys.zip xs) z).2.1.zip (subtractBits (n := n) start (xs.zip ys) z).2.1)
  rw [absDifference_gate_count start xs ys z hlen]
  simp only [List.length_zip, hlen, min_self] at hd
  constructor
  · change (subtractBits (n := n) start (xs.zip ys) z).2.2 < _
    omega
  · intro i hi
    have h := hm i hi
    simp only [subtractBits_gate_count, subtractBits_word_length, List.length_zip,
      hlen, min_self] at h
    omega

theorem absDifference_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys : List ℕ) (z : ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length)
    (hz : z < vals.length) (hzero : vals.getD z false = false) :
    let code := absDifference (n := n) vals.length xs ys z
    let out := runFrom a vals code.1
    if out.getD code.2.1 false then
      wordValue out code.2.2 + wordValue vals xs = wordValue vals ys
    else wordValue out code.2.2 + wordValue vals ys = wordValue vals xs := by
  let d := subtractBits (n := n) vals.length (xs.zip ys) z
  let v1 := runFrom a vals d.1
  let e := subtractBits (n := n) (vals.length + d.1.length) (ys.zip xs) z
  let v2 := runFrom a v1 e.1
  let ps := e.2.1.zip d.2.1
  let m := muxBits (n := n) (vals.length + d.1.length + e.1.length) d.2.2 ps
  have hl1 : v1.length = vals.length + d.1.length := runFrom_length a vals d.1
  have hl2 : v2.length = vals.length + d.1.length + e.1.length := by
    rw [show v2 = runFrom a v1 e.1 from rfl, runFrom_length, hl1]
  have hp : ∀ p ∈ xs.zip ys, p.1 < vals.length ∧ p.2 < vals.length := by
    intro p hp
    exact ⟨hx _ (List.of_mem_zip hp).1, hy _ (List.of_mem_zip hp).2⟩
  have hr1 := subtractBits_refs_lt (n := n) vals.length (xs.zip ys) z hz
  have hdref : ∀ i ∈ d.2.1, i < v1.length := by
    simpa only [hl1, d, subtractBits_gate_count] using hr1.1
  have hbref : d.2.2 < v1.length := by
    simpa only [hl1, d, subtractBits_gate_count] using hr1.2
  have hx1 : ∀ i ∈ xs, i < v1.length := by intro i hi; have h := hx i hi; rw [hl1]; omega
  have hy1 : ∀ i ∈ ys, i < v1.length := by intro i hi; have h := hy i hi; rw [hl1]; omega
  have hz1 : z < v1.length := by rw [hl1]; omega
  have hp1 : ∀ p ∈ ys.zip xs, p.1 < v1.length ∧ p.2 < v1.length := by
    intro p hp
    exact ⟨hy1 _ (List.of_mem_zip hp).1, hx1 _ (List.of_mem_zip hp).2⟩
  have hr2 := subtractBits_refs_lt (n := n) v1.length (ys.zip xs) z hz1
  rw [hl1] at hr2
  have heref : ∀ i ∈ e.2.1, i < v2.length := by
    simpa only [hl2, e, subtractBits_gate_count] using hr2.1
  have hblate : d.2.2 < v2.length := by
    have hlen : v2.length = v1.length + e.1.length := runFrom_length a v1 e.1
    omega
  have hp2 : ∀ p ∈ ps, p.1 < v2.length ∧ p.2 < v2.length := by
    intro p hp
    obtain ⟨he, hd⟩ := List.of_mem_zip hp
    refine ⟨heref _ he, ?_⟩
    have h := hdref _ hd
    have hlen : v2.length = v1.length + e.1.length := runFrom_length a v1 e.1
    omega
  have hdl : d.2.1.length = xs.length := by simp [d, subtractBits_word_length, List.length_zip, hlen]
  have hel : e.2.1.length = xs.length := by simp [e, subtractBits_word_length, List.length_zip, hlen]
  have hm := muxBits_spec a v2 d.2.2 ps hblate hp2
  rw [hl2, show ps.map Prod.fst = e.2.1 from List.map_fst_zip (by omega),
    show ps.map Prod.snd = d.2.1 from List.map_snd_zip (by omega),
    read_runFrom_old a v1 e.1 _ hbref, wordValue_runFrom_old a v1 e.1 _ hdref] at hm
  have hd := subtractBits_spec a vals (xs.zip ys) z hp hz
  have hb := subtractBits_borrow_iff a vals (xs.zip ys) z hp hz
  rw [List.map_fst_zip (by omega), List.map_snd_zip (by omega), hzero,
    Bool.toNat_false, Nat.add_zero] at hd hb
  have he := subtractBits_spec a v1 (ys.zip xs) z hp1 hz1
  have heb := subtractBits_borrow_iff a v1 (ys.zip xs) z hp1 hz1
  rw [List.map_fst_zip (by omega), List.map_snd_zip (by omega),
    read_runFrom_old a vals d.1 z hz, hzero, Bool.toNat_false, Nat.add_zero,
    wordValue_runFrom_old a vals d.1 xs hx,
    wordValue_runFrom_old a vals d.1 ys hy, hl1] at he heb
  have hphase : runFrom a vals (absDifference (n := n) vals.length xs ys z).1 =
      runFrom a v2 m.1 := by
    change runFrom a vals (d.1 ++ e.1 ++ m.1) = _
    rw [runFrom_append, runFrom_append]
  dsimp only
  rw [hphase]
  change if (runFrom a v2 m.1).getD d.2.2 false then
    wordValue (runFrom a v2 m.1) m.2 + wordValue vals xs = wordValue vals ys
    else wordValue (runFrom a v2 m.1) m.2 + wordValue vals ys = wordValue vals xs
  rw [read_runFrom_old a v2 m.1 _ hblate, read_runFrom_old a v1 e.1 _ hbref, hm]
  change wordValue v1 d.2.1 + wordValue vals ys =
    wordValue vals xs + 2 ^ (xs.zip ys).length * (v1.getD d.2.2 false).toNat at hd
  change v1.getD d.2.2 false = true ↔ _ at hb
  change wordValue v2 e.2.1 + wordValue vals xs =
    wordValue vals ys + 2 ^ (ys.zip xs).length * (v2.getD e.2.2 false).toNat at he
  change v2.getD e.2.2 false = true ↔ _ at heb
  cases hbval : v1.getD d.2.2 false with
  | false => simpa only [hbval, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] using hd
  | true =>
    have hlt := hb.mp hbval
    have heval : v2.getD e.2.2 false = false := by
      cases h : v2.getD e.2.2 false
      · rfl
      · have hh := heb.mp h; omega
    simpa only [heval, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] using he

def signControl {n : ℕ} (start sx sy borrow : ℕ) : List (CGate n) :=
  [.bin Bool.xor sx sy, .bin Bool.and start borrow, .bin Bool.xor sx (start + 1)]

@[simp] theorem signControl_length {n : ℕ} (start sx sy borrow : ℕ) :
    (signControl (n := n) start sx sy borrow).length = 3 := rfl

theorem runFrom_signControl {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (sx sy borrow : ℕ) (hx : sx < vals.length) (hb : borrow < vals.length) :
    runFrom a vals (signControl vals.length sx sy borrow) = vals ++
      [vals.getD sx false ^^ vals.getD sy false,
        (vals.getD sx false ^^ vals.getD sy false) && vals.getD borrow false,
        vals.getD sx false ^^
          ((vals.getD sx false ^^ vals.getD sy false) && vals.getD borrow false)] := by
  have hreadx (more : List Bool) : (vals ++ more).getD sx false = vals.getD sx false :=
    List.getD_append _ _ _ _ hx
  have hreadb (more : List Bool) : (vals ++ more).getD borrow false = vals.getD borrow false :=
    List.getD_append _ _ _ _ hb
  simp only [signControl, runFrom, evalGate, List.append_assoc, List.cons_append,
    List.nil_append, hreadx, hreadb, read_append_start, read_append_new,
    List.getD_cons_zero, List.getD_cons_succ]

private theorem signed_sum_identity (sx sy b : Bool) (x y d : ℕ)
    (hd : if b then d + x = y else d + y = x) :
    (if sx ^^ ((sx ^^ sy) && b) then -((if sx ^^ sy then d else x + y : ℕ) : ℤ)
      else ((if sx ^^ sy then d else x + y : ℕ) : ℤ)) =
    (if sx then -(x : ℤ) else (x : ℤ)) + (if sy then -(y : ℤ) else (y : ℤ)) := by
  cases sx <;> cases sy <;> cases b <;> simp_all <;> omega

/-- Sign reference followed by a little-endian magnitude word of width `w+1`.
Both unsigned differences are retained as shared circuit subcomputations. -/
def addSigned {n : ℕ} (start sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ) :
    List (CGate n) × (ℕ × List ℕ) :=
  let sum := addBits (start + 1) (xs.zip ys) start
  let diff := absDifference (start + 1 + sum.1.length) xs ys start
  let t := start + 1 + sum.1.length + diff.1.length
  let control := signControl t sx sy diff.2.1
  let mag := muxBits (t + control.length) t ((diff.2.2 ++ [start]).zip sum.2)
  ([.cst false] ++ sum.1 ++ diff.1 ++ control ++ mag.1, (t + 2, mag.2))

theorem addSigned_gate_count {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (addSigned (n := n) start sx xs sy ys).1.length = 27 * xs.length + 7 := by
  simp only [addSigned, List.length_append, List.length_singleton,
    addBits_gate_count, absDifference_gate_count _ _ _ _ hlen, signControl_length,
    muxBits_gate_count, absDifference_word_length _ _ _ _ hlen, addBits_word_length,
    List.length_zip, hlen, min_self]
  omega

theorem addSigned_word_length {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (addSigned (n := n) start sx xs sy ys).2.2.length = xs.length + 1 := by
  simp only [addSigned, muxBits_word_length, List.length_zip,
    List.length_append, List.length_singleton, absDifference_word_length _ _ _ _ hlen,
    addBits_word_length, hlen, min_self]

theorem addSigned_refs_lt {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (addSigned (n := n) start sx xs sy ys).2.1 <
        start + (addSigned (n := n) start sx xs sy ys).1.length ∧
      ∀ i ∈ (addSigned (n := n) start sx xs sy ys).2.2,
        i < start + (addSigned (n := n) start sx xs sy ys).1.length := by
  let sum := addBits (n := n) (start + 1) (xs.zip ys) start
  let diff := absDifference (n := n) (start + 1 + sum.1.length) xs ys start
  let t := start + 1 + sum.1.length + diff.1.length
  have hm := muxBits_refs_lt (n := n) (t + 3) t ((diff.2.2 ++ [start]).zip sum.2)
  have hs : sum.1.length = 5 * xs.length := by simp [sum, addBits_gate_count, List.length_zip, hlen]
  have hd : diff.1.length = 19 * xs.length := absDifference_gate_count _ _ _ _ hlen
  have hsl : sum.2.length = xs.length + 1 := by simp [sum, addBits_word_length, List.length_zip, hlen]
  have hdl : diff.2.2.length = xs.length := absDifference_word_length _ _ _ _ hlen
  rw [addSigned_gate_count start sx xs sy ys hlen]
  constructor
  · change t + 2 < _
    dsimp only [t]
    omega
  · intro i hi
    have h := hm i hi
    simp only [List.length_zip, List.length_append, List.length_singleton, hsl, hdl,
      min_self, t] at h
    omega

set_option maxHeartbeats 2000000 in
/-- Exact signed addition, with arbitrary sharing of the input references. -/
theorem addSigned_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ)
    (hlen : xs.length = ys.length) (hsx : sx < vals.length) (hsy : sy < vals.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    let code := addSigned (n := n) vals.length sx xs sy ys
    signedValue (runFrom a vals code.1) code.2.1 code.2.2 =
      signedValue vals sx xs + signedValue vals sy ys := by
  let z := vals.length
  let v0 := vals ++ [false]
  let sum := addBits (n := n) (z + 1) (xs.zip ys) z
  let v1 := runFrom a v0 sum.1
  let diff := absDifference (n := n) (z + 1 + sum.1.length) xs ys z
  let v2 := runFrom a v1 diff.1
  let t := z + 1 + sum.1.length + diff.1.length
  let ctrl := signControl (n := n) t sx sy diff.2.1
  let v3 := runFrom a v2 ctrl
  let ps := (diff.2.2 ++ [z]).zip sum.2
  let mag := muxBits (n := n) (t + 3) t ps
  have hl0 : v0.length = z + 1 := by simp [v0, z]
  have hl1 : v1.length = z + 1 + sum.1.length := by rw [show v1 = runFrom a v0 sum.1 from rfl, runFrom_length, hl0]
  have hl2 : v2.length = t := by rw [show v2 = runFrom a v1 diff.1 from rfl, runFrom_length, hl1]
  have hl3 : v3.length = t + 3 := by rw [show v3 = runFrom a v2 ctrl from rfl, runFrom_length, hl2]; rfl
  have hz0 : z < v0.length := by rw [hl0]; omega
  have hz1 : z < v1.length := by rw [hl1]; omega
  have hz2 : z < v2.length := by rw [hl2]; dsimp [t]; omega
  have hzero0 : v0.getD z false = false := read_append_start vals [false]
  have hzero1 : v1.getD z false = false := by rw [read_runFrom_old a v0 sum.1 z hz0, hzero0]
  have hzero2 : v2.getD z false = false := by rw [read_runFrom_old a v1 diff.1 z hz1, hzero1]
  have hzero3 : v3.getD z false = false := by rw [read_runFrom_old a v2 ctrl z hz2, hzero2]
  have hx0 : ∀ i ∈ xs, i < v0.length := by intro i hi; have h := hx i hi; rw [hl0]; dsimp [z]; omega
  have hy0 : ∀ i ∈ ys, i < v0.length := by intro i hi; have h := hy i hi; rw [hl0]; dsimp [z]; omega
  have hx1 : ∀ i ∈ xs, i < v1.length := by intro i hi; have h := hx i hi; rw [hl1]; dsimp [z]; omega
  have hy1 : ∀ i ∈ ys, i < v1.length := by intro i hi; have h := hy i hi; rw [hl1]; dsimp [z]; omega
  have hsx2 : sx < v2.length := by rw [hl2]; dsimp [t, z]; omega
  have hsy2 : sy < v2.length := by rw [hl2]; dsimp [t, z]; omega
  have hxread0 : wordValue v0 xs = wordValue vals xs := wordValue_runFrom_old a vals [.cst false] xs hx
  have hyread0 : wordValue v0 ys = wordValue vals ys := wordValue_runFrom_old a vals [.cst false] ys hy
  have hxread1 : wordValue v1 xs = wordValue vals xs := by rw [wordValue_runFrom_old a v0 sum.1 xs hx0, hxread0]
  have hyread1 : wordValue v1 ys = wordValue vals ys := by rw [wordValue_runFrom_old a v0 sum.1 ys hy0, hyread0]
  have hsxread2 : v2.getD sx false = vals.getD sx false := by
    change (runFrom a (runFrom a v0 sum.1) diff.1).getD sx false = _
    rw [← runFrom_append, read_runFrom_old a v0 _ sx (by rw [hl0]; dsimp [z]; omega)]
    exact List.getD_append _ _ _ _ hsx
  have hsyread2 : v2.getD sy false = vals.getD sy false := by
    change (runFrom a (runFrom a v0 sum.1) diff.1).getD sy false = _
    rw [← runFrom_append, read_runFrom_old a v0 _ sy (by rw [hl0]; dsimp [z]; omega)]
    exact List.getD_append _ _ _ _ hsy
  have hp0 : ∀ p ∈ xs.zip ys, p.1 < v0.length ∧ p.2 < v0.length := by
    intro p hp
    exact ⟨hx0 _ (List.of_mem_zip hp).1, hy0 _ (List.of_mem_zip hp).2⟩
  have hsum := addBits_spec a v0 (xs.zip ys) z hp0 hz0
  rw [List.map_fst_zip (by omega), List.map_snd_zip (by omega),
    hzero0, Bool.toNat_false, Nat.add_zero, hxread0, hyread0, hl0] at hsum
  have hdiff := absDifference_spec a v1 xs ys z hlen hx1 hy1 hz1 hzero1
  dsimp only at hdiff
  rw [hxread1, hyread1, hl1] at hdiff
  change (if v2.getD diff.2.1 false then
    wordValue v2 diff.2.2 + wordValue vals xs = wordValue vals ys
    else wordValue v2 diff.2.2 + wordValue vals ys = wordValue vals xs) at hdiff
  have hrs := addBits_refs_lt (n := n) v0.length (xs.zip ys) z hz0
  rw [hl0] at hrs
  have hsumref1 : ∀ i ∈ sum.2, i < v1.length := by
    simpa only [hl1, sum, addBits_gate_count] using hrs
  have hsumref2 : ∀ i ∈ sum.2, i < v2.length := by
    intro i hi
    have h := hsumref1 i hi
    have hlen2 := runFrom_length a v1 diff.1
    change v2.length = _ at hlen2
    omega
  have hrd := absDifference_refs_lt (n := n) v1.length xs ys z hlen hz1
  rw [hl1] at hrd
  have hdref2 : ∀ i ∈ diff.2.2, i < v2.length := by simpa only [hl2, t, diff] using hrd.2
  have hbref2 : diff.2.1 < v2.length := by simpa only [hl2, t, diff] using hrd.1
  have hcontrol := runFrom_signControl a v2 sx sy diff.2.1 hsx2 hbref2
  rw [hl2] at hcontrol
  change v3 = _ at hcontrol
  have hflag : v3.getD t false = (vals.getD sx false ^^ vals.getD sy false) := by
    rw [hcontrol, ← hl2, read_append_start, hsxread2, hsyread2]
    rfl
  have hsign : v3.getD (t + 2) false = (vals.getD sx false ^^
      ((vals.getD sx false ^^ vals.getD sy false) && v2.getD diff.2.1 false)) := by
    rw [hcontrol, ← hl2, read_append_new, hsxread2, hsyread2]
    rfl
  have hsum3 : wordValue v3 sum.2 = wordValue vals xs + wordValue vals ys := by
    rw [wordValue_runFrom_old a v2 ctrl sum.2 hsumref2,
      wordValue_runFrom_old a v1 diff.1 sum.2 hsumref1]
    exact hsum
  have hdiff3 : wordValue v3 (diff.2.2 ++ [z]) = wordValue v2 diff.2.2 := by
    rw [wordValue_append, wordValue_runFrom_old a v2 ctrl diff.2.2 hdref2]
    simp only [wordValue, hzero3, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
  have hsl : sum.2.length = xs.length + 1 := by simp [sum, addBits_word_length, List.length_zip, hlen]
  have hdl : (diff.2.2 ++ [z]).length = xs.length + 1 := by
    simp only [List.length_append, List.length_singleton, diff, absDifference_word_length _ _ _ _ hlen]
  have hps : ∀ p ∈ ps, p.1 < v3.length ∧ p.2 < v3.length := by
    intro p hp
    obtain ⟨hd, hs⟩ := List.of_mem_zip hp
    have hs' := hsumref2 p.2 hs
    have hv : v2.length ≤ v3.length := by rw [hl2, hl3]; omega
    refine ⟨?_, by omega⟩
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | hd
    · exact lt_of_lt_of_le (hdref2 _ hd) hv
    · omega
  have hm := muxBits_spec a v3 t ps (by rw [hl3]; omega) hps
  rw [hl3, show ps.map Prod.fst = diff.2.2 ++ [z] from List.map_fst_zip (by omega),
    show ps.map Prod.snd = sum.2 from List.map_snd_zip (by omega), hflag, hdiff3, hsum3] at hm
  have hphase : runFrom a vals (addSigned (n := n) vals.length sx xs sy ys).1 =
      runFrom a v3 mag.1 := by
    change runFrom a vals ([.cst false] ++ sum.1 ++ diff.1 ++ ctrl ++ mag.1) = _
    simp only [runFrom_append]
    rfl
  dsimp only
  rw [hphase]
  change signedValue (runFrom a v3 mag.1) (t + 2) mag.2 = _
  rw [signedValue, read_runFrom_old a v3 mag.1 (t + 2) (by rw [hl3]; omega), hsign, hm]
  exact signed_sum_identity (vals.getD sx false) (vals.getD sy false)
    (v2.getD diff.2.1 false) (wordValue vals xs) (wordValue vals ys)
    (wordValue v2 diff.2.2) hdiff

/-- Subtract by a fresh sign-negation gate followed by the same signed adder. -/
def subtractSigned {n : ℕ} (start sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ) :
    List (CGate n) × (ℕ × List ℕ) :=
  let next := addSigned (start + 1) sx xs start ys
  (.un Bool.not sy :: next.1, next.2)

theorem subtractSigned_gate_count {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (subtractSigned (n := n) start sx xs sy ys).1.length = 27 * xs.length + 8 := by
  simp only [subtractSigned, List.length_cons, addSigned_gate_count _ _ _ _ _ hlen]

theorem subtractSigned_word_length {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (subtractSigned (n := n) start sx xs sy ys).2.2.length = xs.length + 1 :=
  addSigned_word_length (start + 1) sx xs start ys hlen

theorem subtractSigned_refs_lt {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (subtractSigned (n := n) start sx xs sy ys).2.1 <
        start + (subtractSigned (n := n) start sx xs sy ys).1.length ∧
      ∀ i ∈ (subtractSigned (n := n) start sx xs sy ys).2.2,
        i < start + (subtractSigned (n := n) start sx xs sy ys).1.length := by
  have h := addSigned_refs_lt (n := n) (start + 1) sx xs start ys hlen
  simpa only [subtractSigned, List.length_cons, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

theorem subtractSigned_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ)
    (hlen : xs.length = ys.length) (hsx : sx < vals.length) (_hsy : sy < vals.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    let code := subtractSigned (n := n) vals.length sx xs sy ys
    signedValue (runFrom a vals code.1) code.2.1 code.2.2 =
      signedValue vals sx xs - signedValue vals sy ys := by
  let v := vals ++ [!vals.getD sy false]
  have hl : v.length = vals.length + 1 := by simp [v]
  have hx' : ∀ i ∈ xs, i < v.length := by intro i hi; have h := hx i hi; rw [hl]; omega
  have hy' : ∀ i ∈ ys, i < v.length := by intro i hi; have h := hy i hi; rw [hl]; omega
  have h := addSigned_spec a v sx xs vals.length ys hlen (by rw [hl]; omega)
    (by rw [hl]; omega) hx' hy'
  have hxval : signedValue v sx xs = signedValue vals sx xs :=
    signedValue_runFrom_old a vals [.un Bool.not sy] sx xs hsx hx
  have hymag : wordValue v ys = wordValue vals ys :=
    wordValue_runFrom_old a vals [.un Bool.not sy] ys hy
  have hyval : signedValue v vals.length ys = -signedValue vals sy ys := by
    simp only [signedValue, show v.getD vals.length false = !vals.getD sy false from
      read_append_start vals _, hymag]
    cases vals.getD sy false <;> simp [signedMagnitude]
  dsimp only at h
  rw [hl, hxval, hyval] at h
  simpa only [subtractSigned, runFrom, evalGate, sub_eq_add_neg] using h

private def signedThree (subtract : Bool) (sx : Bool) (xs : List Bool)
    (sy : Bool) (ys : List Bool) : ℤ :=
  let vals := (sx :: xs) ++ (sy :: ys)
  let code := if subtract then subtractSigned (n := 0) vals.length 0 [1, 2, 3] 4 [5, 6, 7]
    else addSigned (n := 0) vals.length 0 [1, 2, 3] 4 [5, 6, 7]
  signedValue (runFrom (fun i => Fin.elim0 i) vals code.1) code.2.1 code.2.2

set_option maxRecDepth 100000 in
example : signedThree false false [true, true, true] false [true, true, true] = 14 := by decide
set_option maxRecDepth 100000 in
example : signedThree false true [true, true, true] true [true, true, true] = -14 := by decide
set_option maxRecDepth 100000 in
example : signedThree false true [true, false, true] false [true, true, false] = -2 := by decide
set_option maxRecDepth 100000 in
example : signedThree true false [true, true, false] true [true, false, true] = 8 := by decide
set_option maxRecDepth 100000 in
example : signedThree false true [true, false, true] false [true, false, true] = 0 := by decide

end GodMoveSignedArithmetic

#print axioms GodMoveSignedArithmetic.absDifference_spec
#print axioms GodMoveSignedArithmetic.absDifference_gate_count
#print axioms GodMoveSignedArithmetic.addSigned_gate_count
#print axioms GodMoveSignedArithmetic.addSigned_word_length
#print axioms GodMoveSignedArithmetic.addSigned_refs_lt
#print axioms GodMoveSignedArithmetic.addSigned_spec
#print axioms GodMoveSignedArithmetic.subtractSigned_gate_count
#print axioms GodMoveSignedArithmetic.subtractSigned_word_length
#print axioms GodMoveSignedArithmetic.subtractSigned_refs_lt
#print axioms GodMoveSignedArithmetic.subtractSigned_spec
