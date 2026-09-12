import GodMoveBinaryDivisionCompileCost

/-!
# Counted generation of gcd and canonical normalization circuits

The compiler executes the bounded Euclidean unrolling through counted divider
and selector generators. It measures actual length traversals, offset creation
and gate-list copies. Erasure identifies the complete generated code and output
references with the preceding verified gcd/normalization circuits.

The counter uses the shared-index/list traversal model. No tape-machine
implementation or arbitrary-closure lowering cost is asserted here.
-/

namespace GodMoveBinaryNormalizationCompileCost

open GodMoveBooleanExecutionCost GodMoveBinaryPackingCost
open GodMoveBinaryMultiplyCompileCost GodMoveBinaryDivisionCompileCost
open GodMoveBinaryAdder GodMoveBinaryDivision GodMoveBinaryGCD
open GodMoveBinaryFractionNormalize
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

def pairsWith (z : ℕ) : List ℕ → Execution (List (ℕ × ℕ))
  | [] => ⟨[], 1⟩
  | i :: is =>
    let r := pairsWith z is
    ⟨(i, z) :: r.value, r.steps + 2⟩

theorem pairsWith_value (z : ℕ) (xs : List ℕ) :
    (pairsWith z xs).value = xs.map (fun i => (i, z)) := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp only [pairsWith, List.map_cons, ih]

theorem pairsWith_steps (z : ℕ) (xs : List ℕ) :
    (pairsWith z xs).steps = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp only [pairsWith, List.length_cons, ih]; omega

def nonzeroWordCounted {n : ℕ} (start : ℕ) (xs : List ℕ) :
    Execution (List (CGate n) × ℕ) :=
  let offset := addIndex start 1
  let pairs := pairsWith start xs
  let test := differentBitsCounted offset.value pairs.value
  ⟨(.cst false :: test.value.1, test.value.2), offset.steps + pairs.steps + test.steps + 3⟩

theorem nonzeroWordCounted_value {n : ℕ} (start : ℕ) (xs : List ℕ) :
    (nonzeroWordCounted (n := n) start xs).value = nonzeroWord start xs := by
  simp only [nonzeroWordCounted, addIndex_value, pairsWith_value,
    differentBitsCounted_value, nonzeroWord, List.singleton_append]

theorem nonzeroWordCounted_steps_le {n : ℕ} (start : ℕ) (xs : List ℕ) :
    (nonzeroWordCounted (n := n) start xs).steps ≤ 128 * (xs.length + 1) := by
  have h := differentBitsCounted_steps (n := n) (start + 1) (xs.map fun i => (i, start))
  simp only [List.length_map] at h
  simp only [nonzeroWordCounted, addIndex_steps, pairsWith_steps, addIndex_value,
    pairsWith_value]
  omega

def chooseWordsCounted {n : ℕ} (start sel : ℕ) (xs ys : List ℕ) :
    Execution (List (CGate n) × List ℕ) :=
  let pairs := zipCounted xs ys
  let code := muxBitsCounted start sel pairs.value
  ⟨code.value, pairs.steps + code.steps + 1⟩

theorem chooseWordsCounted_value {n : ℕ} (start sel : ℕ) (xs ys : List ℕ) :
    (chooseWordsCounted (n := n) start sel xs ys).value = chooseWords start sel xs ys := by
  simp only [chooseWordsCounted, zipCounted_value, muxBitsCounted_value, chooseWords]

theorem chooseWordsCounted_steps_le {n : ℕ} (start sel : ℕ) (xs ys : List ℕ) :
    (chooseWordsCounted (n := n) start sel xs ys).steps ≤ 128 * (xs.length + 1) := by
  have h := muxBitsCounted_steps (n := n) start sel (xs.zip ys)
  simp only [List.length_zip] at h
  simp only [chooseWordsCounted, zipCounted_value, zipCounted_steps]
  have hm := Nat.min_le_left xs.length ys.length
  omega

def freezeWordsCounted {n : ℕ} (start : ℕ) (xs ys rs : List ℕ) :
    Execution (List (CGate n) × (List ℕ × List ℕ)) :=
  let nz := nonzeroWordCounted start ys
  let nl := lengthFrom 0 nz.value.1
  let sx := addIndex start nl.value
  let mx := chooseWordsCounted sx.value nz.value.2 ys xs
  let ml := lengthFrom 0 mx.value.1
  let sy := addIndex sx.value ml.value
  let my := chooseWordsCounted sy.value nz.value.2 rs ys
  let front := appendList nz.value.1 mx.value.1
  let code := appendList front.value my.value.1
  ⟨(code.value, (mx.value.2, my.value.2)),
    nz.steps + nl.steps + sx.steps + mx.steps + ml.steps + sy.steps + my.steps +
      front.steps + code.steps + 1⟩

theorem freezeWordsCounted_value {n : ℕ} (start : ℕ) (xs ys rs : List ℕ) :
    (freezeWordsCounted (n := n) start xs ys rs).value = freezeWords start xs ys rs := by
  simp only [freezeWordsCounted, nonzeroWordCounted_value, lengthFrom_value, zero_add,
    addIndex_value, chooseWordsCounted_value, appendList_value, freezeWords, List.append_assoc]

theorem freezeWordsCounted_steps_le {n : ℕ} (start : ℕ) (xs ys rs : List ℕ)
    (hlen : xs.length = ys.length) (hrlen : rs.length = ys.length) :
    (freezeWordsCounted (n := n) start xs ys rs).steps ≤ 1024 * (xs.length + 1) ^ 2 := by
  have hn := nonzeroWordCounted_steps_le (n := n) start ys
  have hx := chooseWordsCounted_steps_le (n := n)
    (start + (nonzeroWord (n := n) start ys).1.length) (nonzeroWord (n := n) start ys).2 ys xs
  have hy := chooseWordsCounted_steps_le (n := n)
    (start + (nonzeroWord (n := n) start ys).1.length +
      (chooseWords (n := n) (start + (nonzeroWord (n := n) start ys).1.length)
        (nonzeroWord (n := n) start ys).2 ys xs).1.length)
    (nonzeroWord (n := n) start ys).2 rs ys
  simp only [freezeWordsCounted, lengthFrom_steps, lengthFrom_value, zero_add, addIndex_steps,
    addIndex_value, nonzeroWordCounted_value, chooseWordsCounted_value, appendList_steps,
    appendList_value, List.length_append, nonzeroWord_gate_count,
    chooseWords_gate_count _ _ _ _ hlen.symm]
  simp only [nonzeroWord_gate_count, chooseWords_gate_count _ _ _ _ hlen.symm] at hx hy
  rw [← hlen] at hn hx
  rw [hrlen, ← hlen] at hy
  rw [← hlen]
  nlinarith

def euclideanStepCounted {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    Execution (List (CGate n) × (List ℕ × List ℕ)) :=
  let d := divideWordsCounted start xs ys
  let dl := lengthFrom 0 d.value.1
  let nextStart := addIndex start dl.value
  let next := freezeWordsCounted nextStart.value xs ys d.value.2.2
  let code := appendList d.value.1 next.value.1
  ⟨(code.value, next.value.2), d.steps + dl.steps + nextStart.steps + next.steps + code.steps + 1⟩

theorem euclideanStepCounted_value {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    (euclideanStepCounted (n := n) start xs ys).value = euclideanStep start xs ys := by
  simp only [euclideanStepCounted, divideWordsCounted_value, lengthFrom_value, zero_add,
    addIndex_value, freezeWordsCounted_value, appendList_value, euclideanStep]

theorem euclideanStepCounted_steps_le {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (euclideanStepCounted (n := n) start xs ys).steps ≤ 4096 * (xs.length + 1) ^ 4 := by
  have hd := divideWordsCounted_steps_le (n := n) start xs ys hlen
  have hg := divideWords_gate_count (n := n) start xs ys hlen
  have hf := freezeWordsCounted_steps_le (n := n)
    (start + (divideWords (n := n) start xs ys).1.length) xs ys
    (divideWords (n := n) start xs ys).2.2 hlen
    ((divideWords_lengths (n := n) start xs ys hlen).2.trans hlen)
  have h24 : (xs.length + 1) ^ 2 ≤ (xs.length + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : 1 ≤ (xs.length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  simp only [euclideanStepCounted, lengthFrom_steps, lengthFrom_value, zero_add,
    addIndex_steps, addIndex_value, appendList_steps, divideWordsCounted_value]
  omega

def euclidWordsCounted {n : ℕ} : ℕ → ℕ → List ℕ → List ℕ →
    Execution (List (CGate n) × (List ℕ × List ℕ))
  | 0, _, xs, ys => ⟨([], (xs, ys)), 2⟩
  | fuel + 1, start, xs, ys =>
    let step := euclideanStepCounted start xs ys
    let len := lengthFrom 0 step.value.1
    let nextStart := addIndex start len.value
    let rest := euclidWordsCounted fuel nextStart.value step.value.2.1 step.value.2.2
    let code := appendList step.value.1 rest.value.1
    ⟨(code.value, rest.value.2), step.steps + len.steps + nextStart.steps + rest.steps + code.steps + 1⟩

theorem euclidWordsCounted_value {n : ℕ} (fuel start : ℕ) (xs ys : List ℕ) :
    (euclidWordsCounted (n := n) fuel start xs ys).value = euclidWords fuel start xs ys := by
  induction fuel generalizing start xs ys with
  | zero => rfl
  | succ fuel ih => simp only [euclidWordsCounted, euclideanStepCounted_value, lengthFrom_value,
      zero_add, addIndex_value, ih, appendList_value, euclidWords]

theorem euclidWordsCounted_steps_le {n : ℕ} (fuel start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (euclidWordsCounted (n := n) fuel start xs ys).steps ≤
      8192 * fuel * (xs.length + 1) ^ 4 + 2 := by
  induction fuel generalizing start xs ys with
  | zero => simp [euclidWordsCounted]
  | succ fuel ih =>
    have hl := euclideanStep_lengths (n := n) start xs ys hlen
    have hr := ih (start + (euclideanStep (n := n) start xs ys).1.length)
      (euclideanStep (n := n) start xs ys).2.1 (euclideanStep (n := n) start xs ys).2.2
      (hl.1.trans hl.2.symm)
    rw [hl.1] at hr
    have hs := euclideanStepCounted_steps_le (n := n) start xs ys hlen
    have hg : (euclideanStep (n := n) start xs ys).1.length ≤ 64 * (xs.length + 1) ^ 2 := by
      rw [euclideanStep_gate_count _ _ _ hlen]
      nlinarith
    have h24 : (xs.length + 1) ^ 2 ≤ (xs.length + 1) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have h4 : 1 ≤ (xs.length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    simp only [euclidWordsCounted, lengthFrom_steps, lengthFrom_value, zero_add,
      addIndex_steps, addIndex_value, appendList_steps, euclideanStepCounted_value]
    nlinarith

def gcdWordsCounted {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    Execution (List (CGate n) × List ℕ) :=
  let width := lengthFrom 0 xs
  let doubled := addIndex width.value width.value
  let fuel := addIndex doubled.value 1
  let r := euclidWordsCounted fuel.value start xs ys
  ⟨(r.value.1, r.value.2.1), width.steps + doubled.steps + fuel.steps + r.steps + 1⟩

theorem gcdWordsCounted_value {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    (gcdWordsCounted (n := n) start xs ys).value = gcdWords start xs ys := by
  simp only [gcdWordsCounted, lengthFrom_value, zero_add, addIndex_value,
    euclidWordsCounted_value, gcdWords, two_mul]

theorem gcdWordsCounted_steps_le {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (gcdWordsCounted (n := n) start xs ys).steps ≤ 32768 * (xs.length + 1) ^ 5 := by
  have hr := euclidWordsCounted_steps_le (n := n) (2 * xs.length + 1) start xs ys hlen
  have hb : 8192 * (2 * xs.length + 1) * (xs.length + 1) ^ 4 ≤
      16384 * (xs.length + 1) ^ 5 := by
    calc
      _ ≤ (8192 * (2 * (xs.length + 1))) * (xs.length + 1) ^ 4 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring
  have h15 : xs.length + 1 ≤ (xs.length + 1) ^ 5 := by
    calc
      _ = (xs.length + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  simp only [gcdWordsCounted, lengthFrom_steps, lengthFrom_value, zero_add,
    addIndex_steps, addIndex_value, ← two_mul]
  omega

def normalizeWordsCounted {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    Execution (List (CGate n) × (List ℕ × List ℕ)) :=
  let g := gcdWordsCounted start xs ys
  let gl := lengthFrom 0 g.value.1
  let ns := addIndex start gl.value
  let qn := divideWordsCounted ns.value xs g.value.2
  let nl := lengthFrom 0 qn.value.1
  let ds := addIndex ns.value nl.value
  let qd := divideWordsCounted ds.value ys g.value.2
  let front := appendList g.value.1 qn.value.1
  let code := appendList front.value qd.value.1
  ⟨(code.value, (qn.value.2.1, qd.value.2.1)),
    g.steps + gl.steps + ns.steps + qn.steps + nl.steps + ds.steps + qd.steps +
      front.steps + code.steps + 1⟩

theorem normalizeWordsCounted_value {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    (normalizeWordsCounted (n := n) start xs ys).value = normalizeWords start xs ys := by
  simp only [normalizeWordsCounted, gcdWordsCounted_value, lengthFrom_value, zero_add,
    addIndex_value, divideWordsCounted_value, appendList_value, normalizeWords]

theorem normalizeWordsCounted_steps_le {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (normalizeWordsCounted (n := n) start xs ys).steps ≤ 65536 * (xs.length + 1) ^ 5 := by
  let g := gcdWords (n := n) start xs ys
  let qn := divideWords (n := n) (start + g.1.length) xs g.2
  have hgl : g.2.length = xs.length := gcdWords_word_length start xs ys hlen
  have hg := gcdWordsCounted_steps_le (n := n) start xs ys hlen
  have hn := divideWordsCounted_steps_le (n := n) (start + g.1.length) xs g.2 hgl.symm
  have hd := divideWordsCounted_steps_le (n := n) (start + g.1.length + qn.1.length)
    ys g.2 (hlen.symm.trans hgl.symm)
  have hgg := gcdWords_gate_count (n := n) start xs ys hlen
  have hng := divideWords_gate_count (n := n) (start + g.1.length) xs g.2 hgl.symm
  rw [← hlen] at hd
  have h25 : (xs.length + 1) ^ 2 ≤ (xs.length + 1) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h35 : (xs.length + 1) ^ 3 ≤ (xs.length + 1) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h45 : (xs.length + 1) ^ 4 ≤ (xs.length + 1) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h5 : 1 ≤ (xs.length + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  change g.1.length ≤ _ at hgg
  change qn.1.length ≤ _ at hng
  simp only [normalizeWordsCounted, lengthFrom_steps, lengthFrom_value, zero_add,
    addIndex_steps, addIndex_value, appendList_steps, appendList_value, List.length_append,
    gcdWordsCounted_value, divideWordsCounted_value]
  change (gcdWordsCounted (n := n) start xs ys).steps +
    (2 * g.1.length + 1) + (g.1.length + 1) +
    (divideWordsCounted (n := n) (start + g.1.length) xs g.2).steps +
    (2 * qn.1.length + 1) + (qn.1.length + 1) +
    (divideWordsCounted (n := n) (start + g.1.length + qn.1.length) ys g.2).steps +
    (g.1.length + 1) + (g.1.length + qn.1.length + 1) + 1 ≤ _
  omega

end GodMoveBinaryNormalizationCompileCost

#print axioms GodMoveBinaryNormalizationCompileCost.nonzeroWordCounted_value
#print axioms GodMoveBinaryNormalizationCompileCost.nonzeroWordCounted_steps_le
#print axioms GodMoveBinaryNormalizationCompileCost.chooseWordsCounted_value
#print axioms GodMoveBinaryNormalizationCompileCost.freezeWordsCounted_value
#print axioms GodMoveBinaryNormalizationCompileCost.freezeWordsCounted_steps_le
#print axioms GodMoveBinaryNormalizationCompileCost.euclideanStepCounted_steps_le
#print axioms GodMoveBinaryNormalizationCompileCost.euclidWordsCounted_value
#print axioms GodMoveBinaryNormalizationCompileCost.euclidWordsCounted_steps_le
#print axioms GodMoveBinaryNormalizationCompileCost.gcdWordsCounted_value
#print axioms GodMoveBinaryNormalizationCompileCost.gcdWordsCounted_steps_le
#print axioms GodMoveBinaryNormalizationCompileCost.normalizeWordsCounted_value
#print axioms GodMoveBinaryNormalizationCompileCost.normalizeWordsCounted_steps_le
