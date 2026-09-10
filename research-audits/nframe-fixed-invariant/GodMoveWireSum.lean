import GodMoveControlledWord

/-!
# Exact accumulation of binary weights controlled by existing wires

Each coefficient word is gated by its supplied Boolean wire. Full-carry
addition and padding by a known false wire give exact natural-number sums,
without overflow assumptions. The output width is the total supplied bit
count plus the number of terms; the emitted gate count is polynomial in those
explicit input sizes. No bound on upstream coefficient discovery is assumed.
-/

namespace GodMoveWireSum

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open GodMoveBinaryAdder GodMoveControlledWord GodMoveSignedBinary

abbrev Term := ℕ × List Bool

def totalBits (terms : List Term) : ℕ := (terms.map (fun t => t.2.length)).sum

def value (vals : List Bool) (terms : List Term) : ℕ :=
  (terms.map (fun t => if vals.getD t.1 false then bitsValue t.2 else 0)).sum

def paddedPairs (falseRef : ℕ) (xs ys : List ℕ) : List (ℕ × ℕ) :=
  (xs ++ List.replicate ys.length falseRef).zip (ys ++ List.replicate xs.length falseRef)

theorem paddedPairs_length (falseRef : ℕ) (xs ys : List ℕ) :
    (paddedPairs falseRef xs ys).length = xs.length + ys.length := by
  simp [paddedPairs, Nat.add_comm]

theorem paddedPairs_fst (falseRef : ℕ) (xs ys : List ℕ) :
    (paddedPairs falseRef xs ys).map Prod.fst = xs ++ List.replicate ys.length falseRef := by
  apply List.map_fst_zip
  simp [Nat.add_comm]

theorem paddedPairs_snd (falseRef : ℕ) (xs ys : List ℕ) :
    (paddedPairs falseRef xs ys).map Prod.snd = ys ++ List.replicate xs.length falseRef := by
  apply List.map_snd_zip
  simp [Nat.add_comm]

theorem paddedPairs_refs (falseRef bound : ℕ) (xs ys : List ℕ)
    (hz : falseRef < bound) (hx : ∀ i ∈ xs, i < bound) (hy : ∀ i ∈ ys, i < bound) :
    ∀ p ∈ paddedPairs falseRef xs ys, p.1 < bound ∧ p.2 < bound := by
  intro p hp
  obtain ⟨hpx, hpy⟩ := List.of_mem_zip hp
  constructor
  · rcases List.mem_append.mp hpx with h | h
    · exact hx _ h
    · have he := List.eq_of_mem_replicate h
      simpa only [he] using hz
  · rcases List.mem_append.mp hpy with h | h
    · exact hy _ h
    · have he := List.eq_of_mem_replicate h
      simpa only [he] using hz

theorem wordValue_replicate_zero (vals : List Bool) (falseRef k : ℕ)
    (hz : vals.getD falseRef false = false) : wordValue vals (List.replicate k falseRef) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, wordValue, hz, ih, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

theorem wordValue_pad_zero (vals : List Bool) (xs : List ℕ) (falseRef k : ℕ)
    (hz : vals.getD falseRef false = false) :
    wordValue vals (xs ++ List.replicate k falseRef) = wordValue vals xs := by
  induction xs with
  | nil => exact wordValue_replicate_zero vals falseRef k hz
  | cons x xs ih => simp [wordValue, ih]

theorem paddedPairs_values (vals : List Bool) (falseRef : ℕ) (xs ys : List ℕ)
    (hz : vals.getD falseRef false = false) :
    wordValue vals ((paddedPairs falseRef xs ys).map Prod.fst) = wordValue vals xs ∧
    wordValue vals ((paddedPairs falseRef xs ys).map Prod.snd) = wordValue vals ys := by
  rw [paddedPairs_fst, paddedPairs_snd]
  exact ⟨wordValue_pad_zero vals xs falseRef _ hz, wordValue_pad_zero vals ys falseRef _ hz⟩

/-- Compile from the tail, retaining every final carry. `falseRef` names a false
wire preceding `start`, and every term selector must precede `start`. -/
def sumTerms {n : ℕ} (start falseRef : ℕ) : List Term → List (CGate n) × List ℕ
  | [] => ([], [])
  | t :: ts =>
      let rest := sumTerms start falseRef ts
      let word := controlledWord (start + rest.1.length) t.1 t.2
      let pairs := paddedPairs falseRef rest.2 word.2
      let addition := addBits (start + rest.1.length + word.1.length) pairs falseRef
      ((rest.1 ++ word.1) ++ addition.1, addition.2)

theorem sumTerms_word_length {n : ℕ} (start falseRef : ℕ) (terms : List Term) :
    (sumTerms (n := n) start falseRef terms).2.length = totalBits terms + terms.length := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [sumTerms, addBits_word_length, paddedPairs_length,
      controlledWord_word_length, ih, totalBits, List.map_cons, List.sum_cons,
      List.length_cons]
    omega

theorem sumTerms_gate_count_le {n : ℕ} (start falseRef : ℕ) (terms : List Term) :
    (sumTerms (n := n) start falseRef terms).1.length ≤
      6 * terms.length * (totalBits terms + terms.length + 1) := by
  induction terms with
  | nil => simp [sumTerms]
  | cons t ts ih =>
    simp only [sumTerms, List.length_append, controlledWord_gate_count,
      addBits_gate_count, paddedPairs_length, controlledWord_word_length,
      sumTerms_word_length, List.length_cons]
    have hbits : totalBits (t :: ts) = t.2.length + totalBits ts := rfl
    rw [hbits]
    nlinarith [Nat.zero_le (ts.length * t.2.length)]

theorem sumTerms_refs_lt {n : ℕ} (start falseRef : ℕ) (terms : List Term)
    (hz : falseRef < start) : ∀ i ∈ (sumTerms (n := n) start falseRef terms).2,
      i < start + (sumTerms (n := n) start falseRef terms).1.length := by
  cases terms with
  | nil => simp [sumTerms]
  | cons t ts =>
    intro i hi
    have h := addBits_refs_lt (n := n)
      (start + (sumTerms (n := n) start falseRef ts).1.length +
        (controlledWord (n := n) (start + (sumTerms (n := n) start falseRef ts).1.length) t.1 t.2).1.length)
      (paddedPairs falseRef (sumTerms (n := n) start falseRef ts).2
        (controlledWord (n := n) (start + (sumTerms (n := n) start falseRef ts).1.length) t.1 t.2).2)
      falseRef (by omega) i hi
    simpa only [sumTerms, List.length_append, addBits_gate_count, Nat.add_assoc] using h

/-- Executing appended code preserves the value of every original selector. -/
theorem value_runFrom_old {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (code : List (CGate n)) (terms : List Term)
    (hterms : ∀ t ∈ terms, t.1 < vals.length) :
    value (runFrom a vals code) terms = value vals terms := by
  unfold value
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [read_runFrom_old a vals code t.1 (hterms t ht)]

/-- The generated word is the exact sum of all selected binary weights. -/
theorem sumTerms_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (falseRef : ℕ) (terms : List Term) (hz : falseRef < vals.length)
    (hzval : vals.getD falseRef false = false)
    (hterms : ∀ t ∈ terms, t.1 < vals.length) :
    wordValue (runFrom a vals (sumTerms (n := n) vals.length falseRef terms).1)
      (sumTerms (n := n) vals.length falseRef terms).2 = value vals terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    have ht := hterms t (by simp)
    have hts : ∀ u ∈ ts, u.1 < vals.length := fun u hu => hterms u (by simp [hu])
    have hrest := ih hts
    let rest := sumTerms (n := n) vals.length falseRef ts
    let rv := runFrom a vals rest.1
    have hrvlen : rv.length = vals.length + rest.1.length := runFrom_length _ _ _
    let word := controlledWord (n := n) rv.length t.1 t.2
    let cv := runFrom a rv word.1
    have hcvlen : cv.length = rv.length + word.1.length := runFrom_length _ _ _
    have hzeroRV : falseRef < rv.length := by rw [hrvlen]; omega
    have hzeroCV : falseRef < cv.length := by rw [hcvlen]; omega
    have hzeroRVval : rv.getD falseRef false = false :=
      (read_runFrom_old a vals rest.1 falseRef hz).trans hzval
    have hzeroCVval : cv.getD falseRef false = false :=
      (read_runFrom_old a rv word.1 falseRef hzeroRV).trans hzeroRVval
    have hrestrefs : ∀ i ∈ rest.2, i < rv.length := by
      rw [hrvlen]
      exact sumTerms_refs_lt vals.length falseRef ts hz
    have hwordrefs : ∀ i ∈ word.2, i < cv.length := by
      rw [hcvlen, show word.1.length = t.2.length from controlledWord_gate_count _ _ _]
      exact controlledWord_refs_lt rv.length t.1 t.2
    have hpairs := paddedPairs_refs falseRef cv.length rest.2 word.2 hzeroCV
      (fun i hi => (hrestrefs i hi).trans_le (by rw [hcvlen]; omega)) hwordrefs
    have hadd := addBits_spec a cv (paddedPairs falseRef rest.2 word.2) falseRef hpairs hzeroCV
    rw [(paddedPairs_values cv falseRef rest.2 word.2 hzeroCVval).1,
      (paddedPairs_values cv falseRef rest.2 word.2 hzeroCVval).2, hzeroCVval] at hadd
    have hrvalue : wordValue cv rest.2 = value vals ts := by
      rw [wordValue_runFrom_old a rv word.1 rest.2 hrestrefs]
      exact hrest
    have hwvalue : wordValue cv word.2 = if vals.getD t.1 false then bitsValue t.2 else 0 := by
      have hword := controlledWord_spec a rv t.1 t.2 (by rw [hrvlen]; omega)
      change wordValue cv word.2 = _ at hword
      rw [read_runFrom_old a vals rest.1 t.1 ht] at hword
      exact hword
    rw [hrvalue, hwvalue] at hadd
    change wordValue
      (runFrom a vals ((rest.1 ++
        (controlledWord (n := n) (vals.length + rest.1.length) t.1 t.2).1) ++
        (addBits (n := n) (vals.length + rest.1.length +
          (controlledWord (n := n) (vals.length + rest.1.length) t.1 t.2).1.length)
          (paddedPairs falseRef rest.2
            (controlledWord (n := n) (vals.length + rest.1.length) t.1 t.2).2) falseRef).1))
      (addBits (n := n) (vals.length + rest.1.length +
        (controlledWord (n := n) (vals.length + rest.1.length) t.1 t.2).1.length)
        (paddedPairs falseRef rest.2
          (controlledWord (n := n) (vals.length + rest.1.length) t.1 t.2).2) falseRef).2 = _
    rw [← hrvlen]
    change wordValue
      (runFrom a vals ((rest.1 ++ word.1) ++
        (addBits (n := n) (rv.length + word.1.length) (paddedPairs falseRef rest.2 word.2) falseRef).1))
      (addBits (n := n) (rv.length + word.1.length) (paddedPairs falseRef rest.2 word.2) falseRef).2 = _
    rw [← hcvlen, runFrom_append, runFrom_append]
    simpa only [value, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.add_zero,
      Nat.add_comm, Nat.zero_add] using hadd

end GodMoveWireSum

#print axioms GodMoveWireSum.paddedPairs_values
#print axioms GodMoveWireSum.sumTerms_word_length
#print axioms GodMoveWireSum.sumTerms_gate_count_le
#print axioms GodMoveWireSum.sumTerms_refs_lt
#print axioms GodMoveWireSum.sumTerms_spec
