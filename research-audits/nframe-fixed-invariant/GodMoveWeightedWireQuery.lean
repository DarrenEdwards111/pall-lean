import GodMoveWireSum
import GodMoveMachineCircuitOracle

/-!
# A concrete Boolean circuit for a signed weighted wire relation

The input contains actual source-wire references and explicit signed binary
coefficients. Positive and negative contributions are accumulated separately
by full-carry adders; a Boolean comparator detects their inequality. One
source circuit is retained with all sharing, and no assignments are enumerated.

The output is proved equivalent to nonvanishing of the integer weighted sum.
The gate bound is polynomial in source gates, term count, and supplied bit
payload. It does not supply a precision bound for upstream rational arithmetic.
-/

namespace GodMoveWeightedWireQuery

open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer
open GodMoveBinaryAdder GodMoveSignedBinary GodMoveWireSum
open GodMoveMachineCircuitOracle

abbrev WeightedTerm (s : ℕ) := Fin s × SignedBits

def termBits {s : ℕ} (terms : List (WeightedTerm s)) : ℕ :=
  (terms.map (fun t => t.2.bits.length)).sum

def termValue {s : ℕ} (vals : List Bool) (terms : List (WeightedTerm s)) : ℤ :=
  (terms.map (fun t => if vals.getD t.1.val false then signedValue t.2 else 0)).sum

def unsignedTerms {s : ℕ} (negative : Bool) (terms : List (WeightedTerm s)) : List Term :=
  terms.map (fun t => (t.1.val, if t.2.negative = negative then t.2.bits else []))

theorem unsignedTerms_length {s : ℕ} (negative : Bool) (terms : List (WeightedTerm s)) :
    (unsignedTerms negative terms).length = terms.length := by simp [unsignedTerms]

theorem unsignedTerms_bits_le {s : ℕ} (negative : Bool) (terms : List (WeightedTerm s)) :
    totalBits (unsignedTerms negative terms) ≤ termBits terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    by_cases h : t.2.negative = negative <;>
      simp only [unsignedTerms, List.map_cons, totalBits, List.sum_cons, termBits,
        h, ↓reduceIte, List.length_nil] at * <;> omega

theorem unsignedTerms_refs {s bound : ℕ} (negative : Bool) (terms : List (WeightedTerm s))
    (hs : s ≤ bound) : ∀ t ∈ unsignedTerms negative terms, t.1 < bound := by
  intro t ht
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
  exact u.1.isLt.trans_le hs

/-- Signed arithmetic equals the difference of the two exact natural sums. -/
theorem termValue_eq_sub {s : ℕ} (vals : List Bool) (terms : List (WeightedTerm s)) :
    termValue vals terms =
      (value vals (unsignedTerms false terms) : ℤ) - value vals (unsignedTerms true terms) := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    cases hsign : t.2.negative <;> cases hbit : vals.getD t.1.val false <;>
      simp only [termValue, unsignedTerms, value, List.map_cons, List.sum_cons,
        signedValue, hsign, hbit, Bool.false_eq_true, ↓reduceIte,
        Bool.true_eq, bitsValue, Nat.cast_add, Nat.cast_zero] at * <;> omega

/-- Return the appended relation code and its output reference. The caller
supplies one already-existing false wire for padding and adder carries. -/
def relationCode {n s : ℕ} (start falseRef : ℕ) (terms : List (WeightedTerm s)) :
    List (CGate n) × ℕ :=
  let pos := sumTerms start falseRef (unsignedTerms false terms)
  let neg := sumTerms (start + pos.1.length) falseRef (unsignedTerms true terms)
  let diff := differentBits (start + pos.1.length + neg.1.length)
    (paddedPairs falseRef pos.2 neg.2)
  ((pos.1 ++ neg.1) ++ diff.1, diff.2)

theorem relationCode_ref_lt {n s : ℕ} (start falseRef : ℕ)
    (terms : List (WeightedTerm s)) :
    (relationCode (n := n) start falseRef terms).2 <
      start + (relationCode (n := n) start falseRef terms).1.length := by
  let pos := sumTerms (n := n) start falseRef (unsignedTerms false terms)
  let neg := sumTerms (n := n) (start + pos.1.length) falseRef (unsignedTerms true terms)
  have h := differentBits_ref_lt (n := n) (start + pos.1.length + neg.1.length)
    (paddedPairs falseRef pos.2 neg.2)
  simpa only [relationCode, List.length_append, Nat.add_assoc] using h

theorem relationCode_gate_count_le {n s : ℕ} (start falseRef : ℕ)
    (terms : List (WeightedTerm s)) :
    (relationCode (n := n) start falseRef terms).1.length ≤
      12 * terms.length * (termBits terms + terms.length + 1) +
        4 * (termBits terms + terms.length) + 1 := by
  let pos := sumTerms (n := n) start falseRef (unsignedTerms false terms)
  let neg := sumTerms (n := n) (start + pos.1.length) falseRef (unsignedTerms true terms)
  have hp := sumTerms_gate_count_le (n := n) start falseRef (unsignedTerms false terms)
  have hn := sumTerms_gate_count_le (n := n) (start + pos.1.length) falseRef
    (unsignedTerms true terms)
  have hpb := unsignedTerms_bits_le false terms
  have hnb := unsignedTerms_bits_le true terms
  simp only [unsignedTerms_length] at hp hn
  have hgp : pos.1.length ≤ 6 * terms.length * (termBits terms + terms.length + 1) :=
    hp.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right hpb _) _))
  have hgn : neg.1.length ≤ 6 * terms.length * (termBits terms + terms.length + 1) :=
    hn.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right hnb _) _))
  have hwp : pos.2.length ≤ termBits terms + terms.length := by
    simpa only [pos, sumTerms_word_length, unsignedTerms_length] using Nat.add_le_add_right hpb terms.length
  have hwn : neg.2.length ≤ termBits terms + terms.length := by
    simpa only [neg, sumTerms_word_length, unsignedTerms_length] using Nat.add_le_add_right hnb terms.length
  change ((pos.1 ++ neg.1) ++
    (differentBits (n := n) (start + pos.1.length + neg.1.length)
      (paddedPairs falseRef pos.2 neg.2)).1).length ≤ _
  rw [List.length_append, List.length_append, differentBits_gate_count, paddedPairs_length]
  nlinarith only [hgp, hgn, hwp, hwn]

/-- The finite arithmetic circuit decides nonzero signed sum on any current
wire state containing the supplied source indices and a valid false wire. -/
theorem relationCode_spec {n s : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (falseRef : ℕ) (terms : List (WeightedTerm s)) (hs : s ≤ vals.length)
    (hz : falseRef < vals.length) (hzval : vals.getD falseRef false = false) :
    (runFrom a vals (relationCode (n := n) vals.length falseRef terms).1).getD
      (relationCode (n := n) vals.length falseRef terms).2 false =
      decide (termValue vals terms ≠ 0) := by
  let pos := sumTerms (n := n) vals.length falseRef (unsignedTerms false terms)
  let pv := runFrom a vals pos.1
  have hplen : pv.length = vals.length + pos.1.length := runFrom_length _ _ _
  let neg := sumTerms (n := n) pv.length falseRef (unsignedTerms true terms)
  let nv := runFrom a pv neg.1
  have hnlen : nv.length = pv.length + neg.1.length := runFrom_length _ _ _
  have hzp : falseRef < pv.length := by rw [hplen]; omega
  have hzn : falseRef < nv.length := by rw [hnlen]; omega
  have hzpval : pv.getD falseRef false = false :=
    (read_runFrom_old a vals pos.1 falseRef hz).trans hzval
  have hznval : nv.getD falseRef false = false :=
    (read_runFrom_old a pv neg.1 falseRef hzp).trans hzpval
  have hprefs : ∀ i ∈ pos.2, i < pv.length := by
    rw [hplen]
    exact sumTerms_refs_lt _ _ _ hz
  have hnrefs : ∀ i ∈ neg.2, i < nv.length := by
    rw [hnlen]
    exact sumTerms_refs_lt _ _ _ hzp
  have hpair := paddedPairs_refs falseRef nv.length pos.2 neg.2 hzn
    (fun i hi => (hprefs i hi).trans_le (by rw [hnlen]; omega)) hnrefs
  have hpval : wordValue nv pos.2 = value vals (unsignedTerms false terms) := by
    rw [wordValue_runFrom_old a pv neg.1 pos.2 hprefs]
    exact sumTerms_spec a vals falseRef _ hz hzval (unsignedTerms_refs false terms hs)
  have hnval : wordValue nv neg.2 = value vals (unsignedTerms true terms) := by
    have h := sumTerms_spec a pv falseRef (unsignedTerms true terms) hzp hzpval
      (unsignedTerms_refs true terms (by rw [hplen]; omega))
    rw [value_runFrom_old a vals pos.1 _ (unsignedTerms_refs true terms hs)] at h
    exact h
  have hdiff := differentBits_spec a nv (paddedPairs falseRef pos.2 neg.2) hpair
  rw [(paddedPairs_values nv falseRef pos.2 neg.2 hznval).1,
    (paddedPairs_values nv falseRef pos.2 neg.2 hznval).2, hpval, hnval] at hdiff
  have hneq : (value vals (unsignedTerms false terms) ≠ value vals (unsignedTerms true terms)) ↔
      termValue vals terms ≠ 0 := by
    rw [termValue_eq_sub]
    omega
  simp only [hneq] at hdiff
  change (runFrom a vals ((pos.1 ++
    (sumTerms (n := n) (vals.length + pos.1.length) falseRef (unsignedTerms true terms)).1) ++
    (differentBits (n := n) (vals.length + pos.1.length +
      (sumTerms (n := n) (vals.length + pos.1.length) falseRef (unsignedTerms true terms)).1.length)
      (paddedPairs falseRef pos.2
        (sumTerms (n := n) (vals.length + pos.1.length) falseRef (unsignedTerms true terms)).2)).1)).getD
    (differentBits (n := n) (vals.length + pos.1.length +
      (sumTerms (n := n) (vals.length + pos.1.length) falseRef (unsignedTerms true terms)).1.length)
      (paddedPairs falseRef pos.2
        (sumTerms (n := n) (vals.length + pos.1.length) falseRef (unsignedTerms true terms)).2)).2 false = _
  rw [← hplen]
  change (runFrom a vals ((pos.1 ++ neg.1) ++
    (differentBits (n := n) (pv.length + neg.1.length) (paddedPairs falseRef pos.2 neg.2)).1)).getD
    (differentBits (n := n) (pv.length + neg.1.length) (paddedPairs falseRef pos.2 neg.2)).2 false = _
  rw [← hnlen, runFrom_append, runFrom_append]
  exact hdiff

/-- Source sharing is retained. A fresh false wire supplies padding, and the
final identity gate makes the relation answer the circuit's actual output. -/
def weightedQuery {n : ℕ} (c : List (CGate n)) (terms : List (WeightedTerm c.length)) :
    List (CGate n) :=
  let relation := relationCode (n := n) (c.length + 1) c.length terms
  ((c ++ [.cst false]) ++ relation.1) ++ [.un id relation.2]

theorem termValue_runFrom_old {n s : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (code : List (CGate n)) (terms : List (WeightedTerm s)) (hs : s ≤ vals.length) :
    termValue (runFrom a vals code) terms = termValue vals terms := by
  unfold termValue
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [read_runFrom_old a vals code t.1.val (t.1.isLt.trans_le hs)]

/-- The final Boolean output is exactly the nonzero weighted-wire test. -/
theorem weightedQuery_output {n : ℕ} (c : List (CGate n))
    (terms : List (WeightedTerm c.length)) (a : Fin n → Bool) :
    output (weightedQuery c terms) a = decide (termValue (runFrom a [] c) terms ≠ 0) := by
  let vals := runFrom a [] c
  have hvals : vals.length = c.length := by simp [vals, runFrom_length]
  let base := vals ++ [false]
  have hbase : base.length = c.length + 1 := by simp [base, hvals]
  let relation := relationCode (n := n) (c.length + 1) c.length terms
  have hfalse : base.getD c.length false = false := by
    rw [← hvals]
    exact read_append_start vals [false]
  have hspec := relationCode_spec a base c.length terms (by rw [hbase]; omega)
    (by rw [hbase]; omega) hfalse
  rw [hbase] at hspec
  have hvalue : termValue base terms = termValue vals terms := by
    exact termValue_runFrom_old a vals [.cst false] terms (by rw [hvals])
  rw [hvalue] at hspec
  have hlen : (runFrom a base relation.1).length = c.length + 1 + relation.1.length := by
    rw [runFrom_length, hbase]
  unfold output weightedQuery
  simp only [List.length_append, List.length_singleton, runFrom_append, runFrom, evalGate,
    id_eq]
  change ((runFrom a base relation.1) ++ [(runFrom a base relation.1).getD relation.2 false]).getD
    (c.length + 1 + relation.1.length + 1 - 1) false = _
  rw [show c.length + 1 + relation.1.length + 1 - 1 =
    (runFrom a base relation.1).length by omega]
  rw [read_append_start]
  exact hspec

/-- Gate size is polynomial in the actual supplied coefficient payload. -/
theorem weightedQuery_gate_count_le {n : ℕ} (c : List (CGate n))
    (terms : List (WeightedTerm c.length)) :
    (weightedQuery c terms).length ≤
      32 * (c.length + terms.length + termBits terms + 1) ^ 2 := by
  have h := relationCode_gate_count_le (n := n) (c.length + 1) c.length terms
  simp only [weightedQuery, List.length_append, List.length_singleton]
  nlinarith [Nat.zero_le (c.length * terms.length),
    Nat.zero_le (c.length * termBits terms), Nat.zero_le (terms.length * termBits terms)]

/-- The actual supplied SAT machine decides existence of a violating source
assignment via this concrete Boolean circuit and its Tseitin encoding. -/
theorem machine_query_correct (M : ComposableMachine.Machine) (T : ℕ → ℕ)
    (hD : ComposableMachine.Decides M SeparationTarget.SATLang T)
    {n : ℕ} (c : List (CGate n)) (terms : List (WeightedTerm c.length)) :
    circuitSAT M T (weightedQuery c terms) = true ↔
      ∃ a : Fin n → Bool, termValue (runFrom a [] c) terms ≠ 0 := by
  rw [circuitSAT_correct M T hD]
  apply exists_congr
  intro a
  rw [weightedQuery_output, decide_eq_true_eq]

private def carryCircuit : List (CGate 2) := [.var 0, .var 1, .cst true]

private def carryTerms : List (WeightedTerm carryCircuit.length) :=
  [(⟨0, by decide⟩, encodeInt 3 3),
   (⟨1, by decide⟩, encodeInt 3 3),
   (⟨2, by decide⟩, encodeInt 3 (-6))]

private def cancellingTerms : List (WeightedTerm carryCircuit.length) :=
  [(⟨0, by decide⟩, encodeInt 4 7), (⟨0, by decide⟩, encodeInt 4 (-7))]

/-- info: [true, true, true, false] -/
#guard_msgs in
#eval (GodMoveBooleanWireTable.allAssignments 2).map
  (output (weightedQuery carryCircuit carryTerms))

/-- info: [false, false, false, false] -/
#guard_msgs in
#eval (GodMoveBooleanWireTable.allAssignments 2).map
  (output (weightedQuery carryCircuit cancellingTerms))

end GodMoveWeightedWireQuery

#print axioms GodMoveWeightedWireQuery.termValue_eq_sub
#print axioms GodMoveWeightedWireQuery.relationCode_gate_count_le
#print axioms GodMoveWeightedWireQuery.relationCode_spec
#print axioms GodMoveWeightedWireQuery.weightedQuery_output
#print axioms GodMoveWeightedWireQuery.weightedQuery_gate_count_le
#print axioms GodMoveWeightedWireQuery.machine_query_correct
