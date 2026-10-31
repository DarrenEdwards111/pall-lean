import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPBoundaryFoolingWidthLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPrefixCNFReduction
import Mathlib.Data.List.OfFn

/-!
# A genuine SAT family with exponential width at one fixed boundary cut

This file transports the constructed boundary-fooling lower bound to **actual CNF satisfiability** without an
exact-recovery socket.  Given two `n`-bit blocks `a` and `b`, `equalityCNF a b` contains two local banks of unit
clauses over the same `n` variables: the first bank forces the assignment to be `a`, and the second forces it to
be `b`.  Consequently the formula is satisfiable exactly when `a = b`.

The reduction is local and does not insert a precomputed answer.  It yields a real SAT subfamily whose
satisfiability matrix is equality, so every deterministic decider factoring through one state after the first
block needs at least `2^n` states.

## Honest scope

This is a restricted one-way-communication / OBDD-cut lower bound for SAT.  The formulas are easy and a general
machine compares the two blocks in linear time.  Thus the theorem does not imply `SAT ∉ P` or `P ≠ NP`; it
pinpoints why raw boundary-state cardinality is not a P-wide resource measure.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB

/-- A CNF whose first unit-clause bank forces `a` and whose second bank forces `b`. -/
def equalityCNF {n : Nat} (a b : Fin n → Bool) : CNF where
  vars := n
  clauses :=
    prefixUnitClauses (List.ofFn a) ++ prefixUnitClauses (List.ofFn b)

/-- An extension of a prefix with the same length is exactly that prefix. -/
theorem eq_prefix_of_extends_of_length_eq {p s : RawAssignment}
    (h : ExtendsPrefix p s) (hlen : s.length = p.length) : s = p := by
  rcases h with ⟨tail, rfl⟩
  have htail : tail.length = 0 := by
    simpa using hlen
  have : tail = [] := List.eq_nil_of_length_eq_zero htail
  simp [this]

/-- `List.ofFn` reflects equality of fixed-length Boolean vectors. -/
theorem eq_of_ofFn_eq {n : Nat} {a b : Fin n → Bool}
    (h : List.ofFn a = List.ofFn b) : a = b := by
  funext i
  have hi : i.val < (List.ofFn a).length := by simpa using i.isLt
  have hj : i.val < (List.ofFn b).length := by simpa using i.isLt
  have hget := congrArg (fun l : List Bool => l.getD i.val false) h
  simpa [List.getD_eq_getElem?_getD, hi, hj] using hget

/-- The two local unit-clause banks are jointly satisfiable exactly when their bit blocks agree. -/
theorem equalityCNF_satisfiable_iff {n : Nat} (a b : Fin n → Bool) :
    Satisfiable (equalityCNF a b) ↔ a = b := by
  constructor
  · rintro ⟨s, hlen, heval⟩
    have hall :
        (prefixUnitClauses (List.ofFn a)).all (fun c => Clause.eval s c) = true ∧
          (prefixUnitClauses (List.ofFn b)).all (fun c => Clause.eval s c) = true := by
      simpa [equalityCNF, CNF.eval, List.all_append, Bool.and_eq_true] using heval
    have haExt : ExtendsPrefix (List.ofFn a) s :=
      extends_of_prefixUnitClauses_all_true hall.1
    have hbExt : ExtendsPrefix (List.ofFn b) s :=
      extends_of_prefixUnitClauses_all_true hall.2
    have hsa : s = List.ofFn a :=
      eq_prefix_of_extends_of_length_eq haExt (by simpa using hlen)
    have hsb : s = List.ofFn b :=
      eq_prefix_of_extends_of_length_eq hbExt (by simpa using hlen)
    exact eq_of_ofFn_eq (hsa.symm.trans hsb)
  · intro hab
    subst b
    refine ⟨List.ofFn a, by simp [equalityCNF], ?_⟩
    have hforce :
        (prefixUnitClauses (List.ofFn a)).all
          (fun c => Clause.eval (List.ofFn a) c) = true :=
      prefixUnitClauses_all_true_of_extends ⟨[], by simp⟩
    simp [equalityCNF, CNF.eval, hforce]

/-- A boundary decider is correct for the concrete SAT family. -/
def ComputesEqualitySAT {n : Nat} (D : LayeredBoundaryDecider n n) : Prop :=
  ∀ a b, D.eval a b = true ↔ Satisfiable (equalityCNF a b)

/-- Correctness for this actual SAT family is exactly correctness for the equality matrix. -/
theorem computes_EQ_of_computesEqualitySAT {n : Nat} (D : LayeredBoundaryDecider n n)
    (hSAT : ComputesEqualitySAT D) :
    ∀ a b, D.eval a b = EQ n a b := by
  intro a b
  apply Bool.eq_iff_iff.mpr
  rw [hSAT a b, equalityCNF_satisfiable_iff]
  simp [EQ]

/-- **Actual SAT-family width lower bound.**  Any one-cut boundary decider correct on all formulas
`equalityCNF a b` needs at least `2^n` states. -/
theorem card_ge_two_pow_of_computes_equalitySAT (n : Nat)
    (D : LayeredBoundaryDecider n n) (hSAT : ComputesEqualitySAT D) :
    2 ^ n ≤ @Fintype.card D.State D.fintype :=
  card_ge_two_pow_of_computes_EQ n D (computes_EQ_of_computesEqualitySAT D hSAT)

/-- No sub-`2^n`-width one-cut boundary decider decides satisfiability on the concrete equality-CNF family. -/
theorem no_bounded_width_equalitySAT_decider (n : Nat) :
    ¬ ∃ D : LayeredBoundaryDecider n n,
      @Fintype.card D.State D.fintype < 2 ^ n ∧ ComputesEqualitySAT D := by
  rintro ⟨D, hsmall, hSAT⟩
  exact (Nat.not_lt_of_ge (card_ge_two_pow_of_computes_equalitySAT n D hSAT)) hsmall

/-! ## Calibration: the family is easy outside the one-cut model -/

/-- The unit-clause constructor produces one clause per forced bit. -/
theorem prefixUnitClauses_length (p : RawAssignment) :
    (prefixUnitClauses p).length = p.length := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [prefixUnitClauses, shiftClauses, ih]

/-- The concrete reduction has exactly `2n` clauses; it is not hiding a large hard payload. -/
theorem equalityCNF_clause_count {n : Nat} (a b : Fin n → Bool) :
    (equalityCNF a b).clauses.length = 2 * n := by
  simp [equalityCNF, prefixUnitClauses_length, Nat.two_mul]

/-- Direct executable scan of the two blocks.  This witnesses the model boundary: random access (or a second
pass over the input) decides this SAT family by ordinary equality testing, even though a one-way prefix cut
requires `2^n` states. -/
def scanEquality {n : Nat} (a b : Fin n → Bool) : Bool :=
  decide (List.ofFn a = List.ofFn b)

theorem scanEquality_eq_EQ {n : Nat} (a b : Fin n → Bool) :
    scanEquality a b = EQ n a b := by
  apply Bool.eq_iff_iff.mpr
  simp [scanEquality, EQ, eq_of_ofFn_eq]

theorem scanEquality_correct_for_SAT {n : Nat} (a b : Fin n → Bool) :
    scanEquality a b = true ↔ Satisfiable (equalityCNF a b) := by
  rw [scanEquality_eq_EQ, equalityCNF_satisfiable_iff]
  simp [EQ]

end PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB.equalityCNF_satisfiable_iff
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB.card_ge_two_pow_of_computes_equalitySAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB.no_bounded_width_equalitySAT_decider
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB.scanEquality_correct_for_SAT
