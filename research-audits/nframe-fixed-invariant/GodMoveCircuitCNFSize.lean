import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitUniversality
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCodec

/-!
# Concrete size bounds for the existing circuit-to-CNF compiler

The production `CircuitUniversality.tseitin` compiler already handles every
Boolean gate operation and maps invalid references to a forced-false slot.
This file reuses that implementation and correctness proof, and bounds its
clause count, clause width, variable indices, and faithful encoded bit length.

For `n` inputs and `s` gates, there are at most `4*s+2` clauses of width at
most three. Variable indices are at most `n+s`: the extra index is precisely
the forced-false slot, including when the circuit is empty. The encoded
formula has quadratic size in `n+s+1`.

These are bounds on the actual returned representation. No machine runtime
bound for constructing it, or efficient SAT decision procedure, is asserted.
-/

namespace GodMoveCircuitCNFSize

open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer CookLevinReduction CircuitUniversality CookLevinEmitCodec

theorem gateClauses_length_le (n L m : ℕ) (g : CGate n) :
    (gateClauses n L m g).length ≤ 4 := by
  cases g <;> simp [gateClauses]

theorem gateClauses_width (n L m : ℕ) (g : CGate n) :
    ∀ cl ∈ gateClauses n L m g, cl.length ≤ 3 := by
  cases g <;> simp [gateClauses]

theorem readVar_le (n L j m : ℕ) (hm : m ≤ L) : readVar n L j m ≤ n + L := by
  unfold readVar
  split <;> omega

theorem gateClauses_var_bound (n L m : ℕ) (g : CGate n) (hm : m ≤ L) :
    ∀ cl ∈ gateClauses n L m g, ∀ l ∈ cl, l.1 ≤ n + L := by
  cases g with
  | var i =>
      have hi := i.isLt
      simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      omega
  | cst b =>
      simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq]
      omega
  | un op j =>
      have hj := readVar_le n L j m hm
      simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      omega
  | bin op j k =>
      have hj := readVar_le n L j m hm
      have hk := readVar_le n L k m hm
      simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      omega

theorem gadgets_length_le (n L m : ℕ) (gs : List (CGate n)) :
    (gadgets n L m gs).length ≤ 4 * gs.length := by
  induction gs generalizing m with
  | nil => simp [gadgets]
  | cons g gs ih =>
      have hg := gateClauses_length_le n L m g
      have ht := ih (m + 1)
      simp only [gadgets, List.length_append, List.length_cons]
      omega

theorem gadgets_width (n L m : ℕ) (gs : List (CGate n)) :
    ∀ cl ∈ gadgets n L m gs, cl.length ≤ 3 := by
  intro cl hcl
  obtain ⟨i, _, hi⟩ := gadgets_mem n L m gs cl hcl
  exact gateClauses_width n L (m + i) _ cl hi

theorem gadgets_var_bound (n L m : ℕ) (gs : List (CGate n))
    (hbound : m + gs.length ≤ L) :
    ∀ cl ∈ gadgets n L m gs, ∀ l ∈ cl, l.1 ≤ n + L := by
  intro cl hcl
  obtain ⟨i, hi, hgate⟩ := gadgets_mem n L m gs cl hcl
  exact gateClauses_var_bound n L (m + i) _ (by omega) cl hgate

theorem tseitin_length_le {n : ℕ} (c : List (CGate n)) :
    (tseitin c).length ≤ 4 * c.length + 2 := by
  have h := gadgets_length_le n c.length 0 c
  simpa only [tseitin, List.length_append, List.length_cons, List.length_nil] using
    Nat.add_le_add_right h 2

theorem tseitin_width {n : ℕ} (c : List (CGate n)) :
    ∀ cl ∈ tseitin c, cl.length ≤ 3 := by
  intro cl hcl
  rcases List.mem_append.mp hcl with hg | ht
  · exact gadgets_width n c.length 0 c cl hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp

/-- The inclusive bound accounts for the additional forced-false variable. -/
theorem tseitin_var_bound {n : ℕ} (c : List (CGate n)) :
    ∀ cl ∈ tseitin c, ∀ l ∈ cl, l.1 ≤ n + c.length := by
  intro cl hcl
  rcases List.mem_append.mp hcl with hg | ht
  · exact gadgets_var_bound n c.length 0 c (by omega) cl hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp
    · simp

theorem tseitin_var_lt {n : ℕ} (c : List (CGate n)) :
    ∀ cl ∈ tseitin c, ∀ l ∈ cl, l.1 < n + c.length + 1 := by
  intro cl hcl l hl
  exact Nat.lt_succ_of_le (tseitin_var_bound c cl hcl l hl)

/-- A concrete polynomial bound for the faithful coordinate-encoded CNF. -/
theorem tseitin_encoded_length_le {n : ℕ} (c : List (CGate n)) :
    (encodeFormula' (tseitin c)).length ≤
      (4 * c.length + 3) + (4 * c.length + 2) * (6 * (n + c.length) + 22) := by
  have henc := encodeFormula'_length_le (tseitin c) (n + c.length) 3
    (tseitin_width c) (tseitin_var_bound c)
  have hcount := tseitin_length_le c
  calc
    _ ≤ ((tseitin c).length + 1) +
        (tseitin c).length * (6 * (n + c.length) + 22) := by
      convert henc using 1
      ring
    _ ≤ (4 * c.length + 3) + (4 * c.length + 2) * (6 * (n + c.length) + 22) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ hcount)

theorem tseitin_encoded_length_le_quadratic {n : ℕ} (c : List (CGate n)) :
    (encodeFormula' (tseitin c)).length ≤ 100 * (n + c.length + 1) ^ 2 := by
  have h := tseitin_encoded_length_le c
  nlinarith [Nat.zero_le (n * c.length), Nat.zero_le (n * n),
    Nat.zero_le (c.length * c.length)]

/-- This correctness is inherited from the existing production compiler. -/
theorem tseitin_satisfiable_iff {n : ℕ} (c : List (CGate n)) :
    Satisfiable (tseitin c) ↔ ∃ a : Fin n → Bool, output c a = true :=
  universality n c

theorem encoded_tseitin_satisfiable_iff {n : ℕ} (c : List (CGate n)) :
    Satisfiable (decodeFormula' (encodeFormula' (tseitin c))) ↔
      ∃ a : Fin n → Bool, output c a = true := by
  rw [decodeFormula'_encodeFormula']
  exact tseitin_satisfiable_iff c

end GodMoveCircuitCNFSize

#print axioms GodMoveCircuitCNFSize.tseitin_length_le
#print axioms GodMoveCircuitCNFSize.tseitin_width
#print axioms GodMoveCircuitCNFSize.tseitin_var_bound
#print axioms GodMoveCircuitCNFSize.tseitin_encoded_length_le
#print axioms GodMoveCircuitCNFSize.tseitin_encoded_length_le_quadratic
#print axioms GodMoveCircuitCNFSize.tseitin_satisfiable_iff
#print axioms GodMoveCircuitCNFSize.encoded_tseitin_satisfiable_iff
