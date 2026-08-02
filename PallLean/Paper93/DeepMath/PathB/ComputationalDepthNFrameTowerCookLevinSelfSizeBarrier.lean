import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerEffectiveDiagonalCompilerAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinReduce
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSelfReferenceEquivalence

/-!
# N-Frame tower: Cook–Levin self-size barrier

The effective tower audit left one concrete proposal: use the repository's
encoded universal machine and Cook–Levin reduction to compile solver code into
a finite formula that diagonalizes against that solver.

This file checks the most literal implementation.  A Cook–Levin tableau with
clock `B` contains at least one head-position clause for every time
`0, ..., B`; hence its clause count is at least `B + 1`.  This is proved from
the actual `headFamily`, `assembledFormula`, `fullFormula`, and `fullTableau`
definitions.

Consequently a formula cannot literally equal a tableau simulating its solver
for a clock at least the formula's own clause count: equality would force

`B + 1 ≤ |φ| ≤ B`.

The result does not rule out Kleene-style self-reference through a compact
name, quotation, or recursion theorem.  It rules out the naive physical
self-containment construction.  Any surviving route needs a separately proved
compact naming/fixed-point bridge connecting the small name to the full SAT
formula.  The existing `DiagonalSATSelfReferenceCompiler` states precisely the
semantic object needed, and its existence is already equivalent to the SAT
lower bound under the repository's decision-to-search accounting.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerCookLevinSelfSizeBarrier

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinReduce

/-! ## A real lower bound on the repository tableau size -/

/-- Gathering one nonempty formula per index produces at least one clause per
index. -/
theorem list_length_le_bigAnd_map_length
    {α : Type} (l : List α)
    (f : α → Formula)
    (hne : ∀ a ∈ l, 1 ≤ (f a).length) :
    l.length ≤ (bigAnd (l.map f)).length := by
  induction l with
  | nil => simp [bigAnd]
  | cons a l ih =>
      have ha : 1 ≤ (f a).length := hne a (by simp)
      have htail : ∀ b ∈ l, 1 ≤ (f b).length := by
        intro b hb
        exact hne b (by simp [hb])
      have hi : l.length ≤ (List.map f l).flatten.length := by
        simpa only [bigAnd] using ih htail
      simp only [List.length_cons, List.map_cons, bigAnd, List.flatten_cons,
        List.length_append]
      omega

/-- Every one-hot formula contains its at-least-one clause. -/
theorem one_le_headOneHot_length (t P : Nat) :
    1 ≤ (headOneHot t P).length := by
  simp [headOneHot, oneHot]

/-- The head family contains at least one clause for each time
`0, ..., B`. -/
theorem clock_succ_le_headFamily_length (P B : Nat) :
    B + 1 ≤ (headFamily P B).length := by
  rw [headFamily]
  have h := list_length_le_bigAnd_map_length
    (List.range (B + 1)) (fun t => headOneHot t P) (by
      intro t _
      exact one_le_headOneHot_length t P)
  simpa using h

/-- The actual repository Cook–Levin output has at least `clock + 1` clauses.
This is a lower bound, complementing the existing polynomial upper bound. -/
theorem clock_succ_le_tableauReduction_length
    (M : Machine) (x : List Bool) (clock : Nat) :
    clock + 1 ≤ (tableauReduction M x clock).length := by
  have hh := clock_succ_le_headFamily_length (x.length + clock) clock
  unfold tableauReduction fullTableau fullFormula assembledFormula
  simp only [List.length_append]
  omega

/-! ## Literal self-containment is impossible -/

/-- The most direct proposed implementation: `formula` is literally the
Cook–Levin tableau of a run whose clock is computed from `formula`'s own size. -/
structure DirectTableauSelfEmbedding
    (M : Machine) (x : List Bool) (clock : Nat → Nat) where
  formula : Formula
  fixedpoint : formula = tableauReduction M x (clock formula.length)

/-- Any literal self-tableau must be strictly larger than its own simulation
clock. -/
theorem DirectTableauSelfEmbedding.clock_lt_formula_length
    {M : Machine} {x : List Bool} {clock : Nat → Nat}
    (E : DirectTableauSelfEmbedding M x clock) :
    clock E.formula.length < E.formula.length := by
  have h := clock_succ_le_tableauReduction_length
    M x (clock E.formula.length)
  rw [← E.fixedpoint] at h
  omega

/-- Therefore no literal self-tableau can simulate for even its own clause
count. -/
theorem no_directTableauSelfEmbedding_of_size_le_clock
    (M : Machine) (x : List Bool) (clock : Nat → Nat)
    (hclock : ∀ n, n ≤ clock n) :
    ¬ Nonempty (DirectTableauSelfEmbedding M x clock) := by
  rintro ⟨E⟩
  have hlt := E.clock_lt_formula_length
  exact (Nat.not_lt_of_ge (hclock E.formula.length)) hlt

/-- In particular the linear self-clock `n ↦ n` is already impossible. -/
theorem no_directTableauSelfEmbedding_identityClock
    (M : Machine) (x : List Bool) :
    ¬ Nonempty (DirectTableauSelfEmbedding M x id) := by
  apply no_directTableauSelfEmbedding_of_size_le_clock
  intro n
  rfl

/-- Every ordinary positive polynomial clock of the form
`c * (n + 1)^k` dominates `n`, so it also cannot close the literal size fixed
point. -/
theorem size_le_positivePolynomialClock
    (c k n : Nat) (hc : 0 < c) (hk : 0 < k) :
    n ≤ c * (n + 1) ^ k := by
  have hbase : n ≤ n + 1 := by omega
  cases k with
  | zero => omega
  | succ k =>
      have hone : 1 ≤ (n + 1) ^ k := by
        exact one_le_pow₀ (by omega)
      have hmul : n + 1 ≤ (n + 1) * (n + 1) ^ k := by
        exact Nat.le_mul_of_pos_right (n + 1) (by omega)
      have hc1 : 1 ≤ c := by omega
      calc
        n ≤ n + 1 := hbase
        _ ≤ (n + 1) * (n + 1) ^ k := hmul
        _ = (n + 1) ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
        _ ≤ c * (n + 1) ^ (k + 1) := by
          simpa only [Nat.one_mul] using
            (Nat.mul_le_mul_right ((n + 1) ^ (k + 1)) hc1)

/-- No positive polynomial-time self-simulation clock admits the literal
Cook–Levin fixed point. -/
theorem no_directTableauSelfEmbedding_positivePolynomialClock
    (M : Machine) (x : List Bool) (c k : Nat)
    (hc : 0 < c) (hk : 0 < k) :
    ¬ Nonempty
      (DirectTableauSelfEmbedding M x (fun n => c * (n + 1) ^ k)) := by
  apply no_directTableauSelfEmbedding_of_size_le_clock
  intro n
  exact size_le_positivePolynomialClock c k n hc hk

end PallLean.Paper93.DeepMath.PathB.NFrameTowerCookLevinSelfSizeBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCookLevinSelfSizeBarrier.clock_succ_le_headFamily_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCookLevinSelfSizeBarrier.clock_succ_le_tableauReduction_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCookLevinSelfSizeBarrier.DirectTableauSelfEmbedding.clock_lt_formula_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCookLevinSelfSizeBarrier.no_directTableauSelfEmbedding_of_size_le_clock
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCookLevinSelfSizeBarrier.no_directTableauSelfEmbedding_identityClock
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCookLevinSelfSizeBarrier.no_directTableauSelfEmbedding_positivePolynomialClock
