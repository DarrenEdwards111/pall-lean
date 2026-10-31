import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPTableCountComparator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitInitLoop

/-!
# MCSP verifier: finite-control table preservation and materialization

For the well-formed MCSP path, this file instantiates the repository's large
proved init-loop engine with an empty instruction body.  With bound `N`, that
machine visits exactly `N` cursored table units, preserves and heals their
value/cursor region, preserves the bound, materializes a second `unaryD N`
counter, and emits a doubled copy of the first `N` table bits.

At `N = 2^n = table.length`, the output is therefore exactly the original
table, with both its preserved random-access representation and a fresh
doubled sequential copy.  This is the constructive/completeness half of the
table-length emitter.  Rejecting a malformed table shorter than the bound
still requires exposing the init engine's past-end branch as a rejection bit;
that soundness connector is not assumed here.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPTableMaterializeMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ConcreteMCSP
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoop

/-- The existing finite-control init-loop, specialized to emit only each input
bit and no surrounding instruction body. -/
def tableMaterializeMachine : Machine :=
  initLoopMachine []

/-- Canonical scratch layout for a bound and a cursor-preserving table. -/
def tableMaterializeInput (N : ℕ) (table : List Bool) : List Bool :=
  unaryD N ++ (xVis table 0 ++ (jT N 0 ++ encodeD []))

@[simp] theorem progOut_nil (k : ℕ) :
    progOut ([] : List (Option Bool)) k = [] := rfl

theorem initOutN_nil_eq_bitsUpTo (table : List Bool) (N : ℕ) :
    initOutN [] table N = bitsUpTo table N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [initOutN, progOut_nil, List.nil_append, bitsUpTo, ih]

theorem initOut_nil_eq_bitsUpTo (table : List Bool) (N : ℕ) :
    initOut [] table N = bitsUpTo table N := by
  simpa [initOut] using initOutN_nil_eq_bitsUpTo table N

theorem bitsUpTo_append_prefix (front back : List Bool) :
    ∀ k, k ≤ front.length →
      bitsUpTo (front ++ back) k = bitsUpTo front k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [bitsUpTo]
      rw [ih (Nat.le_of_succ_le hk)]
      rw [List.getD_append (h := Nat.lt_of_succ_le hk)]

theorem bitsUpTo_eq_self (table : List Bool) :
    bitsUpTo table table.length = table := by
  induction table using List.reverseRecOn with
  | nil => rfl
  | append_singleton table b ih =>
      rw [List.length_append, List.length_singleton]
      simp only [bitsUpTo]
      rw [bitsUpTo_append_prefix table [b] table.length (le_refl _)]
      simp [ih]

/-- Exact finite-control run on any bound. -/
theorem tableMaterialize_run (N : ℕ) (table : List Bool) :
    run tableMaterializeMachine (ilClock [] N table.length 0)
      (init tableMaterializeMachine (tableMaterializeInput N table)) =
      ⟨(96, ⟨0, Nat.succ_pos _⟩, false),
        2 * N + 2 + 4 * table.length + 1,
        unaryD N ++
          (xVis table 0 ++
            (unaryD N ++ encodeD (bitsUpTo table N)))⟩ := by
  simpa [tableMaterializeMachine, tableMaterializeInput,
    initOut_nil_eq_bitsUpTo] using
    initLoop_run ([] : List (Option Bool)) N table []

/-- On a well-formed MCSP table the emitted copy is exact, not padded or
truncated. -/
theorem tableMaterialize_wellFormed (I : Instance) (hI : I.WellFormed) :
    run tableMaterializeMachine
        (ilClock [] (2 ^ I.n) I.table.length 0)
        (init tableMaterializeMachine
          (tableMaterializeInput (2 ^ I.n) I.table)) =
      ⟨(96, ⟨0, Nat.succ_pos _⟩, false),
        2 * (2 ^ I.n) + 2 + 4 * I.table.length + 1,
        unaryD (2 ^ I.n) ++
          (xVis I.table 0 ++
            (unaryD (2 ^ I.n) ++ encodeD I.table))⟩ := by
  rw [tableMaterialize_run]
  have hb : bitsUpTo I.table (2 ^ I.n) = I.table := by
    rw [← hI]
    exact bitsUpTo_eq_self I.table
  rw [hb]

theorem tableMaterialize_halts (N : ℕ) (table : List Bool) :
    HaltsBy tableMaterializeMachine (tableMaterializeInput N table)
      (ilClock [] N table.length 0) := by
  simpa [tableMaterializeMachine, tableMaterializeInput] using
    initLoop_halted ([] : List (Option Bool)) N table []

/-- In particular, the preserved cursor representation still contains exactly
the original table values. -/
theorem materialized_value_lo (I : Instance) (i : ℕ) (hi : i < I.table.length) :
    (xVis I.table 0).getD (4 * i) false = I.table.getD i false :=
  by simpa using xVisE_val_lo I.table 0 i [] hi

theorem materialized_value_hi (I : Instance) (i : ℕ) (hi : i < I.table.length) :
    (xVis I.table 0).getD (4 * i + 1) false = I.table.getD i false :=
  by simpa using xVisE_val_hi I.table 0 i [] hi

/-- Existing global polynomial accounting specialized to this emitter. -/
theorem tableMaterialize_clock_le (N X : ℕ) :
    ilClock [] N X 0 ≤
      N * (10 * N + 8 * X + 2 * N + 23) +
        (4 * N + 4 * X + 6) := by
  have h := ilClock_le ([] : List (Option Bool)) N X 0
  simpa [ilCap] using h

end PallLean.Paper93.DeepMath.PathB.MCSPTableMaterializeMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableMaterializeMachine.tableMaterialize_wellFormed
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableMaterializeMachine.tableMaterialize_halts
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableMaterializeMachine.tableMaterialize_clock_le
