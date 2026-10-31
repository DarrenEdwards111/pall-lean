import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBlockDecompositionMinBoundedData
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBlockDecompositionMinPartial

/-!
# The restriction-observer boundary calculus, abstracted — and its scope

The `hardF` address-block extensions (`BlockDecompositionMinBoundedData`, `BlockDecompositionMinPartial`) rest on
two boundary moves:

* **halve** — adding a variable to the free block at most *halves* the residual count, so the boundary drops by at
  most `1`;
* **square** — adding a variable at most *squares* the residual count, so the boundary at most doubles (`+1`).

This file shows those two moves are **not** properties of `hardF`, nor even of Boolean formulas: they follow from
a general `RestrictionObserver` — any variable-indexed behavior count `count : Finset ι → ℕ` satisfying just the
two count axioms.  From them the whole calculus (`boundary_le_insert_succ`, `boundary_insert_le`, the two union
bounds) is derived abstractly.  `blockResidualsObserver` is an instance, recovering `formulaBlockBoundary`.

## The family-independence test result

The calculus is **family-independent across variable-restriction (Nečiporuk/decomposition-type) observers**: it
holds for *any* `RestrictionObserver`, and `blockResiduals` (for *any* formula, not just `hardF`) is one.

It is **not** applicable to the Tseitin **proof-space** rung.  That boundary
(`ComputationalDepthMinBoundaryRealized.minProofSpaceBoundary`) is `sInf` over *refutations* of the total space
`∑ clause-widths` — there is no `Finset ι → ℕ` variable-restriction structure and no "add a variable to the free
block" operation, so it is not a `RestrictionObserver` and the halve/square moves have nothing to act on.

So the two min-realized rungs (Nečiporuk address-block, Tseitin proof-space) share the **fooling/non-mergeability**
mechanism (`BranchingObserver.many_nonmergeable_sectors_force_boundary`, which supplies each rung's super-log
*base* bound — the `hardF` multiplexer, resp. expander-Tseitin width), but **not** the restriction calculus of
this file, which is specific to decomposition observers.  Family-independence holds for the mechanism that starts
the bound (fooling), not for the calculus that propagates it across sub-decompositions.

## Honest scope

An abstraction of the halve/square boundary calculus plus a delineation of where it applies.  No separation, no
new complexity-class bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictionObserverCalculus

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinBoundedData
open PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinPartial

/-- A **restriction observer**: a variable-indexed behavior count where moving a Boolean variable between the
free and fixed parts changes the count by the two canonical bounds.  This is exactly the structure the
halve/square boundary calculus needs. -/
structure RestrictionObserver (ι : Type*) [DecidableEq ι] where
  /-- Number of distinguishable behaviors when `S` is the free block. -/
  count : Finset ι → ℕ
  count_pos : ∀ S, 0 < count S
  /-- **Halve axiom.**  Removing a free variable at most halves the count. -/
  count_le_two_mul_insert : ∀ (v : ι) (S : Finset ι), count S ≤ 2 * count (insert v S)
  /-- **Square axiom.**  Adding a free variable at most squares the count. -/
  count_insert_le_sq : ∀ (v : ι) (S : Finset ι), count (insert v S) ≤ (count S) ^ 2

namespace RestrictionObserver

variable {ι : Type*} [DecidableEq ι] (O : RestrictionObserver ι)

/-- The observer boundary: the log of the behavior count. -/
def boundary (S : Finset ι) : ℕ := Nat.log 2 (O.count S)

/-- **Halve ⟹ boundary drops by at most `1`.** -/
theorem boundary_le_insert_succ (v : ι) (S : Finset ι) :
    O.boundary S ≤ O.boundary (insert v S) + 1 := by
  unfold boundary
  calc Nat.log 2 (O.count S) ≤ Nat.log 2 (2 * O.count (insert v S)) :=
        Nat.log_mono_right (O.count_le_two_mul_insert v S)
    _ = Nat.log 2 (O.count (insert v S)) + 1 := by
        rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) (O.count_pos (insert v S)).ne']

/-- **Square ⟹ boundary at most doubles (`+1`).** -/
theorem boundary_insert_le (v : ι) (S : Finset ι) :
    O.boundary (insert v S) ≤ 2 * O.boundary S + 1 := by
  unfold boundary
  have h1 : O.count S < 2 ^ (Nat.log 2 (O.count S) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : O.count (insert v S) < 2 ^ (2 * Nat.log 2 (O.count S) + 2) := by
    calc O.count (insert v S) ≤ (O.count S) ^ 2 := O.count_insert_le_sq v S
      _ < (2 ^ (Nat.log 2 (O.count S) + 1)) ^ 2 := by apply Nat.pow_lt_pow_left h1; norm_num
      _ = 2 ^ (2 * Nat.log 2 (O.count S) + 2) := by rw [← pow_mul]; congr 1; ring
  have h3 := Nat.log_lt_of_lt_pow (O.count_pos (insert v S)).ne' h2
  omega

/-- **Iterated halve.**  Adding a set `D` drops the boundary by at most `|D|`. -/
theorem boundary_le_union_add_card (S D : Finset ι) :
    O.boundary S ≤ O.boundary (S ∪ D) + D.card := by
  classical
  induction D using Finset.induction with
  | empty => simp
  | @insert v D hv ih =>
      rw [Finset.union_insert, Finset.card_insert_of_notMem hv]
      have := O.boundary_le_insert_succ v (S ∪ D)
      omega

/-- **Iterated square.**  Adding a set `D` grows the boundary by at most a factor `2^{|D|}` (in `boundary + 1`). -/
theorem boundary_union_le (S D : Finset ι) :
    O.boundary (S ∪ D) + 1 ≤ 2 ^ D.card * (O.boundary S + 1) := by
  classical
  induction D using Finset.induction with
  | empty => simp
  | @insert v D hv ih =>
      rw [Finset.union_insert, Finset.card_insert_of_notMem hv]
      have hstep := O.boundary_insert_le v (S ∪ D)
      calc O.boundary (insert v (S ∪ D)) + 1
          ≤ 2 * (O.boundary (S ∪ D) + 1) := by omega
        _ ≤ 2 * (2 ^ D.card * (O.boundary S + 1)) := by omega
        _ = 2 ^ (D.card + 1) * (O.boundary S + 1) := by rw [pow_succ]; ring

end RestrictionObserver

/-! ## `blockResiduals` is a restriction observer -/

/-- The Nečiporuk formula-subfunction observer as a `RestrictionObserver`: the two axioms are exactly the
halve and square residual-count lemmas. -/
noncomputable def blockResidualsObserver {n : ℕ} (F : BFormula n) : RestrictionObserver (Fin n) where
  count S := (blockResiduals S F).card
  count_pos S := by
    apply Finset.card_pos.mpr
    rw [blockResiduals]; exact Finset.univ_nonempty.image _
  count_le_two_mul_insert v S := blockResiduals_card_le_two_mul_insert v S F
  count_insert_le_sq v S := blockResiduals_card_insert_le_sq v S F

/-- The abstract boundary of `blockResidualsObserver` is exactly `formulaBlockBoundary`. -/
theorem boundary_blockResidualsObserver {n : ℕ} (F : BFormula n) (S : Finset (Fin n)) :
    (blockResidualsObserver F).boundary S = formulaBlockBoundary S F := rfl

/-- **The calculus recovers the concrete graceful/partial bounds.**  Both the bounded-data (`boundary_le_union_
add_card`) and partial-block (`boundary_union_le`) moves for `hardF` are instances of the abstract calculus. -/
theorem blockResiduals_calculus_agrees {n : ℕ} (F : BFormula n) (S D : Finset (Fin n)) :
    formulaBlockBoundary S F ≤ formulaBlockBoundary (S ∪ D) F + D.card ∧
      formulaBlockBoundary (S ∪ D) F + 1 ≤ 2 ^ D.card * (formulaBlockBoundary S F + 1) :=
  ⟨(blockResidualsObserver F).boundary_le_union_add_card S D,
   (blockResidualsObserver F).boundary_union_le S D⟩

end PallLean.Paper93.DeepMath.PathB.RestrictionObserverCalculus

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionObserverCalculus.RestrictionObserver.boundary_le_union_add_card
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionObserverCalculus.RestrictionObserver.boundary_union_le
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionObserverCalculus.blockResiduals_calculus_agrees
