import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossBranchCosetCollision
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Exact quotient-rank bound for cross-branch parity classes

Project each queried parity column into the quotient by the kept-column span.  Their image spans a finite F₂-vector
space of dimension `d`.  Every queried-assignment coset is a subset sum of those projected columns, hence lies in
that span.  Therefore the number of distinct residual branch classes is at most exactly the ambient state count
`2^d`.

This replaces the raw `2^q` branch factor by `2^d`, where `d` is the rank contributed by queried columns modulo the
kept span.  A genuine collision saving is possible precisely when `d < q`; the remaining structural question is
whether a useful query block with this rank deficit must exist in the target circuit class.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRank

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.CrossBranchAffineFactorization
open PallLean.Paper93.DeepMath.PathB.CrossBranchCosetCollision

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]

/-- Queried columns projected to the quotient by the kept-column span. -/
noncomputable def projectedQueriedSet (kept queried : Finset V) :
    Finset (V ⧸ Submodule.span (ZMod 2) (↑kept : Set V)) :=
  queried.image (Submodule.mkQ (Submodule.span (ZMod 2) (↑kept : Set V)))

/-- Rank contributed by queried columns modulo the kept span. -/
noncomputable def quotientQueryRank (kept queried : Finset V) : ℕ :=
  Set.finrank (ZMod 2) (↑(projectedQueriedSet kept queried) :
    Set (V ⧸ Submodule.span (ZMod 2) (↑kept : Set V)))

/-- Every reachable branch coset lies in the span of the projected queried columns. -/
theorem cosetClassSet_subset_projectedSpan (kept queried : Finset V) :
    (↑(cosetClassSet (F := ZMod 2) kept queried) :
        Set (V ⧸ Submodule.span (ZMod 2) (↑kept : Set V))) ⊆
      Submodule.span (ZMod 2) (↑(projectedQueriedSet kept queried) :
        Set (V ⧸ Submodule.span (ZMod 2) (↑kept : Set V))) := by
  intro y hy
  obtain ⟨shift, hshift, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hshift
  rw [map_sum]
  apply Submodule.sum_mem
  intro v hv
  apply Submodule.subset_span
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  exact ⟨v, Finset.mem_powerset.mp hs hv, rfl⟩

/-- **Exact quotient-rank class bound (proved): at most `2^d` residual branch classes.** -/
theorem cosetClassSet_card_le_pow_quotientRank (kept queried : Finset V) :
    (cosetClassSet (F := ZMod 2) kept queried).card ≤ 2 ^ quotientQueryRank kept queried := by
  let W := V ⧸ Submodule.span (ZMod 2) (↑kept : Set V)
  let P : Submodule (ZMod 2) W :=
    Submodule.span (ZMod 2) (↑(projectedQueriedSet kept queried) : Set W)
  letI : FiniteDimensional (ZMod 2) P := by
    dsimp [P]
    infer_instance
  letI : Finite P := Module.finite_of_finite (ZMod 2)
  letI : Fintype P := Fintype.ofFinite P
  let f : ↥(cosetClassSet (F := ZMod 2) kept queried) → P := fun y =>
    ⟨y.1, cosetClassSet_subset_projectedSpan kept queried y.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : P => (z : W)) hab
  calc
    (cosetClassSet (F := ZMod 2) kept queried).card =
        Fintype.card ↥(cosetClassSet (F := ZMod 2) kept queried) := by simp
    _ ≤ Fintype.card P := Fintype.card_le_of_injective f hinj
    _ = 2 ^ Module.finrank (ZMod 2) P := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    _ = 2 ^ quotientQueryRank kept queried := rfl

/-- Quotient rank is at most the number of queried columns. -/
theorem quotientQueryRank_le_card (kept queried : Finset V) :
    quotientQueryRank kept queried ≤ queried.card := by
  exact le_trans (finrank_span_finset_le_card (projectedQueriedSet kept queried)) Finset.card_image_le

end PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRank

#print axioms PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRank.cosetClassSet_subset_projectedSpan
#print axioms PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRank.cosetClassSet_card_le_pow_quotientRank
#print axioms PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRank.quotientQueryRank_le_card
