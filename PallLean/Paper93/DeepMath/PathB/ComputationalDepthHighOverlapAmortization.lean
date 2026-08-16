import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNormalizedSeparatorPotential

/-!
# High-overlap amortization: a proved combinatorial surplus and the semantic transfer wall

Normalized ownership has zero surplus.  Raw incidence has local surplus but can exceed the input budget.  The next
candidate combines them: use normalized credit for the `n`-scale budget, and treat repeated incidences as *overlap
surplus*.  This file proves the exact combinatorial engine behind that proposal.

* The sum of live variable degrees equals total live incidence credit (double counting).
* If incidence exceeds `d · #live`, some live variable has degree greater than `d`.
* In particular, if incidence exceeds `#live`, one query destroys at least two live incidences.
* The destroyed degree decomposes into one unit paying for the binary query plus `degree-1` units of genuine overlap
  surplus.

This is the desired amortized high-overlap lemma at the **support graph** level.  It is not yet a circuit-SAT lemma:
deleting an input incidence from a residual `MOD` gate changes its affine residue but generally does not delete the
gate or reduce its continuation-state boundary.  The remaining load-bearing theorem is now the semantic transfer:
prove that accumulated overlap surplus forces gate simplification/separator factorization in a named circuit class,
or exhibit a family where all the combinatorial surplus is semantically inert.
-/

namespace PallLean.Paper93.DeepMath.PathB.HighOverlapAmortization

open Finset
open PallLean.Paper93.DeepMath.PathB.FanoutAwareIncidencePotential

variable {Gate Var : Type} [DecidableEq Gate] [DecidableEq Var]

/-- Per-gate indicator sum counts exactly its live support. -/
theorem sum_live_mem_indicator (S live : Finset Var) :
    (∑ v ∈ live, if v ∈ S ∩ live then 1 else 0) = (S ∩ live).card := by
  classical
  calc
    (∑ v ∈ live, if v ∈ S ∩ live then 1 else 0)
        = ∑ v ∈ live, if v ∈ S then 1 else 0 := by
          apply sum_congr rfl
          intro v hv
          simp [hv]
    _ = (S ∩ live).card := by
          rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
          norm_num

/-- **Incidence double counting (proved).**  Sum degrees over live variables, or sum support sizes over gates: the
result is identical. -/
theorem sum_liveDegree_eq_incidenceCredit (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) :
    (∑ v ∈ live, liveDegree gates support live v) = incidenceCredit gates support live := by
  classical
  unfold liveDegree incidenceCredit
  rw [sum_comm]
  apply sum_congr rfl
  intro g hg
  exact sum_live_mem_indicator (support g) live

/-- **High-average overlap exposes a high-degree query.** -/
theorem exists_liveDegree_gt_of_average (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (d : ℕ) (havg : d * live.card < incidenceCredit gates support live) :
    ∃ v ∈ live, d < liveDegree gates support live v := by
  classical
  by_contra h
  push_neg at h
  have hsum : (∑ v ∈ live, liveDegree gates support live v) ≤ ∑ v ∈ live, d := by
    apply sum_le_sum
    intro v hv
    exact h v hv
  rw [sum_liveDegree_eq_incidenceCredit gates support live] at hsum
  simp only [sum_const_nat, card_attach, nsmul_eq_mul] at hsum
  have havg' : live.card * d < incidenceCredit gates support live := by
    simpa [Nat.mul_comm] using havg
  omega

/-- If raw incidence exceeds normalized variable budget, one live variable has degree at least two. -/
theorem exists_superunit_query (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (hexcess : live.card < incidenceCredit gates support live) :
    ∃ v ∈ live, 1 < liveDegree gates support live v := by
  simpa using exists_liveDegree_gt_of_average gates support live 1 (by simpa using hexcess)

/-- **One queried bit plus overlap surplus.**  For a live variable of positive degree, exact incidence destruction
splits into one unit paying for the query and `degree-1` extra units.  The equation avoids truncated-subtraction
ambiguity and is the amortization identity needed by any semantic transfer theorem. -/
theorem erase_incidence_query_plus_surplus (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (v : Var) (hv : v ∈ live)
    (hdeg : 1 ≤ liveDegree gates support live v) :
    incidenceCredit gates support live + (live.erase v).card
      = incidenceCredit gates support (live.erase v) + live.card
          + (liveDegree gates support live v - 1) := by
  have hcredit : incidenceCredit gates support (live.erase v)
      + liveDegree gates support live v = incidenceCredit gates support live :=
    erase_credit_add_degree gates support live v
  have hcard : (live.erase v).card + 1 = live.card := by
    rw [card_erase_of_mem hv]
    have hpos : 0 < live.card := card_pos.mpr ⟨v, hv⟩
    omega
  omega

/-- In the high-overlap case, the exposed query has at least one strict unit of combinatorial surplus beyond its
branching cost. -/
theorem exists_query_with_positive_overlap_surplus (gates : Finset Gate)
    (support : Gate → Finset Var) (live : Finset Var)
    (hexcess : live.card < incidenceCredit gates support live) :
    ∃ v ∈ live, 1 ≤ liveDegree gates support live v - 1 := by
  obtain ⟨v, hv, hdeg⟩ := exists_superunit_query gates support live hexcess
  exact ⟨v, hv, by omega⟩

end PallLean.Paper93.DeepMath.PathB.HighOverlapAmortization

#print axioms PallLean.Paper93.DeepMath.PathB.HighOverlapAmortization.sum_liveDegree_eq_incidenceCredit
#print axioms PallLean.Paper93.DeepMath.PathB.HighOverlapAmortization.exists_liveDegree_gt_of_average
#print axioms PallLean.Paper93.DeepMath.PathB.HighOverlapAmortization.erase_incidence_query_plus_surplus
