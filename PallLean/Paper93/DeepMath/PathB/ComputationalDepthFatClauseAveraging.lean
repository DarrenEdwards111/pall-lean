import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionWidthSize

/-!
# The popular-literal averaging lemma (toward general DAG size–width)

The Ben-Sasson–Wigderson *general* (DAG) size–width bound runs through the
**fat-clause method**: in a refutation, look at the clauses of width `> d` ("fat"),
find a literal appearing in many of them, restrict it (killing a fraction of the
fat clauses), and recurse.  The combinatorial heart is the averaging step proved
here: among any family `F` of fat clauses over `n` literals, *some* literal lies in
`≥ d·|F| / n` of them.

By double counting, the total literal–clause incidence is `∑_{C∈F} |C| > d·|F|`, and
there are `n = |Lit|` literals, so the most popular literal meets the average:
`n · (incidence ℓ) ≥ d·|F|`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open scoped BigOperators

variable {Lit : Type*} [Fintype Lit] [DecidableEq Lit]

/-- **Double counting.**  Summing, over literals, the number of clauses containing
each literal equals the total width of the family. -/
theorem sum_incidence_eq (F : Finset (ResolutionClause Lit)) :
    ∑ ℓ : Lit, (F.filter (fun C => ℓ ∈ C)).card = ∑ C ∈ F, C.card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **Popular-literal averaging.**  In a family `F` of fat clauses (each of width
`> d`) over the literal type `Lit`, some literal `ℓ` lies in enough clauses that
`d·|F| ≤ |Lit| · (number of clauses of F containing ℓ)`. -/
theorem exists_popular_literal [Nonempty Lit]
    (F : Finset (ResolutionClause Lit)) {d : ℕ} (hfat : ∀ C ∈ F, d < C.card) :
    ∃ ℓ : Lit, d * F.card ≤ Fintype.card Lit * (F.filter (fun C => ℓ ∈ C)).card := by
  by_contra h
  push_neg at h
  have hlt : ∑ ℓ : Lit, Fintype.card Lit * (F.filter (fun C => ℓ ∈ C)).card
      < ∑ _ℓ : Lit, d * F.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun ℓ _ => h ℓ)
  rw [Finset.sum_const, ← Finset.mul_sum, sum_incidence_eq, Finset.card_univ,
    smul_eq_mul] at hlt
  -- hlt : |Lit| * (∑ C ∈ F, C.card) < |Lit| * (d * F.card)
  have hsum : ∑ C ∈ F, C.card < d * F.card := Nat.lt_of_mul_lt_mul_left hlt
  have hge : d * F.card + F.card ≤ ∑ C ∈ F, C.card := by
    rw [← Nat.succ_mul]
    calc (d + 1) * F.card = ∑ _C ∈ F, (d + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ C ∈ F, C.card := Finset.sum_le_sum (fun C hC => hfat C hC)
  omega

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.exists_popular_literal
