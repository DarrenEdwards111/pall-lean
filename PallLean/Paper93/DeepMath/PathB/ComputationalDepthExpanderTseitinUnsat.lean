import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinResolutionWidth

/-!
# Tseitin unsatisfiability from odd charge (concretization brick)

The capstone size lower bound carries the abstract hypothesis `hunsat`: the
constraint family is globally unsatisfiable.  Here we discharge it concretely —
this is the classical **Tseitin unsatisfiability** fact and the reason these
formulas are hard.

The handshake property `card_endpoints : (endpoints e).card = 2` forces, for every
assignment `a`,
  `∑_v parity_v(a) = ∑_e (∑_v constraint v e) · a_e = ∑_e (2 : F₂) · a_e = 0`,
since each edge is counted by exactly its two endpoints (and `2 = 0` in `F₂`).
Hence if the total charge `∑_v charge_v` is **odd** (`= 1`), the constraints
`parity_v = charge_v` cannot all hold (they would force `∑_v charge_v = 0`), so
some vertex constraint fails — exactly the `hunsat` hypothesis.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinResolution

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **Handshake ⇒ every edge column sums to zero.**  Each edge has exactly two
endpoints, and `2 = 0` in `F₂`, so the constraint matrix has zero column sums. -/
theorem sum_constraint_eq_zero (G : TseitinGraph V Edge) (e : Edge) :
    ∑ v : V, G.constraint v e = 0 := by
  simp only [TseitinGraph.constraint, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  rw [G.card_endpoints e]
  decide

/-- **Total parity is always zero.**  Summing the vertex parities over all vertices
counts each edge by its two endpoints, giving `0` in `F₂`. -/
theorem sum_parity_eq_zero (G : TseitinGraph V Edge) (a : Edge → ZMod 2) :
    ∑ v : V, parity G a v = 0 := by
  simp only [parity]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  rw [← Finset.sum_mul, sum_constraint_eq_zero G e, zero_mul]

/-- **Tseitin unsatisfiability.**  If the total charge is odd (`∑_v charge_v = 1`),
no assignment satisfies all vertex constraints: this is the `hunsat` hypothesis of
the resolution lower bounds, discharged concretely. -/
theorem tseitin_unsat (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1) :
    ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a := by
  intro a
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ v : V, charge v = ∑ v : V, parity G a v :=
    Finset.sum_congr rfl (fun v _ => (hcon v).symm)
  exact absurd (hodd.symm.trans (hsum.trans (sum_parity_eq_zero G a))) (by decide)

end PallLean.Paper93.DeepMath.PathB.TseitinResolution

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinResolution.tseitin_unsat
