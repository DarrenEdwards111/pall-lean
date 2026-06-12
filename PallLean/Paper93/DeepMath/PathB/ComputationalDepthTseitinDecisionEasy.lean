import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinWidthKernel

/-!
# "Tseitin is not enough": the proof-hard instance is decision-easy (option-3 guardrail)

The whole observer-debt programme builds its hardness on expander Tseitin: a `2^{Ω(n)}` fooling set, the proved
width/space lower bounds (`combination_support_card_ge_of_expansion`).  That is **proof / distinguishability**
hardness.  This file proves the honest guardrail — the *same* instance is **decision-easy**: satisfiability is
governed by a single parity bit, `∑_v charge v`, not by the exponential fooling-set debt.

A Tseitin assignment `x : Edge → ZMod 2` **satisfies** charges `charge : V → ZMod 2` if the parity at every
vertex matches its charge: `∑_e constraint v e · x e = charge v`.  Summing over all vertices, each edge is
counted by exactly its two endpoints (`card_endpoints = 2`, and `2 = 0` in `ZMod 2`), so the whole sum
vanishes — forcing `∑_v charge v = 0`.  Hence:

> **Satisfiable ⇒ `∑_v charge v = 0`** — equivalently, **odd total charge ⇒ unsatisfiable**.

So the UNSAT side is decided by a **1-bit parity check** (`∑_v charge v ≠ 0`), in linear time, **without
resolving a single residual / fooling-set distinction**.  (The converse — even total charge `⇒` satisfiable —
holds for connected graphs by the standard spanning-tree routing of charges; it is cited, not formalized here.
Together they give Tseitin satisfiability `∈ P` via a parity computation.)

## Proved (clean axioms, no `sorry`)

* `sum_constraint_eq_card` — `∑_v constraint v e = |endpoints e|` in `ZMod 2` (each edge's incidence column
  sums to its endpoint count).
* `tseitin_charge_sum_zero_of_sat` — a satisfying assignment forces `∑_v charge v = 0`.
* `tseitin_unsat_of_odd_charge` — odd total charge ⇒ **no** satisfying assignment exists (decided by one bit).

## Why this is the guardrail

The programme's debt invariants lower-bound **distinguishability / proof / space** complexity, and expander
Tseitin maximises them.  Yet `tseitin_unsat_of_odd_charge` decides (the UNSAT side of) the *same* instance with
a parity check — a linear functional of the charges — that never distinguishes any of the `2^{Ω(n)}` residual
branches.  So **high holonomy / proof / fooling-set debt does NOT imply decision hardness**: it is bypassed
exactly as Gaussian elimination bypasses it.  This is the concrete witness, on our own hard instance, that the
gap to `P ≠ NP` is *decision*-hardness, not the proof-hardness the arc proves.  Crossing it needs a
decision-hard family where no such parity / algebraic shortcut exists — the open `DecisionHolonomyHyp`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- A Tseitin assignment `x` **satisfies** the charges `charge` if the parity at every vertex equals its
charge: `∑_e constraint v e · x e = charge v`. -/
def TseitinGraph.Satisfies (G : TseitinGraph V Edge) (charge : V → ZMod 2) (x : Edge → ZMod 2) : Prop :=
  ∀ v, ∑ e, G.constraint v e * x e = charge v

/-- **Incidence-column sum (proved).**  Summing vertex `e`-coefficients over all vertices counts `e`'s
endpoints: `∑_v constraint v e = |endpoints e|` in `ZMod 2`. -/
theorem sum_constraint_eq_card (G : TseitinGraph V Edge) (e : Edge) :
    ∑ v, G.constraint v e = ((G.endpoints e).card : ZMod 2) := by
  simp only [TseitinGraph.constraint]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **The parity obstruction (proved).**  Any satisfying assignment forces the total charge to be even:
`∑_v charge v = 0`.  (Each edge is counted by its two endpoints; `2 = 0` in `ZMod 2`.) -/
theorem tseitin_charge_sum_zero_of_sat (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (x : Edge → ZMod 2) (hx : G.Satisfies charge x) :
    ∑ v, charge v = 0 := by
  have step : ∑ v, charge v = ∑ e, ((G.endpoints e).card : ZMod 2) * x e := by
    calc ∑ v, charge v
        = ∑ v, ∑ e, G.constraint v e * x e :=
          Finset.sum_congr rfl (fun v _ => (hx v).symm)
      _ = ∑ e, ∑ v, G.constraint v e * x e := Finset.sum_comm
      _ = ∑ e, ((G.endpoints e).card : ZMod 2) * x e := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          rw [← Finset.sum_mul, sum_constraint_eq_card]
  rw [step]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  rw [G.card_endpoints e, ZMod.natCast_self, zero_mul]

/-- **Decision-easy guardrail (proved): odd charge ⇒ unsatisfiable.**  If the total charge is odd
(`∑_v charge v ≠ 0`), there is **no** satisfying assignment.  So unsatisfiability is decided by a single
parity bit — a linear functional of the charges — bypassing the `2^{Ω(n)}` fooling-set debt entirely. -/
theorem tseitin_unsat_of_odd_charge (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (h : ∑ v, charge v ≠ 0) :
    ¬ ∃ x, G.Satisfies charge x := by
  rintro ⟨x, hx⟩
  exact h (tseitin_charge_sum_zero_of_sat G charge x hx)

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.sum_constraint_eq_card
#print axioms PallLean.Paper93.DeepMath.PathB.tseitin_charge_sum_zero_of_sat
#print axioms PallLean.Paper93.DeepMath.PathB.tseitin_unsat_of_odd_charge
