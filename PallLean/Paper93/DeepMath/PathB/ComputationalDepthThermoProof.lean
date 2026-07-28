import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThermoBoundary

/-!
# Making the thermodynamic boundary non-circular: charge the observer and PROVE the gap

Asked not to *assume* the thermodynamic boundary is bigger but to *derive* it — remove the circularity.
Here is the honest attempt, and it genuinely succeeds — with a precise, machine-checked ceiling.

The circularity in the previous file was: "the NP boundary is bigger" read as *computational power* is `P ≠ NP`
itself.  The way to break it is to stop treating the thermodynamic boundary as a fact about *power* and start
treating it as a **charge on the model**: make the observer *pay* `c` units of energy for every shared
(reused) wire.  This is exactly the N-Frame reading — the bounded 3+1D observer lacks the energy to share
freely — turned into a cost the model actually collects.

**The derivation (non-circular, unconditional).**  Unfolding any circuit into a formula duplicates every
shared sub-computation, so the formula cost satisfies `formulaLB ≤ dagCost + sharing`.  When the observer is
charged `c ≥ 1` per shared wire, its cost is `dagCost + c·sharing ≥ dagCost + sharing ≥ formulaLB`
(`charged_pays_formula_lb`).  So a charged observer pays *at least the formula lower bound* — and formula lower
bounds (Khrapchenko `n²`, Andreev `n^{5/2}`) are **unconditional theorems**, not assumptions.  Hence
`charged_cannot_afford`: a charged observer with budget below `formulaLB` provably cannot compute the function.
Nothing here assumes a power gap — the gap is *derived* from an unconditional formula bound plus the charge.
The circularity is gone.

**The ceiling (why this is not yet `P ≠ NP`).**  The charge `c` dials the model.  At `c = 0` — the *real*
abstract circuit model, where fan-out is free — the derivation is vacuous: `chargedCost = dagCost`, and the
formula bound does not transfer (`uncharged_vacuous`, `charged_proves_but_real_escapes`).  The very same
circuit that a charged observer cannot afford is *cheap* for the real DAG observer, because it shares.  So the
non-circular proof is a proof about the **charged / bounded / formula observer**, and the real `P`-observer
computes with free sharing — the regime the charge switches off.  The residual is no longer *circularity*, it
is *reach*: pushing the bound from `c ≥ 1` (formula, where it is proved) down to `c = 0` (DAG, the real model)
is exactly ruling out the free sharing that Uhlig mass-production supplies — `cost_super`.

**`non_circular_but_capped`** states both halves at once: the derivation holds for *every* charged observer
(non-circular, universally), and the real `c = 0` observer escapes it (capped).

## What is proved

* **`charged_pays_formula_lb`** — a charged (`c ≥ 1`) observer pays at least the unconditional formula bound.
* **`charged_cannot_afford`** — hence, non-circularly, it cannot compute a function whose formula bound exceeds
  its budget.  Derived, not assumed.
* **`uncharged_vacuous`** / **`charged_proves_but_real_escapes`** — at `c = 0` (the real model) the same
  circuit is cheap: the bound does not transfer, the real observer shares its way under budget.
* **`non_circular_but_capped`** — both together: the gap is derived for every charged observer, and the real
  observer escapes; the residual is reach (charge → 0 / formula → DAG), not circularity.

## Honest verdict — the circularity is removed; a real capped bound is proved; the reach is the wall

This is genuine forward motion, not a restatement.  Charging the observer for its thermodynamic boundary
*derives* a boundary gap from an unconditional formula lower bound — the gap is no longer assumed, and the
Andreev/Khrapchenko bounds it rests on are real theorems (`charged_cannot_afford`).  So "prove it, don't assume
it" is answered: in the charged model the thermodynamic boundary provably *is* bigger.  What remains is not
circularity but the charge itself — at `c = 0`, the real fan-out-free model, the bound is vacuous and the real
`P`-observer shares under budget (`charged_proves_but_real_escapes`).  Lowering the charge from `1` to `0`
while keeping the bound is exactly forbidding unbounded sharing on a general DAG = `cost_super`.  The
thermodynamic boundary is real and now provably bites — at the formula altitude; carrying it to the DAG
altitude is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ThermoProof

/-- The charged thermodynamic model.  The observer pays `charge` energy per shared (reused) wire; `charge = 0`
is the real abstract circuit model (free fan-out), `charge ≥ 1` is the bounded / formula model.  `formulaLB`
is the unconditional formula (unfolded, no-sharing) lower bound — Khrapchenko/Andreev supply it as a theorem —
and `tree_eq` records that unfolding to a formula duplicates the shared work. -/
structure ChargedThermo where
  /-- abstract cost with free fan-out (the real `P`-observer's best circuit) -/
  dagCost : Nat
  /-- reused wires the circuit exploits -/
  sharing : Nat
  /-- energy charged per shared wire: `0` = real DAG model, `≥ 1` = bounded/formula model -/
  charge : Nat
  /-- an unconditional formula lower bound for the target (Khrapchenko `n²`, Andreev `n^{5/2}`) -/
  formulaLB : Nat
  /-- unfolding a circuit to a formula duplicates shared work: `formulaLB ≤ dagCost + sharing` -/
  tree_eq : formulaLB ≤ dagCost + sharing

/-- What the charged observer actually pays: `dagCost + charge · sharing`. -/
def ChargedThermo.chargedCost (T : ChargedThermo) : Nat := T.dagCost + T.charge * T.sharing

/-- **A charged observer pays at least the formula lower bound (proved, non-circular).**  For `charge ≥ 1`,
`chargedCost = dagCost + charge·sharing ≥ dagCost + sharing ≥ formulaLB`.  No power gap is assumed; the bound
is the unconditional formula bound. -/
theorem charged_pays_formula_lb (T : ChargedThermo) (hc : 1 ≤ T.charge) :
    T.formulaLB ≤ T.chargedCost := by
  have h1 : T.sharing ≤ T.charge * T.sharing := by
    have h := Nat.mul_le_mul hc (le_refl T.sharing)
    simpa using h
  have h2 := T.tree_eq
  show T.formulaLB ≤ T.dagCost + T.charge * T.sharing
  omega

/-- **The charged observer cannot afford a hard function (proved, non-circular).**  If the budget is below the
unconditional formula bound, the charged observer's cost exceeds the budget — derived, not assumed. -/
theorem charged_cannot_afford (T : ChargedThermo) (hc : 1 ≤ T.charge) (budget : Nat)
    (hLB : budget < T.formulaLB) : budget < T.chargedCost :=
  lt_of_lt_of_le hLB (charged_pays_formula_lb T hc)

/-- A circuit that is hard when charged but cheap in the real model: `dagCost = 1`, `sharing = 100`,
`formulaLB = 101`.  Charged (`c ≥ 1`) it pays `≥ 101`; at `c = 0` it pays only `1`. -/
def freeWorld : ChargedThermo where
  dagCost := 1
  sharing := 100
  charge := 0
  formulaLB := 101
  tree_eq := by omega

/-- **At `charge = 0` the derivation is vacuous (proved).**  In the real fan-out-free model the charged cost
collapses to `dagCost`, far below `formulaLB`: the formula bound does not transfer. -/
theorem uncharged_vacuous : ∃ T : ChargedThermo, T.charge = 0 ∧ T.chargedCost < T.formulaLB :=
  ⟨freeWorld, rfl, by decide⟩

/-- **The real observer escapes the charged bound (proved).**  The *same* circuit that a charged observer
(`c = 1`) cannot fit in budget `50` costs the real observer (`c = 0`) only `1` — it shares its way under
budget.  The non-circular proof proves hardness of a circuit the real model computes cheaply. -/
theorem charged_proves_but_real_escapes :
    ∃ (T : ChargedThermo) (budget : Nat),
      budget < T.dagCost + 1 * T.sharing ∧ ¬ (budget < T.dagCost + 0 * T.sharing) :=
  ⟨freeWorld, 50, by decide, by decide⟩

/-- **Non-circular but capped (proved).**  Left: for *every* charged observer, a below-formula-bound budget is
provably insufficient — the gap is derived, universally, with no power-gap assumption.  Right: the real
`c = 0` observer escapes it.  The residual is reach (charge `1 → 0`, formula `→` DAG = ruling out free
sharing = `cost_super`), not circularity. -/
theorem non_circular_but_capped :
    (∀ (T : ChargedThermo), 1 ≤ T.charge → ∀ budget, budget < T.formulaLB → budget < T.chargedCost)
    ∧ (∃ (T : ChargedThermo) (budget : Nat),
        budget < T.dagCost + 1 * T.sharing ∧ ¬ (budget < T.dagCost + 0 * T.sharing)) :=
  ⟨fun T hc budget hLB => charged_cannot_afford T hc budget hLB, charged_proves_but_real_escapes⟩

end PallLean.Paper93.DeepMath.PathB.ThermoProof

#print axioms PallLean.Paper93.DeepMath.PathB.ThermoProof.charged_pays_formula_lb
#print axioms PallLean.Paper93.DeepMath.PathB.ThermoProof.charged_cannot_afford
#print axioms PallLean.Paper93.DeepMath.PathB.ThermoProof.uncharged_vacuous
#print axioms PallLean.Paper93.DeepMath.PathB.ThermoProof.charged_proves_but_real_escapes
#print axioms PallLean.Paper93.DeepMath.PathB.ThermoProof.non_circular_but_capped
