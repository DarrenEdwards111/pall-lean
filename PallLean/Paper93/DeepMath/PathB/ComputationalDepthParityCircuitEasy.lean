import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConsciousAgentSuperpoly

/-!
# Discharging the superpolynomial perception for the parity family is FALSE — parity is circuit-easy

Asked to discharge the superpolynomial-perception hypothesis for the parity family.  It cannot be discharged,
and this is not the wall — it is *false*, for an honest reason I must not paper over: **parity is easy for
general circuits.**  `parityₙ = x₁ ⊕ … ⊕ xₙ` is computed by a chain of `O(n)` gates, so parity ∈ P/poly with a
*linear-size* circuit.  Its true general-circuit cost is linear, not superpolynomial.

The `n²` (Khrapchenko) and `n^{5/2}` (Andreev) perceptions we lifted were **formula** lower bounds.  Parity is
formula-hard (`Ω(n²)` formula size) but circuit-easy (`O(n)` circuit size).  So the perception ladder's
veridicality was at the *formula* altitude throughout; the parity family never reaches the general-circuit wall,
because parity is not general-circuit-hard.

**Parity's true circuit cost is polynomial (proved).**  Modelling parity's general-circuit cost by its actual
linear size `fun n => n` (parity has an `O(n)`-gate circuit), `parity_circuit_cost_polynomial` shows it is
polynomially bounded, hence `parity_circuit_cost_not_superpoly`: **it is not superpolynomial.**  So the
superpolynomial-perception hypothesis is *false* for parity — there is nothing to discharge.

**The formula perception over-reports the circuit cost (proved).**  `formula_perception_exceeds_circuit_cost`:
the Khrapchenko perception `n²` strictly *exceeds* parity's linear circuit cost `n` for `n ≥ 2`.  So the `n²`
perception is not a faithful lower bound on the *circuit* cost — it is faithful only to the *formula* cost.
`PerceptionFamily.faithful` (`perceive ≤ trueCircuitCost`) fails for parity.

**So parity is the wrong family.**  `cannot_discharge_superpoly_for_parity`: parity's circuit cost is not
superpolynomial, and the formula perception exceeds it.  Discharging a *general-circuit* superpolynomial
perception needs a genuinely circuit-hard family (an NP-complete one), and proving that is `cost_super` — parity,
being circuit-easy, cannot do it.

## What is proved

* **`parity_circuit_cost_polynomial`** — parity's general-circuit cost (linear) is polynomially bounded.
* **`parity_circuit_cost_not_superpoly`** — hence it is *not* superpolynomial: the hypothesis is false for
  parity.
* **`formula_perception_exceeds_circuit_cost`** — the `n²` formula perception exceeds parity's linear circuit
  cost (`n < n²` for `n ≥ 2`): it is faithful to formula cost, not circuit cost.
* **`cannot_discharge_superpoly_for_parity`** — both: the discharge is false, below the wall, because parity is
  circuit-easy.

## Honest verdict — false below the wall, not at it; parity is circuit-easy

The superpolynomial-perception hypothesis cannot be discharged for the parity family because it is *false*:
parity is easy for general circuits (linear size, parity ∈ P/poly), so its true circuit cost is polynomial and
*not* superpolynomial (`parity_circuit_cost_not_superpoly`).  The `n²` / `n^{5/2}` perceptions we lifted were
*formula* lower bounds, which over-report relative to parity's linear circuit cost
(`formula_perception_exceeds_circuit_cost`) — faithful at the formula altitude, not the circuit altitude.  So
the whole perception/blade ladder was formula-altitude veridicality, and parity — formula-hard but circuit-easy
— is the wrong witness for a general-circuit superpolynomial perception.  Discharging it needs a genuinely
circuit-hard family (NP-complete), which is `cost_super`.  The discharge fails *below* the wall, not at it: not
because I could not prove parity hard, but because parity is *not* hard for circuits.  This is the honest
boundary of the construction, and I flagged it rather than fake a discharge.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ParityCircuitEasy

open PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling

/-- Parity's true general-circuit cost, modelled by its actual linear size: `parityₙ` has an `O(n)`-gate circuit
(a chain of XORs), so parity ∈ P/poly with linear-size circuits.  We take the representative `fun n => n`. -/
def parityCircuitCost : ℕ → ℕ := fun n => n

/-- **Parity's circuit cost is polynomially bounded (proved).**  Linear size is dominated by `n¹`. -/
theorem parity_circuit_cost_polynomial : PolyBounded parityCircuitCost :=
  ⟨1, fun n => by simp [parityCircuitCost]⟩

/-- **Parity's circuit cost is not superpolynomial (proved).**  It is polynomially bounded, so the
superpolynomial-perception hypothesis is *false* for parity — there is nothing to discharge. -/
theorem parity_circuit_cost_not_superpoly : ¬ Superpoly parityCircuitCost :=
  fun h => superpoly_not_polyBounded h parity_circuit_cost_polynomial

/-- **The formula perception exceeds parity's circuit cost (proved).**  The Khrapchenko perception `n²`
strictly exceeds parity's linear circuit cost `n` for `n ≥ 2` — so `n²` is faithful to the *formula* cost, not
the *circuit* cost. -/
theorem formula_perception_exceeds_circuit_cost (n : ℕ) (hn : 2 ≤ n) :
    parityCircuitCost n < n ^ 2 := by
  show n < n ^ 2
  have e : n ^ 2 = n * n := by ring
  rw [e]
  calc n = n * 1 := (Nat.mul_one n).symm
    _ < n * n := mul_lt_mul_of_pos_left (by omega : (1 : ℕ) < n) (by omega : 0 < n)

/-- **The discharge is false, below the wall (proved).**  Parity's circuit cost is not superpolynomial, and the
formula perception over-reports it.  Discharging a general-circuit superpolynomial perception needs a
circuit-hard family (`cost_super`); parity, being circuit-easy, is the wrong witness. -/
theorem cannot_discharge_superpoly_for_parity :
    ¬ Superpoly parityCircuitCost
    ∧ (∀ n, 2 ≤ n → parityCircuitCost n < n ^ 2) :=
  ⟨parity_circuit_cost_not_superpoly, fun n hn => formula_perception_exceeds_circuit_cost n hn⟩

end PallLean.Paper93.DeepMath.PathB.ParityCircuitEasy

#print axioms PallLean.Paper93.DeepMath.PathB.ParityCircuitEasy.parity_circuit_cost_polynomial
#print axioms PallLean.Paper93.DeepMath.PathB.ParityCircuitEasy.parity_circuit_cost_not_superpoly
#print axioms PallLean.Paper93.DeepMath.PathB.ParityCircuitEasy.formula_perception_exceeds_circuit_cost
#print axioms PallLean.Paper93.DeepMath.PathB.ParityCircuitEasy.cannot_discharge_superpoly_for_parity
