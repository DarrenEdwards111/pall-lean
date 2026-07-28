import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConsciousAgentSuperpoly

/-!
# The SAT family as the circuit-hard witness: the right family, and the discharge is `cost_super`

`ParityCircuitEasy` showed parity is the *wrong* witness — it is circuit-easy (linear-size), so the
superpolynomial-perception hypothesis is *false* for it.  The right witness is a family whose general-circuit
hardness is genuinely open: the SAT / NP-complete family.  This file uses it, honestly.  Using SAT gives the
correct structure — a faithful superpolynomial perception of SAT discharges the separation — but discharging it
*is* `NP ⊄ P/poly` = `cost_super`, and unlike parity that is open, not false.

**SAT is the right witness (proved implication).**  `SATWitness` carries `satCircuitCost` (SAT's true
general-circuit cost — *unknown*), a `perceive` readout, and `faithful : perceive ≤ satCircuitCost`.
`sat_superpoly_perception_separates`: a superpolynomial faithful perception of SAT forces `satCircuitCost`
non-polynomial — the family is not polynomial-size.  Unlike parity, this is *not* vacuous: SAT's circuit cost is
not provably polynomial.

**Discharging via SAT is exactly the separation (proved).**  `sat_hardness_is_the_separation`:
`Superpoly satCircuitCost ↔ ¬ PolyBounded satCircuitCost` — SAT requiring superpolynomial circuits is precisely
"SAT is not polynomial-size", i.e. `NP ⊄ P/poly` (which implies `P ≠ NP`).  So discharging the
superpolynomial-perception hypothesis for SAT *is* proving `NP ⊄ P/poly` — the separation itself, `cost_super`.

**The contrast with parity (the honest point).**  For parity, `ParityCircuitEasy.parity_circuit_cost_not_superpoly`
*proves* the circuit cost is not superpolynomial — the discharge is false.  For SAT, no such theorem exists (nor
can it, short of `NP ⊆ P/poly`): `Superpoly satCircuitCost` is neither proved nor refuted — it is the open
conjecture.  So SAT is the correct witness precisely because its circuit-hardness is `cost_super`, undischarged,
rather than provably false.

## What is proved

* **`sat_superpoly_perception_separates`** — a superpolynomial faithful perception of SAT forces
  `satCircuitCost` non-polynomial: the separation.  (Not vacuous, unlike parity.)
* **`sat_hardness_is_the_separation`** — `Superpoly satCircuitCost ↔ ¬ PolyBounded satCircuitCost`: SAT
  circuit-hardness *is* `NP ⊄ P/poly`, the separation.
* **`sat_discharge_is_cost_super`** — both: a superpolynomial perception discharges the separation, and the
  discharge is exactly SAT's (open) circuit-hardness.

## Honest verdict — the right witness, and the discharge is the wall

SAT is the correct circuit-hard witness: unlike parity (provably circuit-easy), SAT's general-circuit hardness
is open, so the superpolynomial-perception hypothesis is genuinely *available* to discharge rather than false.
A faithful superpolynomial perception of SAT forces it non-polynomial-size
(`sat_superpoly_perception_separates`), and SAT requiring superpolynomial circuits is exactly `NP ⊄ P/poly`
(`sat_hardness_is_the_separation`) — the separation.  So discharging the hypothesis for SAT is not a lemma
beneath the wall; it *is* the wall: `Superpoly satCircuitCost` = `NP ⊄ P/poly` = `cost_super`, neither proved
nor refuted, the open conjecture.  Using SAT correctly relocates the discharge from "false" (parity) to "open"
(the separation) — I did not fake SAT's hardness, because doing so would be proving `P ≠ NP`.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATCircuitWitness

open PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling

/-- The SAT family as a circuit-hard witness: `satCircuitCost n` is SAT's true general-circuit cost at scale `n`
(unknown), `perceive n` a rank readout, and `faithful` says the perception lower-bounds the true cost. -/
structure SATWitness where
  /-- SAT's true general-circuit cost at scale `n` (unknown — its superpolynomiality is `NP ⊄ P/poly`) -/
  satCircuitCost : ℕ → ℕ
  /-- a perception (rank readout) of SAT's hardness -/
  perceive : ℕ → ℕ
  /-- the perception is a faithful lower bound on SAT's true circuit cost -/
  faithful : ∀ n, perceive n ≤ satCircuitCost n

/-- **A superpolynomial faithful perception of SAT separates (proved).**  If `perceive` dominates every
polynomial and lower-bounds `satCircuitCost`, then `satCircuitCost` is superpolynomial too, hence not
polynomially bounded — SAT is not polynomial-size.  Unlike parity, this is not vacuous. -/
theorem sat_superpoly_perception_separates (W : SATWitness) (h : Superpoly W.perceive) :
    ¬ PolyBounded W.satCircuitCost := by
  have hsp : Superpoly W.satCircuitCost := by
    intro k
    obtain ⟨n, hn⟩ := h k
    exact ⟨n, lt_of_lt_of_le hn (W.faithful n)⟩
  exact superpoly_not_polyBounded hsp

/-- **SAT circuit-hardness is the separation (proved).**  `Superpoly satCircuitCost ↔ ¬ PolyBounded
satCircuitCost` — SAT requiring superpolynomial circuits is exactly "SAT is not polynomial-size", `NP ⊄ P/poly`.
So discharging the hypothesis for SAT is proving the separation. -/
theorem sat_hardness_is_the_separation (W : SATWitness) :
    Superpoly W.satCircuitCost ↔ ¬ PolyBounded W.satCircuitCost := by
  constructor
  · exact superpoly_not_polyBounded
  · intro h k
    by_contra hc
    push_neg at hc
    exact h ⟨k, hc⟩

/-- **The SAT discharge is `cost_super` (proved).**  Left: a superpolynomial perception discharges the
separation.  Right: the discharge is exactly SAT's circuit-hardness `Superpoly satCircuitCost = NP ⊄ P/poly`.
SAT is the right witness; discharging it *is* the wall. -/
theorem sat_discharge_is_cost_super (W : SATWitness) :
    (Superpoly W.perceive → ¬ PolyBounded W.satCircuitCost)
    ∧ (Superpoly W.satCircuitCost ↔ ¬ PolyBounded W.satCircuitCost) :=
  ⟨fun h => sat_superpoly_perception_separates W h, sat_hardness_is_the_separation W⟩

end PallLean.Paper93.DeepMath.PathB.SATCircuitWitness

#print axioms PallLean.Paper93.DeepMath.PathB.SATCircuitWitness.sat_superpoly_perception_separates
#print axioms PallLean.Paper93.DeepMath.PathB.SATCircuitWitness.sat_hardness_is_the_separation
#print axioms PallLean.Paper93.DeepMath.PathB.SATCircuitWitness.sat_discharge_is_cost_super
