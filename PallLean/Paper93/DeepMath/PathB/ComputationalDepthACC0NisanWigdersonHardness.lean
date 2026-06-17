import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonYaoCircuit

/-!
# HardnessExcludesCircuit — the definitional link, and the collision with the reconstructed circuit (proved)

Entry 192 left **`HardnessExcludesCircuit`** as a sub-socket of the NW hybrid argument: a hard function has no small
circuit, so exhibiting one is contradictory.  This file discharges it — but it is important to be exact about *what*
this socket is, because it is easy to overclaim.

**This socket is the definitional link, not a circuit lower bound.**  "Hard against size `s`" *means* "no circuit of
size `≤ s` computes `f`".  So `HardnessExcludesCircuit` — that hardness plus a small circuit yields a contradiction — is
genuinely provable precisely because it is the *unfolding of the definition of hardness*.  What this file does **not**
do, and what no argument of this kind can do, is prove that any *particular* function is hard: that is the genuine
circuit lower bound the **entire conditional anatomy rests on** (the `NoEasyWitnessHardFn` / easy-witness side — itself
of separation strength).  Hardness of the witness function is the **irreducible assumption**; here we only formalise
that, *given* that assumption, a small circuit collides with it.

The genuinely useful theorem is the **collision**: the small reconstructed circuit produced by the NW chain (entries
194–196: size `≤ predictorSize + numOther·2^k`, and correct) computes `f`; if `f` is hard against that size, this is a
contradiction — which is exactly how `HardnessExcludesCircuit` is used in the hybrid argument.

## What is proved (clean axioms, no `sorry`)

* **`Computes`** / **`HasCircuitOfSize`** / **`HardFor`** — over the entry-196 `Circ` model: `C` computes `f`; `f` has a
  circuit of size `≤ s`; `f` is hard against size `s` (`:= ¬ HasCircuitOfSize f s`, the *definition* of hardness).
* **`hardFor_excludes`** — the definitional link: `HardFor f s → HasCircuitOfSize f s → False` (literally `hard hc`).
* **`hardness_collision`** — the substantive collision: a concrete circuit `C` of size `≤ s` computing `f` contradicts
  `HardFor f s` — the form in which the NW reconstruction (entries 194–196) collides with hardness.
* **`hardnessExcludesCircuit_discharge`** — discharges the **entry-192 `HardnessExcludesCircuit` socket** for the
  concrete predicates `HardFor`/`HasCircuitOfSize`.

## Honest scope

This proves only the **definitional** content of `HardnessExcludesCircuit` — that hardness (defined as the absence of a
small circuit) excludes a small circuit — concretely over the `Circ` gate model, and the collision with the
reconstructed circuit.  It does **not** prove that any function is hard; that circuit lower bound is the irreducible
input (`NoEasyWitnessHardFn`), of separation strength, and is *not* discharged here.  Closing this socket completes the
NW hybrid argument's *plumbing* down to the single genuine assumption (a hard function exists).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHardness

open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYaoCircuit (Circ)
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHybrid (HardnessExcludesCircuit)

/-- **A circuit computes a function.**  `C.eval` agrees with `f` on every input. -/
def Computes {n : ℕ} (C : Circ n) (f : (Fin n → Bool) → Bool) : Prop := ∀ x, C.eval x = f x

/-- **`f` has a circuit of size `≤ s`.**  Some circuit of gate count `≤ s` computes `f`. -/
def HasCircuitOfSize {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circ n, C.size ≤ s ∧ Computes C f

/-- **`f` is hard against size `s`.**  *By definition*, no circuit of size `≤ s` computes `f`.  (This is the meaning of
hardness; that a *specific* `f` satisfies it is the circuit lower bound, not proved here.) -/
def HardFor {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop := ¬ HasCircuitOfSize f s

/-- **The definitional link (PROVED).**  Hardness against size `s` excludes a size-`s` circuit: it is literally the
negation `HardFor f s = ¬ HasCircuitOfSize f s` applied to the circuit.  This is the *entire* content of
`HardnessExcludesCircuit` — the definition unfolded, not a lower bound. -/
theorem hardFor_excludes {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hard : HardFor f s) (hc : HasCircuitOfSize f s) : False := hard hc

/-- **The collision with a concrete small circuit (PROVED).**  A concrete circuit `C` of size `≤ s` computing `f`
contradicts `HardFor f s`.  This is the form in which the NW reconstruction (entries 194–196: the reconstructed circuit
has size `≤ predictorSize + numOther·2^k` and computes `f`) collides with the hardness of the witness function — the use
of `HardnessExcludesCircuit` in the hybrid argument. -/
theorem hardness_collision {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ) (C : Circ n)
    (hsize : C.size ≤ s) (hcomp : Computes C f) (hard : HardFor f s) : False :=
  hard ⟨C, hsize, hcomp⟩

/-- **Discharging the entry-192 `HardnessExcludesCircuit` socket (PROVED).**  For the concrete predicates `HardFor` /
`HasCircuitOfSize` over the `Circ` model, hardness and a small circuit are contradictory — `fun hard hc => hard hc`.
This closes the socket's *definitional* content; the hardness of the witness function (`HardFor f s` for the actual
witness) remains the irreducible assumption supplied by `NoEasyWitnessHardFn`. -/
theorem hardnessExcludesCircuit_discharge {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ) :
    HardnessExcludesCircuit (HardFor f s) (HasCircuitOfSize f s) :=
  fun hard hc => hard hc

end PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHardness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHardness.hardFor_excludes
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHardness.hardness_collision
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHardness.hardnessExcludesCircuit_discharge
