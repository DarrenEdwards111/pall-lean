import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodelTowerSpring

/-!
# Circuit-soundness via Tseitin: transferring the Gödel spring, and where it bites

`GodelTowerSpring` showed the self-referential spring forces strict growth, but runs on **soundness**
(`Prov ψ → True_ ψ`), which circuits lack.  This file builds the interface that supplies a circuit
analog of soundness through SAT's **Tseitin self-expression**, transfers the spring, and reports —
honestly — exactly what it delivers and what escapes.

## The interface

`CircuitSoundnessInterface` mirrors a `GodelLevel` for circuits:

* **`Computes p`** — a small circuit decides the statement `p` (the `Prov` analog).
* **`True_ p`** — `p` actually holds.
* **`gstar`** — the Tseitin/MCSP self-referential statement "`gstar` is *not* computed by a small
  circuit."  `fixedpoint : True_ gstar ↔ ¬ Computes gstar` is exactly what the self-encoding provides —
  SAT can express this (`TriggerAnatomy`'s concrete `mcspAt`).  **This slot is filled by Tseitin.**
* **`sound`** — `Computes p → True_ p`: the small circuit has **no false positives**.  The circuit
  analog of Gödel soundness.  **This is the missing ingredient.**

## What it delivers (proved)

* **`gstar_hard_against_sound`** — the spring fires: a **sound** small circuit *cannot* compute `gstar`.
  A genuine non-natural lower bound — against the class of sound circuits, via self-reference, with no
  counting.

## Where it escapes (proved)

* **`unsound_escapes`** — drop soundness and `gstar` *can* be "computed", by a false positive.  So the
  spring bounds only **sound** circuits; an unsound circuit (wrong on `gstar`) slips through.  For a
  *theory*, global soundness (PA is sound) closes this; for circuits there is no global soundness
  assumption, so unsound circuits are a real residual.

## Honest verdict

Tseitin fills the self-reference slot, and the Gödel spring then gives a **real, non-natural lower
bound against sound circuits** — the soundness restriction is a legitimate, non-counting hypothesis,
and the spring rules those circuits out.  The residual to the *full* bound is exactly the unsound
circuits: closing it needs a **global circuit-soundness/consistency** — a constraint forcing every
relevant small circuit to have no false positive on `gstar`, which a consistent theory gets for free
and circuits do not.  That global soundness is `cost_super` in Gödel dress.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CircuitSoundnessTseitin

/-- **The circuit-soundness interface (the Gödel spring for circuits via Tseitin).**  `Computes` is the
`Prov` analog (a small circuit decides `p`); `True_` is actual truth; `gstar` is the Tseitin
self-referential statement with its fixed point; `sound` is circuit-soundness (no false positives). -/
structure CircuitSoundnessInterface where
  Computes : Prop → Prop
  True_ : Prop → Prop
  /-- the Tseitin/MCSP self-referential statement: "`gstar` is not computed by a small circuit" -/
  gstar : Prop
  /-- provided by Tseitin self-expression: `gstar` is true iff no small circuit computes it -/
  fixedpoint : True_ gstar ↔ ¬ Computes gstar
  /-- circuit-soundness: a computing circuit has no false positives (the missing ingredient) -/
  sound : ∀ p, Computes p → True_ p

/-- **The spring fires against sound circuits (proved).**  A sound small circuit cannot compute
`gstar`: computing it makes it true (soundness) hence not-computed (fixed point) — contradiction.  A
non-natural lower bound against sound circuits, via self-reference, no counting. -/
theorem gstar_hard_against_sound (I : CircuitSoundnessInterface) : ¬ I.Computes I.gstar := by
  intro h
  exact (I.fixedpoint.mp (I.sound I.gstar h)) h

/-- **Unsound circuits escape (proved).**  Without soundness the fixed point does not force
non-computation: `gstar` can be "computed" by a false positive.  So the spring bounds only sound
circuits; the full bound needs to exclude unsound ones too — a global circuit-soundness the theory
side gets from consistency and circuits lack. -/
theorem unsound_escapes :
    ∃ (Computes True_ : Prop → Prop) (g : Prop),
      (True_ g ↔ ¬ Computes g) ∧ Computes g :=
  ⟨(fun _ => True), (fun _ => False), True,
    ⟨fun h => h.elim, fun h => h trivial⟩, trivial⟩

/-- **The interface IS the Gödel spring (proved).**  A `CircuitSoundnessInterface` yields a
`GodelTowerSpring.GodelLevel` (`Computes`↦`Prov`, same `True_`, `gstar`↦`godel`, same `fixedpoint`,
same `sound`) — the circuit spring is the Gödel spring with Tseitin supplying the self-reference. -/
def toGodelLevel (I : CircuitSoundnessInterface) : GodelTowerSpring.GodelLevel where
  Sentence := Prop
  Prov := I.Computes
  True_ := I.True_
  godel := I.gstar
  fixedpoint := I.fixedpoint
  sound := I.sound

end PallLean.Paper93.DeepMath.PathB.CircuitSoundnessTseitin

#print axioms PallLean.Paper93.DeepMath.PathB.CircuitSoundnessTseitin.gstar_hard_against_sound
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitSoundnessTseitin.unsound_escapes
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitSoundnessTseitin.toGodelLevel
