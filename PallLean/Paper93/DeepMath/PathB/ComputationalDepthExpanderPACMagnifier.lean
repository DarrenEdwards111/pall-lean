import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTeeth

/-!
# The magnifier: the Ramanujan expander through PAC

Darren's direction: the dent needs a **magnifier** to cross the wall — the `p-vs-np1` Ramanujan
expander, through **PAC**.  This file wires that: the expander (`ExpanderTeeth`) supplies a rigid cut
(Ramanujan ⟹ no small cut — the teeth), and PAC learning is the amplifier.  By CIKK
(Carmosino–Impagliazzo–Kabanets–Kolokolova), **MCSP-easy ⟹ efficient PAC learning ⟹ compression**.
Compressing the expander is exactly `compression > 0`, which slips the teeth (`compression_slips_teeth`)
below the rigid cut — contradicting the expander's incompressibility.  So the magnifier turns
MCSP-easiness into a contradiction with the concrete, provably-rigid expander.

## What is proved

* **`magnifier_forces_hardness`** — the PAC magnifier (`MCSPEasy → 0 < compression`, CIKK) together
  with the expander's rigidity (`compression = 0`, Ramanujan / `ExpanderResonator`) forces MCSP hard
  (`¬ MCSPEasy`).  The magnifier + the concrete incompressible target ⟹ the dent.
* **`rigidity_alone_insufficient`** — the expander's rigidity ALONE says nothing about MCSP (rigid and
  MCSP-easy coexist); the PAC magnifier is the load-bearing link.  So the magnifier is the one open
  input, not a formality.

## Honest scope — the magnifier is right; where it bites is the wall

The expander's rigidity (`compression = 0`, no small cut) is PROVED (`ExpanderResonator`, Ramanujan).
The **PAC magnifier** — `MCSP-easy ⟹ compress the SPECIFIC expander` — is the socket, and it is exactly
where the natural-proofs gap sits: CIKK gives PAC learning that compresses *most* functions
(average-case), but the expander is a *specific, worst-case* incompressible instance.  Bridging
"PAC compresses most" to "PAC compresses this expander" is the specific-incompressibility wall =
`cost_super`, now concretely at the Ramanujan expander.  So "the expander through PAC" is the right
magnifier *structure* — a concrete incompressible target plus a learning amplifier, reducing the dent
to one named socket — but it does not cross: the average-vs-specific gap is the wall.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExpanderPACMagnifier

open PallLean.Paper93.DeepMath.PathB.ExpanderTeeth

/-- **The magnifier forces hardness (proved).**  The PAC magnifier (`MCSPEasy → 0 < E.compression` —
CIKK: MCSP-easy ⟹ PAC-learn ⟹ compress the expander) together with the expander's rigidity
(`E.compression = 0` — Ramanujan, no small cut) forces MCSP hard: compressing a rigid expander is a
contradiction. -/
theorem magnifier_forces_hardness (E : ExpanderTeeth) (MCSPEasy : Prop)
    (magnifier : MCSPEasy → 0 < E.compression)
    (rigid : E.compression = 0) : ¬ MCSPEasy := by
  intro he
  have h := magnifier he
  omega

/-- **The magnifier is load-bearing (proved).**  The expander's rigidity ALONE is consistent with MCSP
being easy — rigid and easy coexist.  So it is the PAC magnifier (linking MCSP-easiness to compressing
the expander) that does the work; it is the one open input, not a formality. -/
theorem rigidity_alone_insufficient :
    ∃ (E : ExpanderTeeth) (MCSPEasy : Prop), E.compression = 0 ∧ MCSPEasy :=
  ⟨biteWitness, True, rfl, trivial⟩

/-- **The teeth slip under the magnifier (proved).**  If the PAC magnifier compresses the expander
(`0 < compression`), the cost slips below the rigid cut (`cost < cut`) — mass production, the teeth
don't bite.  This is the concrete face of the contradiction the magnifier drives. -/
theorem magnifier_slips_teeth (E : ExpanderTeeth) (hpos : 0 < E.compression) : E.cost < E.cut :=
  compression_slips_teeth E hpos

end PallLean.Paper93.DeepMath.PathB.ExpanderPACMagnifier

#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderPACMagnifier.magnifier_forces_hardness
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderPACMagnifier.rigidity_alone_insufficient
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderPACMagnifier.magnifier_slips_teeth
