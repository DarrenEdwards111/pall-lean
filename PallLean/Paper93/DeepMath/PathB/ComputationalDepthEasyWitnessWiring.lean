import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWGenerator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKISocketDecomp

/-!
# Wiring the `nwGen` socket to the concrete `NWDesign` generator (and naming the easy-witness step)

`KISocket` decomposed the Kabanets–Impagliazzo socket into `easyWitness → nwGen → ikwCollapse`, with
`nwGen : HardFunction → FullDerand` an abstract slot.  The socket-2 arc (`NWDesign`) has the *concrete*
Nisan–Wigderson generator `nwGen f z p` and its locality `nwGen_local`.  This file **connects the two**:
it instantiates the abstract `FullDerand` slot with a `Prop` that literally mentions the concrete
generator, and it packages the locality core into the exact structural fact the NW hybrid argument
consumes.

* **`nwGen_is_q_junta` (proved)** — each concrete generator output bit `nwGen f z p`, as a function of
  the `q²`-bit seed, depends only on the `q` seed coordinates of the design set `nwSet p`
  (`nwGen_local`), and `#(nwSet p) = q` (`nwSet_card`).  So every output bit is a `q`-junta of the
  seed — the read-once-via-design locality the hybrid argument runs on.
* **`GenProduces`** — the `FullDerand` slot made concrete: *some seed `z` makes the generator output
  `p ↦ nwGen f z p` satisfy the downstream usefulness predicate `Good`*.  A `Prop` about `NWDesign.nwGen`.
* **`wired_lower_bound` (proved)** — feeding `FullDerand := GenProduces f Good` into
  `KISocket.lower_bound_via_nw_generator`: with the easy-witness step (`easyWitness`), the NW-generator
  step (`nwHybrid : HardF → GenProduces f Good`, now literally "hard `f` ⟹ the concrete generator
  produces a pseudorandom output"), and the IKW collapse, a derandomized `PIT` forces
  `¬(NEXP ⊆ P/poly ∧ Perm ∈ polyarith)`.

**Honest scope.**  The *new proved content* is `nwGen_is_q_junta` (the locality/junta packaging of the
concrete generator) and the structural wiring `wired_lower_bound`.  The two deep ingredients stay
socketed and are named precisely: `easyWitness` is the **IKW easy-witness method** (derandomized `PIT`
+ `NEXP ⊆ P/poly` manufactures a hard function — `NEXP`-strength; the *existence* of hard functions is
the counting bound in `NaturalProofsBarrier`, making it *constructive* is the open part), and
`nwHybrid` is the **NW hybrid argument** (locality ⟹ pseudorandomness — the analytic core, not proved).
The output is `¬(NEXP ⊆ P/poly ∧ Perm ∈ polyarith)`, **not** `P ≠ NP`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EasyWitnessWiring

open Polynomial
open PallLean.Paper93.DeepMath.PathB.NWDesign
open PallLean.Paper93.DeepMath.PathB.KISocket
open PallLean.Paper93.DeepMath.PathB.HardnessRandomness

variable {q : ℕ} [Fact q.Prime]

/-- **The concrete NW generator output is a `q`-junta of the seed (proved).**  As a function of the
`q²`-bit seed `z`, the output bit `nwGen f z p` depends only on the `q` seed coordinates in the design
set `nwSet p` (from `nwGen_local`), and `#(nwSet p) = q` (from `nwSet_card`).  This is the
read-once-via-design locality — each of the `qᵏ` output bits reads a different `q`-subset of the `q²`
seed bits — that drives the NW hybrid argument. -/
theorem nwGen_is_q_junta (f : (ZMod q → Bool) → Bool) (p : (ZMod q)[X]) :
    (∀ z z' : ZMod q × ZMod q → Bool, (∀ x ∈ nwSet p, z x = z' x) → nwGen f z p = nwGen f z' p)
      ∧ (nwSet p).card = q :=
  ⟨fun z z' h => nwGen_local f z z' p h, nwSet_card p⟩

/-- **The `FullDerand` slot, made concrete with `NWDesign.nwGen`.**  There is a seed `z` whose
generator output `p ↦ nwGen f z p` satisfies the downstream usefulness predicate `Good`
(pseudorandomness / derandomization-usefulness).  A `Prop` that literally mentions the concrete
generator — the bridge between `KISocket`'s abstract `FullDerand` and the socket-2 construction. -/
def GenProduces (f : (ZMod q → Bool) → Bool) (Good : ((ZMod q)[X] → Bool) → Prop) : Prop :=
  ∃ z : ZMod q × ZMod q → Bool, Good (fun p => nwGen f z p)

/-- **The lower bound with the concrete NW generator wired in (proved).**  Instantiating
`KISocket.lower_bound_via_nw_generator` with `FullDerand := GenProduces f Good`: the NW-generator
socket `nwHybrid : HardF → GenProduces f Good` now reads "hardness of `f` ⟹ the concrete generator
produces a pseudorandom output," and composing the easy-witness step, this NW step, and the IKW
collapse forces `¬(NEXP ⊆ P/poly ∧ Perm ∈ polyarith)`.  The abstract `nwGen` slot is thereby wired to
`NWDesign.nwGen` and its locality core `nwGen_is_q_junta`. -/
theorem wired_lower_bound
    (DerandPIT NEXPinPpoly PermInPolyArith HardF : Prop)
    (Good : ((ZMod q)[X] → Bool) → Prop)
    (f : (ZMod q → Bool) → Bool)
    (easyWitness : DerandPIT → NEXPinPpoly → HardF)
    (nwHybrid : HardF → GenProduces f Good)
    (ikwCollapse : GenProduces f Good → NEXPinPpoly → PermInPolyArith → False)
    (hDerand : DerandPIT) :
    ¬ (NEXPinPpoly ∧ PermInPolyArith) :=
  lower_bound_via_nw_generator DerandPIT NEXPinPpoly PermInPolyArith HardF (GenProduces f Good)
    easyWitness nwHybrid ikwCollapse hDerand

end PallLean.Paper93.DeepMath.PathB.EasyWitnessWiring

#print axioms PallLean.Paper93.DeepMath.PathB.EasyWitnessWiring.nwGen_is_q_junta
#print axioms PallLean.Paper93.DeepMath.PathB.EasyWitnessWiring.wired_lower_bound
