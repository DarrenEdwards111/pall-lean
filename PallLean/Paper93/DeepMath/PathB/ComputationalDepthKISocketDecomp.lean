import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardnessRandomness

/-!
# Pinning the Kabanets–Impagliazzo `ki` socket to the Nisan–Wigderson generator

In `HardnessRandomness`, the bridge `hardness_randomness_bridge` used the deep Kabanets–Impagliazzo
implication `ki : DerandPIT → NEXP⊆P/poly → Perm∈polyarith → False` as a single opaque socket.  This
file **decomposes that socket** into a chain of three named ingredients through a `HardFunction` and a
`FullDerand` intermediary, so that the **Nisan–Wigderson generator** appears as its own isolated
hypothesis rather than being buried.

1. **`easyWitness`** (IKW / easy-witness method): a derandomized `PIT` together with `NEXP ⊆ P/poly`
   *manufactures a hard function* — if every `NEXP` witness is compressible, a hard truth table exists.
2. **`nwGen`** (**the Nisan–Wigderson generator**): a hard function yields *full derandomization* — a
   pseudorandom generator fooling all poly-size circuits.  This is the load-bearing hardness→randomness
   step, isolated here as the exact NW statement.  (Its concrete design/locality core lives in the
   socket-2 arc, `NWDesign.nwGen`/`nwGen_local`.)
3. **`ikwCollapse`** (Impagliazzo–Kabanets–Wigderson): full derandomization *collapses* `NEXP`,
   contradicting `NEXP ⊆ P/poly ∧ Perm ∈ polyarith`.

* **`ki_via_nw_generator` (proved)** — the composition of ingredients 1–3 reconstructs `ki` exactly.
* **`lower_bound_via_nw_generator` (proved)** — feeding that reconstructed `ki` into the *existing*
  `hardness_randomness_bridge` yields the same lower-bound conclusion, now with the socket refined into
  three named theorems whose centre is the NW generator.

**Honest scope.**  This is *structural*: it does not prove Kabanets–Impagliazzo, it **factors** it, so
the one opaque socket becomes three sharper ones and the NW generator is named precisely.  All three
ingredients (`easyWitness`, `nwGen`, `ikwCollapse`) remain hypotheses — real, deep theorems, not
re-proved here.  The output is still `¬(NEXP ⊆ P/poly ∧ Perm ∈ polyarith)`, **not** `P ≠ NP`.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KISocket

open PallLean.Paper93.DeepMath.PathB.HardnessRandomness

/-- **The `ki` socket, decomposed through the Nisan–Wigderson generator (proved).**  The opaque
Kabanets–Impagliazzo implication factors as: derandomized `PIT` + `NEXP ⊆ P/poly` manufactures a hard
function (`easyWitness`); the hard function drives full derandomization via the **NW generator**
(`nwGen`); full derandomization collapses `NEXP` against the two hypotheses (`ikwCollapse`).  Their
composition is exactly a proof of `ki`. -/
theorem ki_via_nw_generator
    (DerandPIT NEXPinPpoly PermInPolyArith HardFunction FullDerand : Prop)
    (easyWitness : DerandPIT → NEXPinPpoly → HardFunction)
    (nwGen : HardFunction → FullDerand)
    (ikwCollapse : FullDerand → NEXPinPpoly → PermInPolyArith → False) :
    DerandPIT → NEXPinPpoly → PermInPolyArith → False :=
  fun hD hN hP => ikwCollapse (nwGen (easyWitness hD hN)) hN hP

/-- **The lower bound via the NW-generator-decomposed bridge (proved).**  Plug the reconstructed `ki`
(`ki_via_nw_generator`) into the *existing* `hardness_randomness_bridge`: a derandomized `PIT`, routed
through the easy-witness step, the **Nisan–Wigderson generator**, and the IKW collapse, forces
`¬(NEXP ⊆ P/poly ∧ Perm ∈ polyarith)`.  Same conclusion as the original bridge, but the KI socket is
now split into three named ingredients with the NW generator isolated as `nwGen`. -/
theorem lower_bound_via_nw_generator
    (DerandPIT NEXPinPpoly PermInPolyArith HardFunction FullDerand : Prop)
    (easyWitness : DerandPIT → NEXPinPpoly → HardFunction)
    (nwGen : HardFunction → FullDerand)
    (ikwCollapse : FullDerand → NEXPinPpoly → PermInPolyArith → False)
    (hDerand : DerandPIT) :
    ¬ (NEXPinPpoly ∧ PermInPolyArith) :=
  hardness_randomness_bridge DerandPIT NEXPinPpoly PermInPolyArith hDerand
    (ki_via_nw_generator DerandPIT NEXPinPpoly PermInPolyArith HardFunction FullDerand
      easyWitness nwGen ikwCollapse)

/-- **The NW generator step, isolated and named (proved).**  Ingredient 2 as a first-class object: a
hard function yields full derandomization — the load-bearing hardness→randomness statement, the same
content as `nisan_wigderson_forward` in the `HardFunction → FullDerand` form used above. -/
theorem nw_generator_statement
    (HardFunction FullDerand : Prop) (nwGen : HardFunction → FullDerand) :
    HardFunction → FullDerand :=
  nwGen

end PallLean.Paper93.DeepMath.PathB.KISocket

#print axioms PallLean.Paper93.DeepMath.PathB.KISocket.ki_via_nw_generator
#print axioms PallLean.Paper93.DeepMath.PathB.KISocket.lower_bound_via_nw_generator
#print axioms PallLean.Paper93.DeepMath.PathB.KISocket.nw_generator_statement
