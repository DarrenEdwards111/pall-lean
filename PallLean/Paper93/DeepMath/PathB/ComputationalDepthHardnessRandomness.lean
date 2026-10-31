/-!
# The hardness ↔ randomness escape (Kabanets–Imagliazzo) — attack randomness, not the bound

The fuzzy pass surfaced the one barrier-threading route not yet built this session: **don't attack the
circuit lower bound directly — attack randomness.**  Nisan–Wigderson: a hard function *manufactures*
pseudorandomness (derandomizes `BPP`).  Kabanets–Impagliazzo run it in reverse: **derandomization
forces hardness.**  Specifically, if polynomial identity testing (`PIT`) can be *derandomized*
(decided deterministically in `P` / subexponential time), then **`NEXP ⊄ P/poly` or the permanent
requires super-polynomial arithmetic circuits** — a circuit lower bound falls out of removing
randomness from *one specific, well-studied* algorithm.

This is genuinely "out of the box": it is **non-relativizing** (the `NW`/`KI` machinery uses the
algebraic structure of `PIT`, not an oracle), so it threads the Baker–Gill–Solovay barrier — the same
barrier a bare diagonal cannot cross.

* **`hardness_randomness_bridge` (proved, axiom-free)** — `Derandomize PIT` + the `KI` implication
  ⟹ `¬(NEXP ⊆ P/poly ∧ Permanent ∈ poly-arith)`: a lower bound holds on (at least) one side.

**Honest scope.**  Two named sockets, both open — but *different* open problems from P vs NP, and
*studied* ones: (1) `DerandPIT` — a deterministic `PIT` algorithm (we have a *randomized* one via
Schwartz–Zippel; derandomizing it is a central goal, believed true); (2) `ki` — the Kabanets–Imagliazzo
implication itself (a real, deep theorem, socketed here, not re-proved).  The **output** is
`NEXP ⊄ P/poly` **or** a permanent lower bound — *not* `NP ⊄ P/poly`, so it does not by itself give
P vs NP.  It relocates the crossing to **derandomizing `PIT`** — a concrete, attackable target that is
plausibly *easier* than P vs NP and is where much current effort goes.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HardnessRandomness

/-- **The hardness ↔ randomness bridge (Kabanets–Imagliazzo), proved (axiom-free).**  If `PIT` is
derandomized (`hDerand : DerandPIT`), then via the `KI` implication a circuit lower bound follows:
**not both** `NEXP ⊆ P/poly` and `Permanent ∈ poly-size arithmetic circuits` can hold.  So killing
randomness in one algorithm hands back hardness — attack randomness, not the bound. -/
theorem hardness_randomness_bridge
    (DerandPIT NEXPinPpoly PermInPolyArith : Prop)
    (hDerand : DerandPIT)
    (ki : DerandPIT → NEXPinPpoly → PermInPolyArith → False) :
    ¬ (NEXPinPpoly ∧ PermInPolyArith) :=
  fun ⟨h1, h2⟩ => ki hDerand h1 h2

/-- **The Nisan–Wigderson forward direction, recorded (proved).**  The dual: *hardness* manufactures
*pseudorandomness*.  If a hard function exists (`hHard : HardFunction`) and the `NW` implication holds
(`nw : HardFunction → PITDerandomizable`), then `PIT` is derandomizable.  So hardness and
derandomization are two faces of one coin — the `KI` bridge above is this run in reverse. -/
theorem nisan_wigderson_forward
    (HardFunction PITDerandomizable : Prop)
    (hHard : HardFunction) (nw : HardFunction → PITDerandomizable) :
    PITDerandomizable :=
  nw hHard

end PallLean.Paper93.DeepMath.PathB.HardnessRandomness

#print axioms PallLean.Paper93.DeepMath.PathB.HardnessRandomness.hardness_randomness_bridge
#print axioms PallLean.Paper93.DeepMath.PathB.HardnessRandomness.nisan_wigderson_forward
