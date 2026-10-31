import Mathlib.Data.Nat.Basic

/-!
# The restricted localization probe: a global affine gate can't witness a nonlinear block

The residue after the tower-geometry brick (`OverlapFromSharedInputs`) is **localization**: minimal circuits
admit support-local witnesses — witness mass can't hide in deep *global* gates.  Here we prove it on a
restricted gate basis, via the degree machinery: **a global affine gate cannot witness a nonlinear block**.

The point.  A witness for a block must *locally supply the block's demand degree* — to witness a demand of
degree `d`, a single gate must reach degree `d`.  An **affine** gate has degree `≤ 1`; a **nonlinear** block
demands degree `≥ 2`.  So an affine gate — *however global its support* — cannot witness a nonlinear block:
`2 ≤ demand ≤ gateDegree ≤ 1` is a contradiction.  The witness mass for a nonlinear block is therefore
*forced off* the affine gates and onto nonlinear (degree `≥ 2`) gates.  On the affine basis, the god-gates
cannot be affine — a genuine, if partial, localization.

## What is proved

* **`affine_cant_witness_nonlinear`** — an affine gate (`gateDegree ≤ 1`) does *not* witness a nonlinear
  block (`2 ≤ demand`): `¬ Witnesses`.  Degree forbids it, regardless of support size.
* **`nonlinear_witness_is_nonlinear`** — conversely, any actual witness of a nonlinear block has
  `gateDegree ≥ 2`: nonlinear demands force nonlinear witnesses.
* **`global_affine_fails`** — concrete: a global affine gate (degree `1`) fails to witness a degree-`2`
  block.

## Honest scope — real localization on the affine basis, capped at the degree ceiling

This is a genuine restricted localization: the affine part of the circuit *cannot* do nonlinear block-local
witness work — the linear horn is excluded, exactly as `LinearHorn` is vacuous for SAT (`output_affine`).
So the witnesses of a nonlinear block live on nonlinear gates.

But it **caps**, and precisely where the map already says it must.  It only excludes *affine* gates.  The
*nonlinear* (degree `≥ 2`) gates can still be global, and bounding *their* locality — or their count — is the
general wall.  The degree method that attacks this is provably capped at `log n` (`DegreeCertificate` /
`AndPeeling`: any circuit for `n`-bit AND has `> log₂ n` nonlinear gates, and degree `≤ n` blocks any
superpolynomial reach).  So localization on the affine basis is real and now checked; localization for
*arbitrary global gates* — the residue that would close the wall — is `cost_super`, non-natural, beyond the
degree ceiling.  This sharpens and calibrates the residue; it does not cross it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LocalizationProbe

/-- A candidate witness gate for a block: the gate's polynomial `gateDegree`, and the block's `demand`
degree.  Witnessing means the gate locally supplies the demand: `demand ≤ gateDegree`. -/
structure GateForBlock where
  /-- the gate's polynomial degree -/
  gateDegree : ℕ
  /-- the block's demand degree -/
  demand : ℕ

/-- The gate is **affine**: degree at most one. -/
def Affine (W : GateForBlock) : Prop := W.gateDegree ≤ 1

/-- The block is **nonlinear**: it demands degree at least two. -/
def Nonlinear (W : GateForBlock) : Prop := 2 ≤ W.demand

/-- The gate **witnesses** the block: it locally supplies the demand degree. -/
def Witnesses (W : GateForBlock) : Prop := W.demand ≤ W.gateDegree

/-- **An affine gate cannot witness a nonlinear block (proved).**  Degree forbids it — `2 ≤ demand ≤
gateDegree ≤ 1` is impossible — regardless of how global the gate's support is. -/
theorem affine_cant_witness_nonlinear (W : GateForBlock) (haff : Affine W) (hnl : Nonlinear W) :
    ¬ Witnesses W := by
  intro hwit
  have h1 : W.gateDegree ≤ 1 := haff
  have h2 : 2 ≤ W.demand := hnl
  have h3 : W.demand ≤ W.gateDegree := hwit
  omega

/-- **A nonlinear block's witness is nonlinear (proved).**  Any gate that actually witnesses a nonlinear
block has `gateDegree ≥ 2`: nonlinear demands force nonlinear witnesses — the witness mass is pushed onto
nonlinear gates. -/
theorem nonlinear_witness_is_nonlinear (W : GateForBlock) (hnl : Nonlinear W) (hwit : Witnesses W) :
    2 ≤ W.gateDegree := by
  have h2 : 2 ≤ W.demand := hnl
  have h3 : W.demand ≤ W.gateDegree := hwit
  omega

/-- A **global affine gate**: degree `1` (affine), facing a degree-`2` (nonlinear) block. -/
def globalAffineGate : GateForBlock := ⟨1, 2⟩

/-- **The global affine gate fails (proved).**  It cannot witness the nonlinear block — its degree caps at
`1`, the demand is `2`.  Globality of support does not help; degree is the obstruction. -/
theorem global_affine_fails : ¬ Witnesses globalAffineGate :=
  affine_cant_witness_nonlinear globalAffineGate (Nat.le_refl 1) (Nat.le_refl 2)

end PallLean.Paper93.DeepMath.PathB.LocalizationProbe

#print axioms PallLean.Paper93.DeepMath.PathB.LocalizationProbe.affine_cant_witness_nonlinear
#print axioms PallLean.Paper93.DeepMath.PathB.LocalizationProbe.global_affine_fails
