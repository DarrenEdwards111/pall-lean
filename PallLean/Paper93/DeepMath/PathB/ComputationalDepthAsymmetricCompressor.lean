import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCostSuperRobust

/-!
# The asymmetric compressor: compress P, expand NP, maintain the inequality

Darren's idea: a compressor that works with **i-th witnesses** and the **N-Frame Lagrangian** may
**compress P** while **expanding NP past the wall**, and the asymmetry **maintains the inequality**.

This file formalizes the shape and locates the wall.  A compressor `size : Obj → ℕ` that is **small on
P** (`size ≤ s`) and **large on NP** (`s < size`) distinguishes the two — that asymmetry *is* the
separation (`asymmetry_separates`).  The N-Frame Lagrangian supplies the NP-expansion: given the
per-level **reading** driven by the i-th witnesses (`2·L d ≤ L(d+1)`), the NP-size amplifies to `2^d`,
past any wall (`lagrangian_expansion` — the `cost_super` amplification engine).

## What is proved

* **`asymmetry_separates`** — a compressor small on P (`size x ≤ s`) and large on NP (`s < size x`),
  with an NP witness, forces `NP ⊄ P` — the inequality.  The asymmetry maintains it: compress one
  side, expand the other, they cannot coincide.
* **`lagrangian_expansion`** — given the reading (NP expands per level, from the i-th witness tower),
  the Lagrangian amplifies the NP-size to `2^d · L 0` — the expansion past the wall.  This is
  `CostSuperRobust.doubling_amplifies`, the same multiplicative engine.
* **`compression_of_P_is_free`** — the P-side is (near) free: P-objects are poly-sized, so a
  circuit-size compressor is automatically small on P.  The load is entirely on the NP-side.

## Honest scope — the asymmetry is right; the NP-expansion is the wall

`asymmetry_separates` is the correct shape (a separating measure / `Π★`), and the Lagrangian is the
correct expansion engine.  Compressing P is (near) free — P is poly by definition.  The open input is
**`expandsNP`**: that the compressor genuinely expands NP past the wall — equivalently, that the
per-level **reading** `2·L d ≤ L(d+1)` holds on SAT's i-th-witness tower.  That reading is the specific
incompressibility of NP = `cost_super` (the `NFrameInstantiation` finding: the Lagrangian gives the
*frame/amplification*; the *reading* is the wall).  So "compress P, expand NP" is the right mechanism
and maintains the inequality *given* the expansion — but the expansion itself is the wall.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AsymmetricCompressor

open PallLean.Paper93.DeepMath.PathB.CostSuperRobust
open PallLean.Paper93.DeepMath.PathB.DemandGeneration

/-- **The asymmetry maintains the inequality (proved).**  A compressor small on P (`size x ≤ s`) and
large on NP (`s < size x`), with an NP witness, forces `NP ⊄ P`: the witness would be both compressed
and expanded, a contradiction.  Compress one side, expand the other — they cannot coincide. -/
theorem asymmetry_separates {Obj : Type} (InP InNP : Obj → Prop) (size : Obj → ℕ) (s : ℕ)
    (compressesP : ∀ x, InP x → size x ≤ s)
    (expandsNP : ∀ x, InNP x → s < size x)
    (witness : Obj) (hw : InNP witness) :
    ¬ (∀ x, InNP x → InP x) := by
  intro hsub
  have hexp := expandsNP witness hw
  have hcomp := compressesP witness (hsub witness hw)
  omega

/-- **The N-Frame Lagrangian expands NP (proved).**  Given the per-level reading `2·L d ≤ L(d+1)` —
driven by the i-th-witness tower — the NP-size amplifies to `2^d · L 0`, past any fixed wall.  This is
the `cost_super` multiplicative engine, re-read as the Lagrangian expansion. -/
theorem lagrangian_expansion (L : TowerDemand) (reading : ∀ d, 2 * L.D d ≤ L.D (d + 1)) (d : ℕ) :
    2 ^ d * L.D 0 ≤ L.D d :=
  doubling_amplifies L reading d

/-- **Compressing P is (near) free (proved).**  If every P-object has size at most the poly bound `s`,
the compressor is automatically small on P.  The asymmetry's load is entirely on the NP-expansion. -/
theorem compression_of_P_is_free {Obj : Type} (InP : Obj → Prop) (size : Obj → ℕ) (s : ℕ)
    (hpoly : ∀ x, InP x → size x ≤ s) : ∀ x, InP x → size x ≤ s :=
  hpoly

end PallLean.Paper93.DeepMath.PathB.AsymmetricCompressor

#print axioms PallLean.Paper93.DeepMath.PathB.AsymmetricCompressor.asymmetry_separates
#print axioms PallLean.Paper93.DeepMath.PathB.AsymmetricCompressor.lagrangian_expansion
#print axioms PallLean.Paper93.DeepMath.PathB.AsymmetricCompressor.compression_of_P_is_free
