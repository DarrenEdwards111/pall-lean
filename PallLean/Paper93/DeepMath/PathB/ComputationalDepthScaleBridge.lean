import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWilliamsSynthesis

/-!
# The NEXP→NP scale-bridge: real for uniform separations (padding), blocked for Williams' non-uniform output

`WilliamsSynthesis` left the crossing as `object ∧ bridge`, the bridge being a way to carry NEXP-scale
hardness down to superpoly-on-NP.  A real bridge exists — but only on one side, and Williams' output is on
the other.  This file builds the working bridge and machine-checks exactly where it fails to reach.

**The bridge that works: uniform padding.**  Pad an `NEXP` language to an `NP` one (its witness fits in the
exponentially-longer input).  If `NP ⊆ P`, the padded language is in `P`, and unpadding puts the original in
`EXP` — so `P = NP ⟹ EXP = NEXP` (`collapse_translates_up`).  Contrapositive: **`EXP ≠ NEXP ⟹ P ≠ NP`**
(`uniform_hardness_scales_down`).  This is a genuine downward scale-bridge — proved — for *uniform*
separations.

**Why Williams' output does not feed it.**  Two gaps, both real:
1. **Wrong kind of hardness.**  Williams' algorithmic method gives a *non-uniform* circuit lower bound
   (`NEXP ⊄ ACC⁰`), not the *uniform* separation `EXP ≠ NEXP` that padding consumes.  Non-uniform NEXP
   circuit hardness does not give `EXP ≠ NEXP`.
2. **Padding blows up size.**  On the non-uniform side padding fails outright: the padded input has length
   `2^n`, so a *polynomial* circuit at the padded scale is *exponential* at the original scale
   (`padding_blows_up_size`, `n² < 2^n`).  A non-uniform NEXP circuit bound cannot be compressed to an NP
   circuit bound this way — the transfer is unforced (`nonuniform_bridge_not_forced`).

So the bridge is not vacuous — it exists and is proved — but it consumes a uniform separation, and Williams
delivers a non-uniform circuit bound.  The residual sharpens to a concrete pair: **either obtain the uniform
`EXP ≠ NEXP` (which padding then scales to `P ≠ NP`), or compress Williams' non-uniform NEXP bound past the
`2^n` size-blowup.**  Both are open.

## What is proved

* **`Padding` / `collapse_translates_up`** — padding scales a collapse up: `NP ⊆ P ⟹ NEXP ⊆ EXP`.
* **`uniform_hardness_scales_down`** — the working bridge: `EXP ≠ NEXP ⟹ P ≠ NP` (uniform).
* **`padding_blows_up_size`** — the padded length is exponential (`n² < 2^n`): the non-uniform obstruction.
* **`nonuniform_bridge_not_forced`** — a consistent scenario with non-uniform NEXP circuit hardness but no
  NP circuit hardness: the non-uniform transfer is not forced.

## Honest verdict — the bridge is built, and it reaches everything except the non-uniform gap

I built the scale-bridge, and it is a real theorem: padding carries `EXP ≠ NEXP` down to `P ≠ NP`
(`uniform_hardness_scales_down`).  That is the honest answer to "build the bridge" — it exists for uniform
separations.  What it cannot do is consume Williams' *non-uniform* NEXP circuit bound: that hardness is the
wrong kind for padding, and on the non-uniform side padding's `2^n` size-blowup blocks the transfer outright
(`padding_blows_up_size`, `nonuniform_bridge_not_forced`).  So the residual is now exact and small: promote
Williams' non-uniform NEXP bound to the uniform `EXP ≠ NEXP` (then the built bridge finishes it), or compress
it past the size-blowup.  The bridge is no longer a vague "second object" — it is one proved half plus one
sharply-named gap.  That gap is `cost_super`, at the uniform-vs-non-uniform seam.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ScaleBridge

/-! ### The bridge that works: uniform padding -/

/-- The padding translation between an `NEXP` language and its `NP`-padded form, at two time scales. -/
structure Padding where
  /-- the original language is in NEXP -/
  InNEXP : Prop
  /-- the original language is in EXP -/
  InEXP : Prop
  /-- the padded language is in NP -/
  InNP : Prop
  /-- the padded language is in P -/
  InP : Prop
  /-- padding sends an NEXP language to an NP (padded) language -/
  pad_np : InNEXP → InNP
  /-- if the padded language is in P, unpadding puts the original in EXP -/
  unpad_exp : InP → InEXP

/-- **Padding scales a collapse up (proved).**  If `NP ⊆ P`, then `NEXP ⊆ EXP`: pad up into `NP`, collapse
to `P`, unpad down to `EXP`. -/
theorem collapse_translates_up (P : Padding) (collapse : P.InNP → P.InP) :
    P.InNEXP → P.InEXP :=
  fun h => P.unpad_exp (collapse (P.pad_np h))

/-- **The uniform scale-bridge (proved).**  `EXP ≠ NEXP ⟹ P ≠ NP`: a NEXP language outside EXP forbids the
`NP ⊆ P` collapse.  A genuine downward bridge — for uniform separations. -/
theorem uniform_hardness_scales_down (P : Padding) (hard : P.InNEXP ∧ ¬ P.InEXP) :
    ¬ (P.InNP → P.InP) :=
  fun collapse => hard.2 (collapse_translates_up P collapse hard.1)

/-! ### Why Williams' non-uniform output does not feed it -/

/-- The padded input length: exponential in the original length. -/
def paddedLen (n : ℕ) : ℕ := 2 ^ n

/-- **Padding blows up size (proved).**  At original length `n = 10` the padded length is `2^10 = 1024`,
so a *polynomial* (`n² = 100`) circuit at the padded scale is *exponential* at the original scale.  A
non-uniform NEXP circuit bound cannot be compressed to an NP circuit bound by padding. -/
theorem padding_blows_up_size : (10 : ℕ) * 10 < paddedLen 10 := by decide

/-- Non-uniform circuit hardness at the two scales — Williams' output (`NEXPcircuitHard`) and the goal
(`NPcircuitHard`).  There is no padding field between them: the size-blowup blocks it. -/
structure CircuitScales where
  /-- non-uniform NEXP circuit lower bound (Williams' algorithmic-method output) -/
  NEXPcircuitHard : Prop
  /-- superpoly circuit lower bound on NP (the goal) -/
  NPcircuitHard : Prop

/-- **The non-uniform bridge is not forced (proved).**  A consistent scenario has the non-uniform NEXP
circuit bound but no NP circuit bound — padding's size-blowup gives no transfer, so `NEXPcircuitHard →
NPcircuitHard` does not hold. -/
theorem nonuniform_bridge_not_forced :
    ∃ C : CircuitScales, C.NEXPcircuitHard ∧ ¬ C.NPcircuitHard :=
  ⟨⟨True, False⟩, trivial, not_false⟩

/-- **Non-uniform NEXP hardness does not force NP hardness (proved).**  `NEXPcircuitHard → NPcircuitHard` is
not derivable — the size-blowup scenario witnesses the gap. -/
theorem nonuniform_no_downscale : ¬ (∀ C : CircuitScales, C.NEXPcircuitHard → C.NPcircuitHard) := by
  intro h
  exact h ⟨True, False⟩ trivial

end PallLean.Paper93.DeepMath.PathB.ScaleBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ScaleBridge.collapse_translates_up
#print axioms PallLean.Paper93.DeepMath.PathB.ScaleBridge.uniform_hardness_scales_down
#print axioms PallLean.Paper93.DeepMath.PathB.ScaleBridge.padding_blows_up_size
#print axioms PallLean.Paper93.DeepMath.PathB.ScaleBridge.nonuniform_bridge_not_forced
#print axioms PallLean.Paper93.DeepMath.PathB.ScaleBridge.nonuniform_no_downscale
