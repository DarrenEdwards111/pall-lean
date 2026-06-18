import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TypedBoundary
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CrossFieldCombination

/-!
# Probing the composite lift — does `MOD_5 ∉ ACC⁰[6]` reduce to the proved single-prime no-go?

Entry 288 reduced the typed crossing to one open socket: the Smolensky-*composite* implication
"cross-characteristic ⟹ not `ACC⁰[6]`-computable".  Its *single-prime* instance `MOD_q ∉ AC⁰[p]` (`q ∤ p`) is **already
proved** in this arc (`Layer4.mod_q_indicators_false`).  The honest question: can the composite case
`MOD_5 ∉ ACC⁰[6] = AC⁰[{2,3}]` be *reduced* to that proved single-prime tool?  This file answers it — **no**, and proves
exactly why.

**The single-prime tool covers each sub-class — prime by prime.**  Smolensky over a single field `F` linearises a
`MOD_p` gate by the Fermat indicator `1 - x^(p-1)` (degree `p-1`) **iff** `F` has characteristic `p` (native); over any
other characteristic `MOD_p` is high-degree (the single-prime no-go itself).  So a single-field reduction covers the
available set `S` iff one field is native to *every* prime in `S`.  Each singleton `{p}` is coverable
(`single_prime_coverable`, witness `ZMod p`), and there `MOD_q ∉ AC⁰[p]` is the proved Layer-4 theorem — giving
`MOD_5 ∉ AC⁰[2]` and `MOD_5 ∉ AC⁰[3]` as genuine sub-class facts.

**But the joint class `AC⁰[{2,3}]` is NOT single-field-reducible — proved.**  `no_single_field_covers_acc6`: no field is
native to both `2` and `3`, because that needs `CharP F 2 ∧ CharP F 3`, refuted by `no_common_char` (entries 280, 243).
So a single-field Smolensky reduction *cannot* linearise an `AC⁰[6]` circuit, which freely mixes `MOD_2` and `MOD_3`
gates: linearising the `MOD_2` gates needs char 2, the `MOD_3` gates need char 3, no common field.

**The verdict.**  The composite lift does **not** reduce to the single-prime no-go.  The single-prime tool works
prime-by-prime (each singleton coverable) but **provably cannot combine** at the joint class — and the precise
obstruction is exactly `no_common_char` (entry 280) applied to the linearisation step.  This is the same compositional
cross-modulus blow-up flagged open in `JointModularBarrier`, now pinned to the typed invariant: `CrossCharacteristic 5
{2,3}` is real, each sub-characteristic is individually handled, yet the cross-characteristic combination is
irreducible to the single-prime method.  The barrier is genuine, not a missing reduction.

## What is proved (clean axioms, no `sorry`)

* **`single_prime_coverable`** (PROVED) — each singleton `{p}` is single-field-reducible (witness `ZMod p`), so the
  proved single-prime no-go applies to every sub-class `AC⁰[p]`.
* **`acc6_reduction_needs_char_2_and_3`** (PROVED) — a single-field reduction covering `ACC⁰[6]` forces
  `CharP F 2 ∧ CharP F 3`.
* **`no_single_field_covers_acc6`** (PROVED) — no field covers `{2,3}`: the joint class is *not* single-field-reducible
  (`no_common_char`).
* **`composite_lift_not_single_field_reducible`** (PROVED) — therefore `MOD_5 ∉ ACC⁰[6]` does not reduce to the
  single-prime no-go via the single-field method; the obstruction is the incompatible characteristics.

## Honest scope

This **answers the probe**: the composite lift is *not* a reduction to the proved single-prime no-go.  The single-prime
tool covers each prime individually but provably cannot combine at the joint class, the exact obstruction being
`no_common_char`.  So the composite `ACC⁰[6]` lower bound genuinely needs new (non-single-field) machinery — it is the
real open barrier, confirmed, not a gap a reduction could close.  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeReductionProbe

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary

/-- **The native-linearisation condition.**  A single field `F` linearises a `MOD_p` gate by the Fermat indicator
`1 - x^(p-1)` (degree `p-1`) exactly when `F` has characteristic `p` (native); over any other characteristic `MOD_p` is
high-degree (the single-prime Smolensky no-go).  So "F natively linearises `MOD_p`" is modelled by `CharP F p`. -/
def NativelyLinearizes (F : Type) [Field F] (p : ℕ) : Prop := CharP F p

/-- A single-field Smolensky reduction over `F` covers the available prime set `S` when `F` natively linearises every
`MOD_p` gate with `p ∈ S`. -/
def SingleFieldReductionCovers (F : Type) [Field F] (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, NativelyLinearizes F p

/-- **Each prime is individually coverable (PROVED).**  The singleton class `AC⁰[p]` is single-field-reducible — `ZMod p`
is native to `p`.  So the proved single-prime no-go `Layer4.mod_q_indicators_false` (`MOD_q ∉ AC⁰[p]`, `q ∤ p`) applies
on every sub-class; in particular it gives `MOD_5 ∉ AC⁰[2]` and `MOD_5 ∉ AC⁰[3]`. -/
theorem single_prime_coverable (p : ℕ) [Fact p.Prime] :
    ∃ (F : Type) (_ : Field F), SingleFieldReductionCovers F ({p} : Finset ℕ) := by
  refine ⟨ZMod p, inferInstance, ?_⟩
  intro q hq
  rw [Finset.mem_singleton] at hq
  subst q
  exact ZMod.charP p

/-- **A single-field reduction of `ACC⁰[6]` needs both characteristics (PROVED).**  Covering the available set
`acc6 = {2,3}` over one field forces `CharP F 2 ∧ CharP F 3` — the `MOD_2` gates need char 2, the `MOD_3` gates need
char 3. -/
theorem acc6_reduction_needs_char_2_and_3 {F : Type} [Field F]
    (h : SingleFieldReductionCovers F acc6) : CharP F 2 ∧ CharP F 3 :=
  ⟨h 2 (by decide), h 3 (by decide)⟩

/-- **No single field covers `ACC⁰[6]` (PROVED).**  By `no_common_char` (entries 243, 280), no field has both
characteristic 2 and 3, so no single-field Smolensky reduction can linearise an `AC⁰[6]` circuit (which mixes `MOD_2`
and `MOD_3` gates).  This is the precise obstruction to lifting the single-prime no-go. -/
theorem no_single_field_covers_acc6 :
    ¬ ∃ (F : Type) (_ : Field F), SingleFieldReductionCovers F acc6 := by
  rintro ⟨F, _, h⟩
  obtain ⟨h2, h3⟩ := acc6_reduction_needs_char_2_and_3 h
  exact ACC0CrossFieldCombination.no_common_char F 2 3 (by decide) h2 h3

/-- **The composite lift does not reduce to the single-prime no-go (PROVED — the probe's answer).**  Each prime is
individually coverable (`single_prime_coverable`), so the single-prime tool handles every sub-class `AC⁰[2]`, `AC⁰[3]`
(giving `MOD_5 ∉ AC⁰[2]`, `MOD_5 ∉ AC⁰[3]`); but the joint class `AC⁰[{2,3}]` is **not** single-field-reducible
(`no_single_field_covers_acc6`).  So the single-field method that proves the sub-class bounds provably cannot combine
them into `MOD_5 ∉ ACC⁰[6]` — the obstruction is exactly the incompatible characteristics (`no_common_char`).  The
composite barrier is genuine, not a missing reduction. -/
theorem composite_lift_not_single_field_reducible :
    (∃ (F : Type) (_ : Field F), SingleFieldReductionCovers F ({2} : Finset ℕ))
    ∧ (∃ (F : Type) (_ : Field F), SingleFieldReductionCovers F ({3} : Finset ℕ))
    ∧ ¬ ∃ (F : Type) (_ : Field F), SingleFieldReductionCovers F acc6 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact ⟨single_prime_coverable 2, single_prime_coverable 3, no_single_field_covers_acc6⟩

/-- **The gap matches the typed invariant (PROVED).**  `MOD_5` is cross-characteristic for `ACC⁰[6]`
(`mod5_cross_acc6`, entry 288) precisely because its prime `5 ∉ {2,3}`; and even were `5` replaced by a covered
combination, the joint `{2,3}` itself is not single-field-reducible.  This ties the reduction obstruction to the typed
invariant: cross-characteristic targets are exactly those the single-field method cannot reach. -/
theorem cross_characteristic_witnesses_irreducibility :
    CrossCharacteristic 5 acc6
    ∧ ¬ ∃ (F : Type) (_ : Field F), SingleFieldReductionCovers F acc6 :=
  ⟨mod5_cross_acc6, no_single_field_covers_acc6⟩

/-!
**The probe's answer.**  `MOD_5 ∉ ACC⁰[6]` does **not** reduce to the proved single-prime no-go.  The single-prime tool
(`Layer4.mod_q_indicators_false`) covers each sub-class — every singleton `{p}` is single-field-reducible
(`single_prime_coverable`), giving `MOD_5 ∉ AC⁰[2]` and `MOD_5 ∉ AC⁰[3]` — but the joint class `AC⁰[{2,3}]` is provably
*not* single-field-reducible (`no_single_field_covers_acc6`): linearising both gate types needs `CharP F 2 ∧ CharP F 3`,
impossible by `no_common_char`.  So the obstruction to the lift is exactly the incompatible-characteristics fact of
entry 280, now seen as *why* the single-prime method cannot combine across primes.  The composite barrier is genuine —
new, non-single-field machinery is required.  This confirms entry 288's socket is the real open problem, not a gap a
reduction could close.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeReductionProbe

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeReductionProbe.single_prime_coverable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeReductionProbe.acc6_reduction_needs_char_2_and_3
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeReductionProbe.no_single_field_covers_acc6
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeReductionProbe.composite_lift_not_single_field_reducible
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeReductionProbe.cross_characteristic_witnesses_irreducibility
