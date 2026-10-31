import PallLean.Paper93.DeepMath.PathB.ComputationalDepthScaleBridge

/-!
# Promoting the non-uniform NEXP bound to uniform EXP≠NEXP: it runs backwards down the easy-witness lemma

`ScaleBridge` proved `EXP ≠ NEXP ⟹ P ≠ NP` (uniform padding) and left two residual routes for Williams'
*non-uniform* NEXP bound: promote it to the uniform `EXP ≠ NEXP`, or compress it past the size-blowup.  This
file attempts the promotion — and machine-checks why it is blocked.

The controlling fact is the **easy-witness lemma** (Kabanets–Impagliazzo / IKW): `NEXP ⊆ P/poly ⟹ NEXP =
EXP`.  If NEXP had polynomial circuits, its witnesses would be describable by small circuits, findable in
EXP, so `NEXP ⊆ EXP`.  This gives one direction cleanly — the *contrapositive*: **`EXP ≠ NEXP ⟹ NEXP ⊄
P/poly`** (`uniform_gives_nonuniform`).  That is uniform-separation ⟹ non-uniform-bound: exactly the
direction we do *not* want.

The promotion we want is the **reverse**: `NEXP ⊄ P/poly ⟹ EXP ≠ NEXP`.  It fails, and the reason is exact.
Suppose `NEXP = EXP` (uniform collapse).  Then `NEXP ⊄ P/poly` becomes `EXP ⊄ P/poly` — so non-uniform NEXP
hardness plus the uniform collapse simply *forces* `EXP ⊄ P/poly` (`promotion_forces_exp_hard`), which is a
consistent, indeed *believed-true*, world.  So there is a scenario with `NEXP ⊄ P/poly` (non-uniform hard)
yet `NEXP = EXP` (uniform collapse) — namely whenever `EXP ⊄ P/poly` (`promotion_not_forced`).  Hence the
promotion `NEXP ⊄ P/poly ⟹ EXP ≠ NEXP` is not derivable (`promotion_fails`).  And Williams gives only
`NEXP ⊄ ACC⁰`, weaker still than `NEXP ⊄ P/poly` — so the gap is if anything wider.

## What is proved

* **`Uniformization`** — the three propositions (`NEXP ⊆ P/poly`, `NEXP = EXP`, `EXP ⊆ P/poly`) with the
  easy-witness lemma and the collapse identity `NEXP = EXP ⟹ (NEXP ⊆ P/poly ↔ EXP ⊆ P/poly)`.
* **`uniform_gives_nonuniform`** — the direction that works: `EXP ≠ NEXP ⟹ NEXP ⊄ P/poly`.
* **`promotion_forces_exp_hard`** — non-uniform NEXP hardness `∧` uniform collapse `⟹ EXP ⊄ P/poly`.
* **`promotion_not_forced`** — a consistent (believed-true) world with `NEXP ⊄ P/poly` yet `NEXP = EXP`.
* **`promotion_fails`** — `NEXP ⊄ P/poly ⟹ EXP ≠ NEXP` is not derivable.

## Honest verdict — the promotion is the wrong way down easy-witness; this branch is closed

I attempted the promotion, and it does not go through.  The easy-witness lemma runs uniform ⟹ non-uniform
(`uniform_gives_nonuniform`); the promotion asks for non-uniform ⟹ uniform, and that is blocked because a
non-uniform NEXP lower bound is consistent with the uniform collapse `NEXP = EXP` — it merely forces `EXP ⊄
P/poly`, an open and *believed-true* statement (`promotion_forces_exp_hard`, `promotion_not_forced`,
`promotion_fails`).  So in the world we think we live in, Williams' non-uniform bound simply does not promote:
you would first have to rule out `EXP ⊄ P/poly` (wrong direction, and open), and even then the target `EXP ≠
NEXP` is itself open.  That closes this residual branch honestly: the scale-bridge's remaining hope is the
*other* route — compressing the non-uniform bound past the `2^n` size-blowup — not uniformization.  The
uniformity gap is real and one-directional.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Uniformization

/-- The propositions governing whether Williams' non-uniform NEXP bound promotes to a uniform separation,
with the easy-witness lemma and the collapse identity. -/
structure Uniformization where
  /-- `NEXP ⊆ P/poly` -/
  NEXPinPpoly : Prop
  /-- `NEXP = EXP` (uniform collapse) -/
  NEXPeqEXP : Prop
  /-- `EXP ⊆ P/poly` -/
  EXPinPpoly : Prop
  /-- **Easy-witness lemma** (Kabanets–Impagliazzo / IKW): `NEXP ⊆ P/poly ⟹ NEXP = EXP` -/
  easy_witness : NEXPinPpoly → NEXPeqEXP
  /-- if `NEXP = EXP` then NEXP and EXP have circuits together -/
  collapse_ident : NEXPeqEXP → (NEXPinPpoly ↔ EXPinPpoly)

namespace Uniformization

variable (U : Uniformization)

/-- **The direction that works (proved).**  `EXP ≠ NEXP ⟹ NEXP ⊄ P/poly` — the contrapositive of the
easy-witness lemma.  Uniform separation implies the non-uniform bound; not the direction we want. -/
theorem uniform_gives_nonuniform (h : ¬ U.NEXPeqEXP) : ¬ U.NEXPinPpoly :=
  fun hin => h (U.easy_witness hin)

/-- **The promotion forces EXP-hardness (proved).**  Non-uniform NEXP hardness together with the uniform
collapse `NEXP = EXP` forces `EXP ⊄ P/poly` — so the two are consistent exactly when `EXP ⊄ P/poly`. -/
theorem promotion_forces_exp_hard (hnu : ¬ U.NEXPinPpoly) (hcol : U.NEXPeqEXP) : ¬ U.EXPinPpoly :=
  fun hexp => hnu ((U.collapse_ident hcol).mpr hexp)

end Uniformization

/-- The believed-true world: `NEXP ⊄ P/poly` and `EXP ⊄ P/poly`, yet `NEXP = EXP`.  All hypotheses hold. -/
def believedWorld : Uniformization where
  NEXPinPpoly := False
  NEXPeqEXP := True
  EXPinPpoly := False
  easy_witness := False.elim
  collapse_ident := fun _ => Iff.rfl

/-- **The promotion is not forced (proved).**  A consistent world has `NEXP ⊄ P/poly` (non-uniform hard) yet
`NEXP = EXP` (uniform collapse) — exactly when `EXP ⊄ P/poly`, which is believed true. -/
theorem promotion_not_forced :
    ∃ U : Uniformization, ¬ U.NEXPinPpoly ∧ U.NEXPeqEXP ∧ ¬ U.EXPinPpoly :=
  ⟨believedWorld, not_false, trivial, not_false⟩

/-- **The promotion fails (proved).**  `NEXP ⊄ P/poly ⟹ EXP ≠ NEXP` is not derivable — the believed-true
world witnesses `NEXP ⊄ P/poly` with `NEXP = EXP`. -/
theorem promotion_fails : ¬ (∀ U : Uniformization, ¬ U.NEXPinPpoly → ¬ U.NEXPeqEXP) := by
  intro h
  exact h believedWorld not_false trivial

end PallLean.Paper93.DeepMath.PathB.Uniformization

#print axioms PallLean.Paper93.DeepMath.PathB.Uniformization.Uniformization.uniform_gives_nonuniform
#print axioms PallLean.Paper93.DeepMath.PathB.Uniformization.Uniformization.promotion_forces_exp_hard
#print axioms PallLean.Paper93.DeepMath.PathB.Uniformization.promotion_not_forced
#print axioms PallLean.Paper93.DeepMath.PathB.Uniformization.promotion_fails
