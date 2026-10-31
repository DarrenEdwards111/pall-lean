import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRankLoweringTarget

/-!
# Beyond whole‑support fixing — the reuse switching target, and why the generic bound can't separate

The rung‑ladder (read‑once → bounded‑overlap → bounded‑depth tree) is exhausted: every rung lowered rank by fixing
some gate's *whole support*, and unbounded re‑use defeats that hook.  This file names the next missing mechanism
and runs the reuse case to its honest conclusion.

A genuine, fully general fact survives — `restricted_rank_le_two_pow_free`: after *any* restriction leaving `u`
free variables, the realized charges depend on `x` only through its free coordinates, so
`realizedClasses ≤ 2^u`, **for any circuit, any re‑use**.  So restrictions *do* lower effective rank despite
reuse — but to the **circuit‑independent** bound `2^{#free vars}`.

That bound cannot separate, for a precise reason: it applies *equally to the hard family*.  The Tseitin/expander
charge realizes the full `2^{#free}` (`expander_realizedClasses_eq` — the generic bound is *tight*), so a
restriction leaving `u` free variables lowers **both** the circuit and the hard family to `≤ 2^u`: no gap.  The
whole‑support hook gave a *circuit‑specific* drop (`q^{#free gates} ≪ 2^{#free vars}` for structured circuits)
that beat the hard family — and that is exactly what unbounded re‑use kills.

## What is proved (clean axioms, no `sorry`)

* `override_eq_extend` — a restricted input is determined by the free coordinates (`override x ρ` factors through
  `x|_free`).
* `restricted_rank_le_two_pow_free` — **the generic rank‑lowering, despite arbitrary reuse**:
  `realizedClasses ≤ 2^{#free variables}`.

## The named target (the missing mechanism)

* `RandomRestrictionLowersEffectiveRankDespiteReuse` — a restriction drives a poly‑size ACC⁰ circuit's realized
  effective rank *strictly below* the surviving Tseitin rank, **without** fixing any gate's whole support — i.e. a
  *circuit‑specific* drop under unbounded reuse.  This is the new mechanism beyond whole‑support fixing.

## Honest verdict — the negative branch

The reuse case lands on HAL's negative outcome: with the whole‑support hook gone, the only surviving rank bound is
the circuit‑independent `2^{#free vars}`, which is *tight* (achieved by the expander) and therefore cannot
distinguish a poly‑size ACC⁰ circuit from the hard family.  A separation needs a *circuit‑specific* drop under
reuse — the circuit shrinking faster than the generic free‑variable bound — which is precisely Håstad‑shrinkage /
Razborov–Smolensky‑correlation content (`RandomRestrictionLowersEffectiveRankDespiteReuse`), `NP ⊄ ACC⁰`‑strength,
under the PRF‑free naturalness ceiling.  So the holonomy/restriction route reaches its boundary here: the next
move is the Williams/correlation mechanism, not another counting‑style rung.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCReuseSwitchingTarget

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl
open PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank
open PallLean.Paper93.DeepMath.PathB.ACCRankLoweringTarget

variable {n : ℕ} {W : Type*}

/-- The free coordinates of `x` under restriction `ρ`. -/
def freeRestrict (ρ : Fin n → Option Bool) (x : Fin n → Bool) : {v : Fin n // ρ v = none} → Bool :=
  fun v => x v.val

/-- Rebuild a full input from free‑coordinate values and `ρ`'s fixed values. -/
def extendFree (ρ : Fin n → Option Bool) (fs : {v : Fin n // ρ v = none} → Bool) : Fin n → Bool :=
  fun v => if h : ρ v = none then fs ⟨v, h⟩ else (ρ v).getD false

/-- **A restricted input is determined by its free coordinates (proved).** -/
theorem override_eq_extend (ρ : Fin n → Option Bool) (x : Fin n → Bool) :
    override x ρ = extendFree ρ (freeRestrict ρ x) := by
  funext v
  unfold override extendFree freeRestrict
  by_cases h : ρ v = none
  · rw [dif_pos h, h]
    rfl
  · rw [dif_neg h]
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
    rw [hb]
    rfl

/-- **The generic rank‑lowering, despite arbitrary reuse (proved): `realizedClasses ≤ 2^{#free variables}`.**  The
restricted charge depends on the input only through its free coordinates, so it factors through the
`2^{#free}` free‑coordinate assignments — for *any* circuit, regardless of gate re‑use. -/
theorem restricted_rank_le_two_pow_free {m : ℕ} (chargeOf : (Fin n → Bool) → (W → ZMod 2))
    (ρ : Fin n → Option Bool) (cycle : Fin m → Finset W) (Inputs : Finset (Fin n → Bool)) :
    realizedClasses cycle (fun x => chargeOf (override x ρ)) Inputs
      ≤ 2 ^ (Finset.univ.filter (fun v => ρ v = none)).card := by
  classical
  have hfac : ∀ x, (fun x => chargeOf (override x ρ)) x
      = (fun fs => chargeOf (extendFree ρ fs)) (freeRestrict ρ x) := by
    intro x
    show chargeOf (override x ρ) = chargeOf (extendFree ρ (freeRestrict ρ x))
    rw [override_eq_extend]
  refine le_trans (realized_le_of_factorThroughStat cycle (fun x => chargeOf (override x ρ)) Inputs
    (freeRestrict ρ) (fun fs => chargeOf (extendFree ρ fs)) hfac) ?_
  calc (Inputs.image (freeRestrict ρ)).card
      ≤ Fintype.card ({v : Fin n // ρ v = none} → Bool) := Finset.card_le_univ _
    _ = 2 ^ (Finset.univ.filter (fun v => ρ v = none)).card := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]

/-- **The named target — the missing mechanism beyond whole‑support fixing.**  A restriction drives a poly‑size
ACC⁰ circuit's realized rank strictly below the surviving Tseitin rank *without* fixing any gate's whole support
(a circuit‑specific drop under unbounded reuse).  `NP ⊄ ACC⁰`‑strength; this is the Håstad‑shrinkage /
correlation content the route now requires. -/
def RandomRestrictionLowersEffectiveRankDespiteReuse
    (acc0Classes : ℕ → ℕ) (survivingTseitinClasses : ℕ → ℕ) : Prop :=
  ∀ n, acc0Classes n < survivingTseitinClasses n

end PallLean.Paper93.DeepMath.PathB.ACCReuseSwitchingTarget

#print axioms PallLean.Paper93.DeepMath.PathB.ACCReuseSwitchingTarget.override_eq_extend
#print axioms PallLean.Paper93.DeepMath.PathB.ACCReuseSwitchingTarget.restricted_rank_le_two_pow_free
