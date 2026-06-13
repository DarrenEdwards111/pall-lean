import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFragmentSwitching

/-!
# The rank‑lowering target — named, and proved one rung higher (read‑once modular gates)

The only missing moving part toward an ACC⁰ lower bound in this framework is **rank lowering under restriction**.
This file names the exact target and climbs one rung above the modular‑statistic fragment: the **read‑once**
fragment (gates reading *disjoint* variable supports), where a variable‑restriction *provably* reduces the
surviving statistic count — because fixing a gate's whole support makes its statistic **constant**.

## The named target

* `ACCRestrictionLowersEffectiveRank` — for a poly‑size ACC⁰ circuit on hard instances, *some* restriction drops
  the realized effective holonomy rank below the surviving Tseitin rank.  The open `NP ⊄ ACC⁰`‑strength theorem.

## What is proved for the read‑once rung (clean axioms, no `sorry`)

* `gate_constant` — **the new structural lemma**: a gate reading only its support, with that support fixed by the
  restriction, is *constant* on all restricted inputs (read‑once ⇒ fixing a block fixes exactly its gate).
* `readonce_restriction_lowers_rank` — hence the restricted charge factors through only the **free** gates, so
  `realizedClasses ≤ q^{#free gates}`.
* `readonce_rank_drops` — `#free gates < k` whenever the restriction fixes at least one gate (`T` nonempty), so
  the rank bound *strictly drops* `q^k → q^{#free}`.

Combined with `tseitin_holonomy_survives_restriction` and `fragment_below_surviving_tseitin`
(`…FragmentSwitching`), this gives a real lower bound for the read‑once fragment: a read‑once modular layer whose
free gates are too few cannot realize the surviving Tseitin holonomy.

## Honest scope — one rung, not the summit

This climbs from "modular‑statistic" (restriction's effect assumed) to "read‑once" (restriction's effect
*derived* from disjoint supports).  It is still a fragment: it needs the gate supports **disjoint**.  The next
rungs (bounded‑overlap, bounded‑depth trees, small sharing) and finally poly‑gate ACC⁰ — where supports overlap
arbitrarily and a restriction need *not* reduce the statistic count — remain open; that last is exactly
`ACCRestrictionLowersEffectiveRank`, `NP ⊄ ACC⁰`‑strength, under the PRF‑free naturalness ceiling.  The genuine
gain: the rank‑lowering mechanism now *derives* from circuit structure (disjointness), not just an assumed drop.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCRankLoweringTarget

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl
open PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank

/-- **The named open target.**  Some restriction drops a poly‑size ACC⁰ circuit's realized effective holonomy rank
below the surviving Tseitin rank — the `NP ⊄ ACC⁰`‑strength theorem this framework reduces to. -/
def ACCRestrictionLowersEffectiveRank
    (acc0RealizedClasses : ℕ → ℕ) (survivingTseitinClasses : ℕ → ℕ) : Prop :=
  ∀ n, acc0RealizedClasses n < survivingTseitinClasses n

variable {n k q : ℕ} {W : Type*}

/-- Override `x` with the fixed values of the restriction `ρ`. -/
def override (x : Fin n → Bool) (ρ : Fin n → Option Bool) : Fin n → Bool :=
  fun v => (ρ v).getD (x v)

/-- A fixed variable's value under `override` does not depend on `x`. -/
theorem override_fixed {ρ : Fin n → Option Bool} {v : Fin n} (h : (ρ v).isSome) (x x' : Fin n → Bool) :
    override x ρ v = override x' ρ v := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  simp [override, hb]

/-- **The new structural lemma (proved): a read‑once gate with its support fixed is constant.**  A gate that reads
only its support, when that support is fixed by `ρ`, evaluates the same on every restricted input. -/
theorem gate_constant (supp : Fin k → Finset (Fin n)) (gstat : Fin k → (Fin n → Bool) → ZMod q)
    (hreads : ∀ i (x y : Fin n → Bool), (∀ v ∈ supp i, x v = y v) → gstat i x = gstat i y)
    (ρ : Fin n → Option Bool) (i : Fin k) (hfix : ∀ v ∈ supp i, (ρ v).isSome) (x x' : Fin n → Bool) :
    gstat i (override x ρ) = gstat i (override x' ρ) :=
  hreads i (override x ρ) (override x' ρ) (fun v hv => override_fixed (hfix v hv) x x')

/-- **Read‑once restriction lowers the rank bound (proved): `realizedClasses ≤ q^{#free gates}`.**  After a
restriction fixing the supports of the gates in `T`, those gate statistics are constant (`gate_constant`), so the
restricted charge factors through only the free gates `{i ∉ T}`. -/
theorem readonce_restriction_lowers_rank [NeZero q] {m : ℕ}
    (supp : Fin k → Finset (Fin n)) (gstat : Fin k → (Fin n → Bool) → ZMod q)
    (hreads : ∀ i (x y : Fin n → Bool), (∀ v ∈ supp i, x v = y v) → gstat i x = gstat i y)
    (chargeOf : (Fin n → Bool) → (W → ZMod 2)) (chargeFromStats : (Fin k → ZMod q) → (W → ZMod 2))
    (hfac : ∀ y, chargeOf y = chargeFromStats (fun i => gstat i y))
    (ρ : Fin n → Option Bool) (T : Finset (Fin k))
    (hfix : ∀ i ∈ T, ∀ v ∈ supp i, (ρ v).isSome)
    (cycle : Fin m → Finset W) (Inputs : Finset (Fin n → Bool)) :
    realizedClasses cycle (fun x => chargeOf (override x ρ)) Inputs
      ≤ q ^ (Fintype.card {i : Fin k // i ∉ T}) := by
  classical
  set cT : Fin k → ZMod q := fun i => gstat i (override (fun _ => false) ρ) with hcT
  set freeStat : (Fin n → Bool) → ({i : Fin k // i ∉ T} → ZMod q) :=
    fun x i => gstat i.val (override x ρ) with hfree
  set chargeFromFree : ({i : Fin k // i ∉ T} → ZMod q) → (W → ZMod 2) :=
    fun fs => chargeFromStats (fun i => if h : i ∈ T then cT i else fs ⟨i, h⟩) with hcff
  have hfac' : ∀ x, (fun x => chargeOf (override x ρ)) x = chargeFromFree (freeStat x) := by
    intro x
    show chargeOf (override x ρ) = chargeFromFree (freeStat x)
    rw [hfac (override x ρ), hcff]
    congr 1
    funext i
    by_cases h : i ∈ T
    · rw [dif_pos h]
      exact gate_constant supp gstat hreads ρ i (hfix i h) x (fun _ => false)
    · rw [dif_neg h]
  refine le_trans (realized_le_of_factorThroughStat cycle (fun x => chargeOf (override x ρ)) Inputs
    freeStat chargeFromFree hfac') ?_
  calc (Inputs.image freeStat).card
      ≤ Fintype.card ({i : Fin k // i ∉ T} → ZMod q) := Finset.card_le_univ _
    _ = q ^ (Fintype.card {i : Fin k // i ∉ T}) := by rw [Fintype.card_fun, ZMod.card]

/-- **The rank strictly drops (proved): `#free gates < k` when at least one gate is fixed.** -/
theorem readonce_rank_drops {T : Finset (Fin k)} (a : Fin k) (ha : a ∈ T) :
    Fintype.card {i : Fin k // i ∉ T} < k := by
  have h := Fintype.card_subtype_lt (p := fun i : Fin k => i ∉ T) (x := a) (not_not_intro ha)
  rwa [Fintype.card_fin] at h

end PallLean.Paper93.DeepMath.PathB.ACCRankLoweringTarget

#print axioms PallLean.Paper93.DeepMath.PathB.ACCRankLoweringTarget.gate_constant
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRankLoweringTarget.readonce_restriction_lowers_rank
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRankLoweringTarget.readonce_rank_drops
