import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRankLoweringTarget

/-!
# Bounded‑overlap rank lowering — the next rung above read‑once

The read‑once rank‑lowering (`…ACCRankLoweringTarget`) needed *disjoint* gate supports.  This file climbs to
**bounded overlap**: each variable feeds at most `d` gates (bounded incidence).  Two observations close the rung:

* the gate‑constant argument needs **no** disjointness — fixing a gate's whole support makes it constant whatever
  the overlap (already general in `readonce_restriction_lowers_rank`);
* what bounded overlap buys is a **count**: a restriction leaving `u` free variables leaves at most `d · u` *free*
  gates, because each free gate contains a free variable and each free variable feeds `≤ d` gates.

So a restriction leaving `u` free variables drops the effective holonomy rank bound to `q^{d·u}` — polynomial when
`u = O(log n / d)`.

## What is proved (clean axioms, no `sorry`)

* `bounded_overlap_free_gates_le` — **the new counting lemma**: `#{free gates} ≤ d · #{free variables}` under
  incidence bound `d` (free gates inject into the free variables, `≤ d`‑to‑one).
* `bounded_overlap_restriction_lowers_rank` — hence `realizedClasses ≤ q^{d · (#free variables)}`: the
  bounded‑overlap modular layer's rank is controlled by the *free‑variable count*, not the gate count.

## Honest scope

A genuine rung up: rank lowering now holds for **arbitrary‑overlap** modular layers (the gate‑constant step is
overlap‑free) with the magnitude controlled by **bounded incidence** `d`.  It is still a fragment — it assumes the
charge factors through per‑gate modular statistics with bounded incidence.  The remaining rungs (bounded‑depth
trees with re‑use, then poly‑gate ACC⁰ where a restriction need not fix any gate's *whole* support, so no gate
need become constant) stay open — the last is exactly `ACCRestrictionLowersEffectiveRank`, `NP ⊄ ACC⁰`‑strength,
under the PRF‑free naturalness ceiling.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundedOverlapRankLowering

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl
open PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank
open PallLean.Paper93.DeepMath.PathB.ACCRankLoweringTarget

variable {n k q : ℕ} {W : Type*}

/-- **The new counting lemma (proved): `#{free gates} ≤ d · #{free variables}`.**  Each free gate (whose support
contains a free variable) maps to such a variable, and each free variable feeds `≤ d` gates (incidence bound). -/
theorem bounded_overlap_free_gates_le (supp : Fin k → Finset (Fin n)) (ρ : Fin n → Option Bool) (d : ℕ)
    (hinc : ∀ v, (Finset.univ.filter (fun i => v ∈ supp i)).card ≤ d) :
    (Finset.univ.filter (fun i => ¬ ∀ v ∈ supp i, (ρ v).isSome)).card
      ≤ d * (Finset.univ.filter (fun v => ¬ (ρ v).isSome)).card := by
  classical
  have hsub : (Finset.univ.filter (fun i => ¬ ∀ v ∈ supp i, (ρ v).isSome))
      ⊆ (Finset.univ.filter (fun v => ¬ (ρ v).isSome)).biUnion
          (fun v => Finset.univ.filter (fun i => v ∈ supp i)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨v, hv, hvfree⟩ : ∃ v ∈ supp i, ¬ (ρ v).isSome := by
      by_contra hc
      push_neg at hc
      exact hi.2 hc
    rw [Finset.mem_biUnion]
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvfree⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hv⟩⟩
  calc (Finset.univ.filter (fun i => ¬ ∀ v ∈ supp i, (ρ v).isSome)).card
      ≤ ((Finset.univ.filter (fun v => ¬ (ρ v).isSome)).biUnion
          (fun v => Finset.univ.filter (fun i => v ∈ supp i))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => ¬ (ρ v).isSome),
          (Finset.univ.filter (fun i => v ∈ supp i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ Finset.univ.filter (fun v => ¬ (ρ v).isSome), d :=
        Finset.sum_le_sum (fun v _ => hinc v)
    _ = (Finset.univ.filter (fun v => ¬ (ρ v).isSome)).card * d := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = d * (Finset.univ.filter (fun v => ¬ (ρ v).isSome)).card := Nat.mul_comm _ _

/-- **Bounded‑overlap restriction lowers the rank bound (proved): `realizedClasses ≤ q^{d · (#free vars)}`.**  The
restricted charge factors through the free gates (gates with all‑fixed support are constant), and bounded
incidence bounds the free‑gate count by `d · (#free variables)`. -/
theorem bounded_overlap_restriction_lowers_rank [NeZero q] {m : ℕ}
    (supp : Fin k → Finset (Fin n)) (gstat : Fin k → (Fin n → Bool) → ZMod q)
    (hreads : ∀ i (x y : Fin n → Bool), (∀ v ∈ supp i, x v = y v) → gstat i x = gstat i y)
    (chargeOf : (Fin n → Bool) → (W → ZMod 2)) (chargeFromStats : (Fin k → ZMod q) → (W → ZMod 2))
    (hfac : ∀ y, chargeOf y = chargeFromStats (fun i => gstat i y))
    (ρ : Fin n → Option Bool) (d : ℕ)
    (hinc : ∀ v, (Finset.univ.filter (fun i => v ∈ supp i)).card ≤ d)
    (cycle : Fin m → Finset W) (Inputs : Finset (Fin n → Bool)) :
    realizedClasses cycle (fun x => chargeOf (override x ρ)) Inputs
      ≤ q ^ (d * (Finset.univ.filter (fun v => ¬ (ρ v).isSome)).card) := by
  classical
  have hrank := readonce_restriction_lowers_rank supp gstat hreads chargeOf chargeFromStats hfac ρ
    (Finset.univ.filter (fun i => ∀ v ∈ supp i, (ρ v).isSome))
    (fun i hi => (Finset.mem_filter.mp hi).2) cycle Inputs
  refine le_trans hrank (Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) ?_)
  rw [Fintype.card_subtype]
  refine le_trans (Finset.card_le_card ?_) (bounded_overlap_free_gates_le supp ρ d hinc)
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_univ i, ?_⟩
  intro hall
  exact hi.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hall⟩)

end PallLean.Paper93.DeepMath.PathB.BoundedOverlapRankLowering

#print axioms PallLean.Paper93.DeepMath.PathB.BoundedOverlapRankLowering.bounded_overlap_free_gates_le
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedOverlapRankLowering.bounded_overlap_restriction_lowers_rank
