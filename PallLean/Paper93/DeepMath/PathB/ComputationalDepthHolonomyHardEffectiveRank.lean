import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyEffectiveRank
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypergraphHolonomySPDP

/-!
# The hard side in the effective‑rank framework — the matching lower bound

`…HolonomyEffectiveRank` proved the tame upper bound: a `k`‑gate modular layer realizes `≤ q^k` holonomy classes
(effective cycle rank `≤ k·log₂ q`).  This file proves the **matching lower bound**: the charged expander gadget
(`DisjointCycles`) realizes the *full* `2^m` classes — effective cycle rank exactly `m`.  Together they make the
tame/hard split one coherent statement in the realized‑charge language.

The charges are `chargeForZ G S = ` indicator of the representatives in `S`; charging cycle `i`'s representative
flips precisely cycle `i`'s holonomy, so the signature of `chargeForZ G S` is the indicator of `S`, and over all
`S ⊆ Fin m` these realize all `2^m` distinct signatures.

## What is proved (clean axioms, no `sorry`)

* `holZ_chargeForZ` — over `F₂`, charging the reps in `S` gives cycle `i` holonomy `[i ∈ S]`.
* `holSigZ_chargeForZ` — hence the holonomy signature of `chargeForZ G S` is the indicator of `S`.
* `expander_realizedClasses_eq` — **`realizedClasses = 2^m`**: the expander gadget's realized charges achieve the
  full effective cycle rank `m`.

## Verdict — the effective‑rank dichotomy is now two‑sided and proved

* **tame** (`modular_layer_realized_le`): `k` modular statistics ⇒ `≤ q^k` classes, effective rank `≤ k·log₂ q`;
* **hard** (`expander_realizedClasses_eq`): `m` charged disjoint cycles ⇒ `= 2^m` classes, effective rank `= m`.

Both ends are proved *in the same framework*, on the same object (`realizedClasses`).  The separation would follow
from showing a poly‑time decider of an NP‑hard family is forced onto the hard side — `ACC0LowRealizedGodelSPDP`:
that poly‑time computation cannot keep the realized charges' effective rank below `Ω(n)` on hard instances.  That
implication is the open, `NP ⊄ ACC⁰`‑strength step, still under the PRF‑free naturalness ceiling.  What is now
complete: the *invariant itself* cleanly separates tame from hard (low vs full effective rank); only the
"poly‑time ⇒ tame" bridge is missing, and it is named precisely.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolonomyHardEffectiveRank

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl
open PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank
open PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP

variable {V : Type*}

/-- The `F₂` charge that charges exactly the representatives of the cycles in `S`. -/
def chargeForZ [DecidableEq V] {m : ℕ} (G : DisjointCycles V m) (S : Finset (Fin m)) : V → ZMod 2 :=
  fun v => if v ∈ S.image G.rep then 1 else 0

/-- **Charging the reps in `S` gives cycle `i` holonomy `[i ∈ S]` (proved).** -/
theorem holZ_chargeForZ [DecidableEq V] {m : ℕ} (G : DisjointCycles V m) (S : Finset (Fin m)) (i : Fin m) :
    holZ (G.cycle i) (chargeForZ G S) = if i ∈ S then 1 else 0 := by
  unfold holZ chargeForZ
  rw [Finset.sum_boole]
  by_cases hiS : i ∈ S
  · have hset : (G.cycle i).filter (fun v => v ∈ S.image G.rep) = {G.rep i} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨hvc, j, hjS, hrep⟩
        have hmem : G.rep j ∈ G.cycle i := hrep ▸ hvc
        have hji : j = i := G.rep_only_own j i hmem
        rw [← hrep, hji]
      · rintro rfl
        exact ⟨G.rep_mem i, i, hiS, rfl⟩
    rw [hset]; simp [hiS]
  · have hset : (G.cycle i).filter (fun v => v ∈ S.image G.rep) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hvc
      rw [Finset.mem_image]
      rintro ⟨j, hjS, hrep⟩
      have hmem : G.rep j ∈ G.cycle i := hrep ▸ hvc
      have hji : j = i := G.rep_only_own j i hmem
      exact hiS (hji ▸ hjS)
    rw [hset]; simp [hiS]

/-- **The holonomy signature of `chargeForZ G S` is the indicator of `S` (proved).** -/
theorem holSigZ_chargeForZ [DecidableEq V] {m : ℕ} (G : DisjointCycles V m) (S : Finset (Fin m)) :
    holSigZ G.cycle (chargeForZ G S) = fun i => if i ∈ S then 1 else 0 := by
  funext i
  exact holZ_chargeForZ G S i

/-- The indicator map `S ↦ (i ↦ [i ∈ S])` is injective. -/
theorem indicatorZ_injective {m : ℕ} :
    Function.Injective (fun (S : Finset (Fin m)) => fun i => if i ∈ S then (1 : ZMod 2) else 0) := by
  intro S T h
  ext i
  have hi := congrFun h i
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp_all

/-- **The hard side (proved): the expander gadget realizes the full `2^m` holonomy classes — effective cycle rank
`= m`.**  Over all subsets `S ⊆ Fin m`, the charges `chargeForZ G S` realize all `2^m` distinct indicator
signatures. -/
theorem expander_realizedClasses_eq [DecidableEq V] {m : ℕ} (G : DisjointCycles V m) :
    realizedClasses G.cycle (fun S : Finset (Fin m) => chargeForZ G S) Finset.univ = 2 ^ m := by
  unfold realizedClasses
  have hcong : Finset.univ.image (fun S : Finset (Fin m) => holSigZ G.cycle (chargeForZ G S))
      = Finset.univ.image (fun S : Finset (Fin m) => fun i => if i ∈ S then (1 : ZMod 2) else 0) := by
    apply Finset.image_congr
    intro S _
    exact holSigZ_chargeForZ G S
  rw [hcong, Finset.card_image_of_injective _ indicatorZ_injective, Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.HolonomyHardEffectiveRank

#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyHardEffectiveRank.holZ_chargeForZ
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyHardEffectiveRank.holSigZ_chargeForZ
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyHardEffectiveRank.expander_realizedClasses_eq
