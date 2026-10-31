import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypergraphHolonomySPDP

/-!
# P‑side holonomy control — linearity, acyclic triviality, and the generator bound

The hard side (`…HypergraphHolonomySPDP`) showed charged expander cycles realize `2^m` holonomy classes.  The
P‑side question — the `ACC0LowRealizedGodelSPDP` analogue — is whether *structured* (poly‑time / circuit) charges
realize only *few* holonomy classes.  This file establishes the genuine structural asset of holonomy and proves
the two extremes, locating exactly where the open content lives.

We work over `F₂ = ZMod 2`, where holonomy is the cycle sum `holZ C c = ∑_{v ∈ C} c(v)`.

## What is proved (clean axioms, no `sorry`)

* **Holonomy is `F₂`‑linear in the charge** — `holSigZ_zero` (`holSigZ 0 = 0`) and `holSigZ_add`
  (`holSigZ (c₁ + c₂) = holSigZ c₁ + holSigZ c₂`).  This is the asset plain SPDP lacked: the holonomy signature is
  a *linear map* of the charge, so the realized signatures form a **subspace**, and the number of holonomy classes
  is `2^{rank}` — controlled by the **cycle rank**, not by the raw gate count.
* **Acyclic ⇒ trivial (proved)** — `holonomy_acyclic_trivial`: with `m = 0` cycles (a tree/forest constraint
  graph) every charge has the *same* (empty) holonomy signature — **one** class.  The tame extreme.
* **Generator bound (proved)** — `holonomy_classes_le_of_generators`: charges that are `F₂`‑combinations of `k`
  generators realize `≤ 2^k` holonomy classes.

## Where the open content lives — honest

By linearity the class count is `2^{rank}` with `rank ≤ min(k, m)` — the rank of the gate‑charge images in cycle
space.  The two extremes are proved: acyclic ⇒ `rank = 0` ⇒ 1 class; full expander ⇒ `rank = m` ⇒ `2^m`
(`holonomy_realizes_all`).  So the P‑side control theorem reduces to a **rank bound**: *poly‑time circuits produce
gate charges of low cycle‑rank*.  That is exactly `ACC0LowRealizedGodelSPDP` in holonomy form, and it is the open,
`NP ⊄ ACC⁰`‑strength content — the generator bound alone gives `2^k` (vacuous for `k = poly` gates), so control
must come from *linear dependence* of the gate charges in cycle space, not from counting.  Holonomy's advantage
over the additive‑statistic budget is precisely this: `2^{rank}` can be far below `2^{gates}` when the gate charges
are cycle‑dependent — but proving they are, for poly‑time circuits, is the lower bound itself.  And the naturalness
caveat (`…DynamicSPDPNaturalnessRange`) still caps the method at the PRF‑free classes.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl

open PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP

variable {V : Type*}

/-- **Cycle holonomy over `F₂`:** the sum of charges around `C`. -/
def holZ (C : Finset V) (c : V → ZMod 2) : ZMod 2 := ∑ v ∈ C, c v

/-- The `F₂` holonomy signature over `m` cycles. -/
def holSigZ {m : ℕ} (cycle : Fin m → Finset V) (c : V → ZMod 2) : Fin m → ZMod 2 :=
  fun i => holZ (cycle i) c

/-- `holZ` is additive in the charge. -/
theorem holZ_add (C : Finset V) (c₁ c₂ : V → ZMod 2) :
    holZ C (c₁ + c₂) = holZ C c₁ + holZ C c₂ := by
  unfold holZ
  rw [← Finset.sum_add_distrib]
  rfl

/-- `holZ` sends the zero charge to `0`. -/
theorem holZ_zero (C : Finset V) : holZ C (0 : V → ZMod 2) = 0 := by
  unfold holZ
  simp

/-- **Holonomy is `F₂`‑linear in the charge — additivity (proved).**  Hence the realized holonomy signatures form
a subspace and the class count is `2^{rank}`. -/
theorem holSigZ_add {m : ℕ} (cycle : Fin m → Finset V) (c₁ c₂ : V → ZMod 2) :
    holSigZ cycle (c₁ + c₂) = holSigZ cycle c₁ + holSigZ cycle c₂ := by
  funext i
  exact holZ_add (cycle i) c₁ c₂

/-- **Holonomy is `F₂`‑linear in the charge — zero (proved).** -/
theorem holSigZ_zero {m : ℕ} (cycle : Fin m → Finset V) :
    holSigZ cycle (0 : V → ZMod 2) = 0 := by
  funext i
  exact holZ_zero (cycle i)

/-- **Acyclic ⇒ trivial holonomy (proved): with no cycles, every charge has the same signature — one class.** -/
theorem holonomy_acyclic_trivial (cycle : Fin 0 → Finset V) (𝒞 : Finset (V → ZMod 2)) :
    (𝒞.image (holSigZ cycle)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x _ y _
  funext i
  exact i.elim0

/-- **Generator bound (proved): `k` charge generators give `≤ 2^k` holonomy classes.**  The `F₂`‑combinations of
`k` generators (subset sums) number `2^k`, so their holonomy signatures do too.  *Vacuous for `k = poly` gates* —
the real control must come from linear dependence of the generators in cycle space (low rank), not their count. -/
theorem holonomy_classes_le_of_generators {m k : ℕ} (cycle : Fin m → Finset V)
    (g : Fin k → (V → ZMod 2)) :
    (Finset.univ.image (fun S : Finset (Fin k) => holSigZ cycle (∑ i ∈ S, g i))).card ≤ 2 ^ k := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl

#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl.holSigZ_add
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl.holSigZ_zero
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl.holonomy_acyclic_trivial
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl.holonomy_classes_le_of_generators
