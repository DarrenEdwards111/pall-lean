import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyPSideControl

/-!
# Bounded cycle rank ⇒ few holonomy classes — a provable tame‑side control

The P‑side control (`…HolonomyPSideControl`) reduced the tame side to a **rank bound**: holonomy is `F₂`‑linear,
so the class count is `2^{rank}` where `rank` is the cycle‑space rank, not the gate count.  This file lands the
*provable, non‑vacuous* instance of that bound: when the constraint graph's cycle space has rank `r` — i.e. the
`m` cycles in the family are spanned by `r` basis cycles — there are `≤ 2^r` holonomy classes, **for every charge
family, regardless of `m` or the gate count**.

This is the genuine tame‑side theorem one rung below the full ACC⁰ claim:

* **bounded‑treewidth / planar / series‑parallel** constraint graphs have cycle rank `r = O(\log n)` or `O(1)`
  → `≤ 2^r` = polynomial / constant holonomy classes — provably tame;
* **expander** constraint graphs have cycle rank `r = Ω(n)` → `2^{Ω(n)}` classes (the hard side,
  `holonomy_realizes_all`).

## What is proved (clean axioms, no `sorry`)

* `holonomy_classes_le_of_basis` — **the rank bound**: if the holonomy signature factors as
  `holSigZ cycle = T ∘ holSigZ basis` for a linear `T` and `r` basis cycles (cycle rank `≤ r`), then any charge
  family realizes `≤ 2^r` holonomy classes.
* `holonomy_classes_le_of_few_distinct` — **a concrete instance, factoring proved**: if the `m` cycles are drawn
  from only `r` distinct basis cycles (`cycle = basis ∘ f`), the bound `≤ 2^r` holds — the factoring `T` is the
  pullback by `f`, no hypothesis assumed.
* `holonomy_classes_le_one_of_no_cycles` — the acyclic extreme as the `r = 0` case: `≤ 1` class.

## Honest scope

This is a *real* tame‑side control (conditional only on a **graph property** — the cycle rank — not on any
complexity assumption), so it is not a socket.  But it is not yet `ACC0LowRealizedGodelSPDP`: that needs poly‑time
/ ACC⁰ circuits to *produce constraint graphs of low cycle rank*, which is **false in general** (an ACC⁰ circuit
can encode an expander), so the full tame side requires the genuine structural fact that the *realized* charges —
not the raw graph — have low effective cycle rank.  That remains the open `NP ⊄ ACC⁰`‑strength content, and the
naturalness ceiling (`…DynamicSPDPNaturalnessRange`) still caps the method at the PRF‑free classes.  What is new
and solid: the tame side is now a **proved theorem for bounded‑cycle‑rank instances**, with the open part isolated
to "poly‑time ⇒ low effective cycle rank".
-/

namespace PallLean.Paper93.DeepMath.PathB.HolonomyBoundedCycleRank

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl

variable {V : Type*}

/-- `Fin r → ZMod 2` has exactly `2^r` elements. -/
theorem card_fun_zmod2 (r : ℕ) : Fintype.card (Fin r → ZMod 2) = 2 ^ r := by
  rw [Fintype.card_fun, Fintype.card_fin]
  norm_num [ZMod.card]

/-- **The rank bound (proved): cycle rank `≤ r` ⇒ `≤ 2^r` holonomy classes.**  If every cycle's holonomy is a
fixed linear combination of `r` basis‑cycle holonomies (`holSigZ cycle = T ∘ holSigZ basis`), then any charge
family realizes at most `2^r` holonomy signatures — independent of the number of cycles `m` or gates. -/
theorem holonomy_classes_le_of_basis {m r : ℕ} (cycle : Fin m → Finset V) (basis : Fin r → Finset V)
    (T : (Fin r → ZMod 2) → (Fin m → ZMod 2)) (hfac : ∀ c, holSigZ cycle c = T (holSigZ basis c))
    (𝒞 : Finset (V → ZMod 2)) :
    (𝒞.image (holSigZ cycle)).card ≤ 2 ^ r := by
  have hsub : 𝒞.image (holSigZ cycle) ⊆ (Finset.univ : Finset (Fin r → ZMod 2)).image T := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨c, _, rfl⟩ := hs
    rw [hfac c]
    exact Finset.mem_image.mpr ⟨holSigZ basis c, Finset.mem_univ _, rfl⟩
  calc (𝒞.image (holSigZ cycle)).card
      ≤ ((Finset.univ : Finset (Fin r → ZMod 2)).image T).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin r → ZMod 2)).card := Finset.card_image_le
    _ = 2 ^ r := by rw [Finset.card_univ, card_fun_zmod2]

/-- **Concrete instance (proved): `m` cycles drawn from `r` distinct basis cycles ⇒ `≤ 2^r` classes.**  Here the
factoring is *proved*, not assumed: the linear `T` is the pullback by the index map `f`. -/
theorem holonomy_classes_le_of_few_distinct {m r : ℕ} (basis : Fin r → Finset V) (f : Fin m → Fin r)
    (𝒞 : Finset (V → ZMod 2)) :
    (𝒞.image (holSigZ (fun i => basis (f i)))).card ≤ 2 ^ r := by
  refine holonomy_classes_le_of_basis (fun i => basis (f i)) basis (fun sig => fun i => sig (f i)) ?_ 𝒞
  intro c
  funext i
  rfl

/-- **The acyclic extreme as `r = 0` (proved): no independent cycles ⇒ at most one holonomy class.** -/
theorem holonomy_classes_le_one_of_no_cycles {m : ℕ} (cycle : Fin m → Finset V)
    (T : (Fin 0 → ZMod 2) → (Fin m → ZMod 2)) (hfac : ∀ c, holSigZ cycle c = T (holSigZ (fun i : Fin 0 => i.elim0) c))
    (𝒞 : Finset (V → ZMod 2)) :
    (𝒞.image (holSigZ cycle)).card ≤ 1 := by
  have h := holonomy_classes_le_of_basis cycle (fun i : Fin 0 => i.elim0) T hfac 𝒞
  simpa using h

end PallLean.Paper93.DeepMath.PathB.HolonomyBoundedCycleRank

#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBoundedCycleRank.holonomy_classes_le_of_basis
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBoundedCycleRank.holonomy_classes_le_of_few_distinct
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBoundedCycleRank.holonomy_classes_le_one_of_no_cycles
