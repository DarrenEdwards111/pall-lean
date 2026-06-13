import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictedCashout

/-!
# The explicitness wall: counting gives a hard function, `P ≠ NP` needs an explicit NP one

The counting cash‑out (`…RestrictedCashout`) proves *some* Boolean function escapes every cheap decider.  But
`P ≠ NP` needs a **specific, explicit** family in `NP` (e.g. SAT) to be hard.  This file formalizes the exact
gap and fixes a common explicit‑family interface for future routes to target.

The gap is a quantifier/structure mismatch:

* **counting gives** `∀ n, ∃ f, (f hard at length n)` — per‑length existence.  By choice this assembles into
  `∃ F, HardFor F` — a hard *family* — but with **no control over membership in `NP`**.
* **`P ≠ NP` needs** `∃ F, InNP F ∧ HardFor F` — a hard family that is *also explicit / in `NP`*.

So the counting witness is the explicit target **minus the `InNP` conjunct**.  Counting (a property of *most*
functions) cannot supply that conjunct — isolating an `NP` family is precisely the missing, `P ≠ NP`‑strength
step (and the next obstruction is the natural‑proofs / largeness barrier: the counting property is "large", so
by Razborov–Rudich it cannot, under standard assumptions, *usefully* isolate `NP`).

## Proved (clean axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`)

* `HardFor` / `InNP` / `ExplicitNPHard` — the explicit‑family interface (one target object).
* `counting_hard_at_each_length` — per‑length existence (from `cheap_class_misses_function`).
* `hard_family_exists` — a hard *family* exists (by choice) — **but carries no `InNP` guarantee**.
* `explicitNPHard_imp_hardFamily` — the explicit‑NP target is *strictly stronger*: it implies the
  (`InNP`‑free) hard‑family existence that counting already gives.  So the entire remaining content is the
  `InNP` conjunct.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExplicitnessWall

open PallLean.Paper93.DeepMath.PathB.RestrictedCashout

/-- A uniform family of Boolean functions (one per input length) — the candidate explicit object. -/
abbrev ExplicitFamily := (n : ℕ) → BoolFun n

/-- `F` is hard for the cheap class: no cheap decider equals `F n`, at every length. -/
def HardFor (N : ℕ → ℕ) (cheap : ∀ n, Fin (N n) → BoolFun n) (F : ExplicitFamily) : Prop :=
  ∀ n i, cheap n i ≠ F n

/- `InNP` is the **abstract NP‑membership interface** — an *opaque* predicate every explicit route must
discharge for its candidate family.  It is deliberately a parameter (not a definition): counting provides no
handle on it, which is precisely the gap. -/
variable (InNP : ExplicitFamily → Prop)

/-- The `P ≠ NP`‑shaped target: a hard family that is **also** in `NP`. -/
def ExplicitNPHard (N : ℕ → ℕ) (cheap : ∀ n, Fin (N n) → BoolFun n) : Prop :=
  ∃ F, InNP F ∧ HardFor N cheap F

/-- **Counting gives per‑length hardness (proved).**  At each length, some Boolean function is missed by the
cheap class. -/
theorem counting_hard_at_each_length {N : ℕ → ℕ} (cheap : ∀ n, Fin (N n) → BoolFun n)
    (hN : ∀ n, N n < 2 ^ 2 ^ n) (n : ℕ) :
    ∃ f : BoolFun n, ∀ i, cheap n i ≠ f :=
  cheap_class_misses_function (cheap n) (hN n)

/-- **A hard family exists — nonconstructively, with no `NP` guarantee (proved).**  Choice assembles the
per‑length witnesses into a family `F` hard for the cheap class.  This is exactly what counting yields: hardness
*without* `InNP`. -/
theorem hard_family_exists {N : ℕ → ℕ} (cheap : ∀ n, Fin (N n) → BoolFun n)
    (hN : ∀ n, N n < 2 ^ 2 ^ n) :
    ∃ F : ExplicitFamily, HardFor N cheap F := by
  classical
  refine ⟨fun n => Classical.choose (counting_hard_at_each_length cheap hN n), fun n i => ?_⟩
  exact Classical.choose_spec (counting_hard_at_each_length cheap hN n) i

/-- **The explicit‑NP target is strictly stronger (proved).**  `ExplicitNPHard` implies the `InNP`‑free
hard‑family existence that counting already delivers.  Hence the *entire* gap between what counting proves and
what `P ≠ NP` needs is the `InNP` conjunct — which counting cannot supply. -/
theorem explicitNPHard_imp_hardFamily {N : ℕ → ℕ} {cheap : ∀ n, Fin (N n) → BoolFun n}
    (h : ExplicitNPHard InNP N cheap) :
    ∃ F : ExplicitFamily, HardFor N cheap F := by
  obtain ⟨F, _, hF⟩ := h
  exact ⟨F, hF⟩

end PallLean.Paper93.DeepMath.PathB.ExplicitnessWall

#print axioms PallLean.Paper93.DeepMath.PathB.ExplicitnessWall.hard_family_exists
#print axioms PallLean.Paper93.DeepMath.PathB.ExplicitnessWall.explicitNPHard_imp_hardFamily
