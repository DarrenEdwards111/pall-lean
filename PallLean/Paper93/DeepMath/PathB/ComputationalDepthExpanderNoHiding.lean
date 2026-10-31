import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchCostLowerBound

/-!
# Expander no-hiding: residual subfunction explosion forces continuation debt (proved)

This is the missing bridge between the structured forcing families and full SAT debt, in its honest
restricted form.  The conceptual target (the "God-Move" / no-hiding lemma):

> small boundary + expander constraints ⇒ large unresolved continuation debt.

The mechanism is **residual subfunction explosion**: a decomposition that reads few variables leaves many
constraints *crossing* the cut; their values on the continuation form a **residual outcome vector**, and if
`r` crossing constraints are independent (realise all `2^r` outcomes) then there are `2^r` pairwise
**distinguishable** continuations — a residual fooling set.  A low-boundary observer (`≤ 2^B` states) cannot
keep them apart, so it carries debt `≥ 2^r − 2^B`.

The genuine, fully proved content here is the explosion ⇒ debt step.  Expansion's role (already proved for
`Kₙ` in the expander-Tseitin width kernel, `combination_support_card_ge_of_expansion`) is to supply
`r = Ω(n)` independent crossing constraints for variable-subset reads — that is, to discharge the surjectivity
hypothesis `hsurj` below for expander Tseitin.

## Proved (clean axioms, no `sorry`)

* `residualFooling` — the must-separate relation "different residual outcome vector".
* `surjective_residual_forces_debt` — **the no-hiding lemma**: if the residual map `residual : C → Fin (2^r)`
  is *surjective* (the `r` crossing constraints realise all `2^r` outcomes), then **every** boundary-`B`
  observer carries residual debt `2^r − 2^B ≤ debtCount (residualFooling residual) view`.
* `no_hiding_superlog` — if additionally `B ≤ r − 1` (the boundary is below the crossing count), the debt is
  `≥ 2^{r−1}` — super-logarithmic for `r = Ω(n)`.

## Honest scope — what closes and what stays open

This proves: **whenever a decomposition's residual explodes (surjects onto `2^{Ω(n)}` outcomes), a
low-boundary observer is forced into super-log debt** — and expansion supplies that explosion for the
variable-subset decompositions (the "dynamic Nečiporuk" reads).  It is **not** `P ≠ NP`: the surjectivity
`hsurj` is *for a fixed residual map*, i.e. a fixed decomposition.  Proving that the residual explodes for
**every** cheap adaptive decomposition of SAT — that no cheap decomposition can make the residual collapse —
is exactly the min-over-decompositions quantifier, and is the open core.  What this file does is reduce that
core to a single clean property: *residual non-collapse* (surjectivity of the residual onto a large outcome
set) under every cheap decomposition.  The debt then follows mechanically.  Expansion gives non-collapse for
structured reads; the adaptive min is open, named not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The **residual must-separate relation**: two continuations must be separated iff they have *different*
residual outcome vectors (a downstream check on the crossing-constraint values distinguishes them). -/
def residualFooling {k : ℕ} (residual : C → Fin k) : Finset (C × C) :=
  Finset.univ.filter (fun p => residual p.1 ≠ residual p.2)

/-- **Expander no-hiding lemma (proved).**  If the residual map `residual : C → Fin (2^r)` is surjective —
the `r` crossing constraints realise all `2^r` outcome vectors — then every boundary-`B` observer
(`view : C → Fin (2^B)`) carries residual debt at least `2^r − 2^B`.  Small boundary cannot hide an exploded
residual. -/
theorem surjective_residual_forces_debt {r : ℕ} (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual) {B : ℕ} (view : C → Fin (2 ^ B)) :
    2 ^ r - 2 ^ B ≤ debtCount (residualFooling residual) view := by
  classical
  -- a section picking one preimage per outcome
  set s : Fin (2 ^ r) → C := Function.surjInv hsurj with hs
  set P : Finset C := Finset.univ.image s with hP
  have hsinj : Function.Injective s := Function.injective_surjInv hsurj
  have hres : ∀ o : Fin (2 ^ r), residual (s o) = o := fun o => Function.surjInv_eq hsurj o
  have hPcard : P.card = 2 ^ r := by
    rw [hP, Finset.card_image_of_injective _ hsinj, Finset.card_univ, Fintype.card_fin]
  have hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ residualFooling residual := by
    intro x hx y hy hxy
    rw [residualFooling, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨ox, _, hox⟩ := Finset.mem_image.mp hx
    obtain ⟨oy, _, hoy⟩ := Finset.mem_image.mp hy
    intro hr
    -- residual x = ox, residual y = oy; if equal then ox = oy then x = y
    have hrx : residual x = ox := by rw [← hox]; exact hres ox
    have hry : residual y = oy := by rw [← hoy]; exact hres oy
    have hoo : ox = oy := by rw [← hrx, ← hry]; exact hr
    exact hxy (by rw [← hox, ← hoy]; exact congrArg s hoo)
  have h := foolingSet_forces_debt P view (residualFooling residual) hfool
  rwa [hPcard] at h

/-- **Super-logarithmic residual debt (proved).**  If the boundary is below the crossing-constraint count
(`B ≤ r − 1`), an exploded (surjective) residual forces debt `≥ 2^{r−1}` — super-logarithmic for
`r = Ω(n)`, `B = O(log n)`. -/
theorem no_hiding_superlog {r : ℕ} (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual) {B : ℕ} (view : C → Fin (2 ^ B))
    (hB : B ≤ r - 1) (hr : 1 ≤ r) :
    2 ^ (r - 1) ≤ debtCount (residualFooling residual) view := by
  have h := surjective_residual_forces_debt residual hsurj view
  have hBr : 2 ^ B ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) hB
  have hsplit : 2 ^ r = 2 ^ (r - 1) + 2 ^ (r - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring
  omega

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.surjective_residual_forces_debt
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.no_hiding_superlog
