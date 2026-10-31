import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGoldreichMajorityCandidate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSequenceBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundedLocalityNonCollapse

/-!
# Restricted `InversionHardness`: proved, unconditionally, for concrete inverter classes

The global `InversionHardness` (no fast algorithm inverts the Majority‑Goldreich family) is `P ≠ NP`‑strength.
This file proves it as a **theorem** for several *restricted* inverter classes — extending the proved frontier
without claiming the separation.  Each result is unconditional and reuses already‑proved machinery; none needs
the cryptographic conjecture.

We model a *correct inverter* as a **separator** of the preimage classes: a decision view with zero
distinguishability debt against a surjective residual onto `Fin (2^r)` (it keeps all `2^r` classes apart).  A
restricted inverter class is hard exactly when no member is a separator.

## Proved (clean axioms, no `sorry`)

* `no_low_degree_algebraic_inverter` — **the low‑degree algebraic class is empty (NEW, from optimal AI).**  For
  `n = 2t-1`, the Majority predicate admits no nonzero ANF degree‑`< t` annihilator, so the
  linearization / low‑degree Gröbner attack provably fails.  This is `InversionHardness` restricted to
  degree‑`< t` algebraic inverters, unconditional, straight from `AI(Maj) = t`.
* `boundedCrossing_not_correct_inverter` — **the bounded‑crossing class fails.**  A width‑`w` crossing‑sequence
  observer over `q` states is not a separator once `q^w < 2^r` (positive debt), via the crossing‑sequence bridge.
* `boundedLocality_not_correct_inverter` — **the bounded‑locality (junta) class fails.**  A view reading only
  `|W|` variables is not a separator once `2^{|W|} < 2^r`, via `bounded_support_forces_debt`.

## Honest scope

These discharge `InversionHardness` for: degree‑`< t` algebraic inverters (the algebraic attack), bounded
crossing‑sequence inverters (one‑tape/oblivious), and bounded‑locality/junta inverters.  They do **not** cover
all of `P`: the algebraic case is *exact* low‑degree (an `AC⁰[p]` / *approximate* low‑degree inverter needs the
Razborov–Smolensky approximation argument, not the exact‑annihilator bound used here — noted, not done); the
crossing and locality cases are the classical restricted models.  So the proved frontier now includes
unconditional restricted `InversionHardness`; the global statement remains the `P ≠ NP`‑hard wall.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictedInversionHardness

open Finset
open PallLean.Paper93.DeepMath.PathB.MajorityAI
open PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate
open PallLean.Paper93.DeepMath.PathB.CrossingSequenceBridge
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

/-! ### The low‑degree algebraic inverter class (new — from the optimal Majority AI) -/

/-- A **degree‑`< t` algebraic inverter certificate** for the Majority predicate: a nonzero ANF degree‑`< t`
function annihilating `Maj t` — the low‑degree relation a linearization / Gröbner attack exploits. -/
def LowDegreeAlgebraicCertificate {n : ℕ} (t : ℕ) (cert : Finset (Fin n) → ZMod 2) : Prop :=
  cert ≠ 0 ∧ DegreeLt cert t ∧ (∀ T, cert T * Maj t T = 0)

/-- **No low‑degree algebraic inverter (proved — restricted `InversionHardness`).**  For `n = 2t-1`, the
Majority‑Goldreich predicate admits **no** degree‑`< t` algebraic inverter certificate: the only degree‑`< t`
function annihilating `Maj` is `0`.  The linearization / low‑degree algebraic attack provably fails —
unconditional, from the optimal algebraic immunity `AI(Maj) = t`. -/
theorem no_low_degree_algebraic_inverter {n t : ℕ} (ht : 1 ≤ t) (hn : n = 2 * t - 1) :
    ¬ ∃ cert : Finset (Fin n) → ZMod 2, LowDegreeAlgebraicCertificate t cert := by
  rintro ⟨cert, hne, hdeg, hann⟩
  obtain ⟨T, hT⟩ := (majority_defeats_low_degree_separator ht hn cert hne hdeg).1
  exact hT (hann T)

/-! ### Inverter = separator; the bounded‑resource classes fail -/

/-- A **correct inverter** keeps all `2^r` preimage classes apart: its decision view has zero
distinguishability debt against the (surjective) residual. -/
def CorrectInverter {C S : Type*} [Fintype C] [DecidableEq C] [DecidableEq S] {r : ℕ}
    (residual : C → Fin (2 ^ r)) (view : C → S) : Prop :=
  debtCount (residualFooling residual) view = 0

/-- **No bounded‑crossing inverter (proved — restricted `InversionHardness`).**  A width‑`w` crossing‑sequence
observer over `q` states is **not** a correct inverter once `q^w < 2^r`: it cannot keep the `2^r` preimage
classes apart (positive debt).  Unconditional, from the crossing‑sequence bridge. -/
theorem boundedCrossing_not_correct_inverter {C : Type*} [Fintype C] [DecidableEq C] {r w q : ℕ}
    (hlt : q ^ w < 2 ^ r) (residual : C → Fin (2 ^ r)) (hsurj : Function.Surjective residual)
    (view : C → (Fin w → Fin q)) :
    ¬ CorrectInverter residual view :=
  fun h => crossingSequence_no_separator hlt residual hsurj view h

/-- **No bounded‑locality (junta) inverter (proved — restricted `InversionHardness`).**  A decision view that
reads only the variables in `W` is **not** a correct inverter once `2^{|W|} < 2^r`: it carries debt
`≥ 2^r − 2^{|W|} > 0`.  Unconditional, from `bounded_support_forces_debt`. -/
theorem boundedLocality_not_correct_inverter {Edge : Type*} [Fintype Edge] [DecidableEq Edge] {r : ℕ}
    (residual : (Edge → ZMod 2) → Fin (2 ^ r)) (hsurj : Function.Surjective residual)
    {S : Type*} [DecidableEq S] (view : (Edge → ZMod 2) → S) (W : Finset Edge)
    (hdep : ∀ x y : Edge → ZMod 2, (∀ e ∈ W, x e = y e) → view x = view y)
    (hWr : 2 ^ W.card < 2 ^ r) :
    ¬ CorrectInverter residual view := by
  intro h
  have hdebt := bounded_support_forces_debt residual hsurj view W hdep
  unfold CorrectInverter at h
  rw [h] at hdebt
  omega

end PallLean.Paper93.DeepMath.PathB.RestrictedInversionHardness

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedInversionHardness.no_low_degree_algebraic_inverter
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedInversionHardness.boundedCrossing_not_correct_inverter
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedInversionHardness.boundedLocality_not_correct_inverter
