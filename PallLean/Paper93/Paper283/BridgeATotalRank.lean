/-
  PallLean/Paper93/Paper283/BridgeATotalRank.lean

  Paper §28.3 — Bridge A (rank form), real arithmetic composition over
  the **active set** `S`.

  ## Scope (Z8, paper-faithful)

  Y7 (`BridgeAComposition.lean`) packages the composed form of Bridge A
  into a conjunction bundling
    * the arithmetic identity `∑_{v ∈ S} κ = |S| · κ`, and
    * the per-vertex rank bound `κ ≤ (gadgetFamily v).rank` on the
      active set `S`.

  The present Z8 module isolates the two arithmetic ingredients of that
  composition and exposes them as self-contained kernel-only lemmas:

    1. `bridgeA_totalRank_composition` — the per-vertex rank bound
       `hPerVertex` composes pointwise into the total-rank inequality
       `∑_{v ∈ S} κ ≤ ∑_{v ∈ S} (gadgetFamily v).rank`, obtained by
       `Finset.sum_le_sum` applied to the per-vertex hypothesis;

    2. `bridgeA_totalRank_equals_card_kappa` — the elementary identity
       `∑_{v ∈ S} κ = |S| · κ`, obtained by summing the constant `κ`
       over the active set via `Finset.sum_const` and
       `Nat.smul_eq_mul`.

  Together these two lemmas supply the "real composition" step in the
  §28.3 Route C ⇒ Route A chain: summing the per-vertex Bridge A rank
  bound over the active set yields the total SPDP rank budget
  `|S| · κ`, which is exactly the quantity that the global Bridge B
  log-det bound is compared against downstream.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 line 6870 — Tseitin charge `χ : V_n → {±1}`, parity
      violation `(1 − χ(v) · sgn Φ_v)_+`.
    * §28.3 line 6889 — Bridge A: `E_v ≥ α_0 ⟹ rk_SPDP(Q_v) ≥ κ`,
      composed arithmetically here over the active set
      `S = {v : α_0 ≤ E_v}`.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import PallLean.Paper93.Concrete.RegularGraphFixed
import PallLean.Paper93.Paper283.BridgeAComposition
import PallLean.Paper93.Paper283.BridgeALocalEnergy
import PallLean.Paper93.Paper283.BridgeALocalRank
import PallLean.Paper93.Paper283.TseitinCharge

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- **Bridge A total-rank composition (inequality form)**.

    Paper §28.3 line 6889, composed pointwise. Given the per-vertex
    rank hypothesis `hPerVertex` — which states that every vertex `v`
    in the active set `S` carries a local SPDP rank at least `κ` — the
    total rank `∑_{v ∈ S} κ` is bounded above by the sum of
    per-vertex ranks `∑_{v ∈ S} (gadgetFamily v).rank`.

    This is the "real composition" step from Y6's local Bridge A rank
    bound (pointwise `κ ≤ (gadgetFamily v).rank`) to a sum-indexed
    inequality over the active set; it is discharged directly by
    `Finset.sum_le_sum` applied to the hypothesis `hPerVertex`. -/
theorem bridgeA_totalRank_composition {N d : ℕ}
    (α β α0 : ℝ) (κ : ℕ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (hPerVertex : ∀ v ∈ activeSet (α := α) (β := β) (α0 := α0) G χ Φ,
                  κ ≤ (gadgetFamily v).rank) :
    ∑ v ∈ activeSet (α := α) (β := β) (α0 := α0) G χ Φ, κ ≤
    ∑ v ∈ activeSet (α := α) (β := β) (α0 := α0) G χ Φ,
      (gadgetFamily v).rank := by
  -- Pointwise dominance `κ ≤ (gadgetFamily v).rank` on every `v ∈ S`
  -- lifts to the summed inequality via `Finset.sum_le_sum`.
  apply Finset.sum_le_sum
  exact hPerVertex

/-- **Bridge A total-rank as `|S| · κ`**.

    Paper §28.3 line 6889. The pure combinatorial content of composing
    a constant per-vertex rank bound `κ` over the active set: summing
    `κ` over the `Finset` `S` equals `|S| · κ`. This is the identity
    `Finset.sum_const` specialised to natural numbers (where `•` is
    multiplication, via `Nat.smul_eq_mul`). -/
theorem bridgeA_totalRank_equals_card_kappa {N d : ℕ}
    (α β α0 : ℝ) (κ : ℕ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ) :
    ∑ v ∈ activeSet (α := α) (β := β) (α0 := α0) G χ Φ, κ =
    (activeSet (α := α) (β := β) (α0 := α0) G χ Φ).card * κ := by
  -- `Finset.sum_const` yields `|S| • κ`; on `ℕ`, `•` reduces to `*`.
  rw [Finset.sum_const, smul_eq_mul]

end PallLean.Paper93.Paper283
