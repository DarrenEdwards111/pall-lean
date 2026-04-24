/-
  PallLean/Paper93/Paper283/BridgeAComposition.lean

  Paper §28.3 — Bridge A, composed over the **active set** `S` of
  vertices whose local energy meets the analytic threshold `α_0`.

  ## Scope (Y7, paper-faithful)

  Y6 (`BridgeALocalRank.lean`) supplies the *local* rank form of
  Bridge A: at a single vertex `v`, if the analytic energy threshold
  `α_0 ≤ E_v(Φ)` holds and the family-level hypothesis
  `hGadgetRank` records the paper's analytic-to-algebraic derivation,
  then `κ ≤ (gadgetFamily v).rank`.

  The present Y7 module composes that local bound over the set of
  vertices which clear the threshold. Concretely:

    * `activeSet G χ Φ` is the `Finset (Fin N)` of vertices `v` where
      `α_0 ≤ E_v(Φ)` — i.e.\ the vertices at which the local form of
      Bridge A kicks in;
    * `bridgeA_total_rank` states the arithmetic composition of the
      per-vertex rank bound: summing `κ` over the active set equals
      `|S| · κ`, and every vertex in `S` individually carries a rank
      lower bound of `κ` (via the hypothesis `hRank`, which is the
      Y6 output threaded through the active set).

  The aggregate identity

      ∑_{v ∈ S} κ = |S| · κ

  is the pure combinatorial ingredient that the rest of the §28.3
  chain consumes when turning a per-vertex rank lower bound into a
  *global* rank budget over the active set. The present file records
  it as a kernel-only statement together with the rank-side hypothesis
  coming from Y6; downstream files compose this with Bridge B
  (log-det ⟹ global rank) to close §28.3.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 line 6870 — Tseitin charge `χ : V_n → {±1}`, parity
      violation `(1 − χ(v) · sgn Φ_v)_+`.
    * §28.3 line 6889 — Bridge A: `E_v ≥ α_0 ⟹ rk_SPDP(Q_v) ≥ κ`,
      composed here over the active set `S = {v : E_v ≥ α_0}`.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import PallLean.Paper93.Concrete.RegularGraphFixed
import PallLean.Paper93.Paper283.BridgeALocalEnergy
import PallLean.Paper93.Paper283.BridgeALocalRank
import PallLean.Paper93.Paper283.TseitinCharge

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- **Active set** of vertices where the per-vertex local energy
    `E_v(Φ)` clears the analytic threshold `α_0`.

    Paper §28.3 line 6889: Bridge A applies pointwise at each vertex
    whose local energy is at least `α_0`. The *active set* collects
    exactly those vertices; the local rank bound of Y6
    (`bridgeA_rank_lower_bound`) then yields a per-vertex rank `≥ κ`
    on this set, which we compose arithmetically below. -/
noncomputable def activeSet {N d : ℕ}
    (α β α0 : ℝ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun v => α0 ≤ localEnergy α β G χ Φ v)

/-- The active set is a sub-`Finset` of the full vertex set, so its
    cardinality is at most `N`.

    This bookkeeping lemma is the counterpart of the paper's remark
    that the active set `S` is a subset of the vertex set `V_n`; it is
    used downstream to compare the active-set rank budget with the
    global ambient dimension. -/
theorem activeSet_card_le {N d : ℕ}
    (α β α0 : ℝ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ) :
    (activeSet (N := N) (d := d) α β α0 G χ Φ).card ≤ N := by
  classical
  -- Unfold and use `card_filter_le` together with `card_univ = N`.
  unfold activeSet
  have h1 :
      (Finset.univ.filter
          (fun v : Fin N => α0 ≤ localEnergy α β G χ Φ v)).card
        ≤ (Finset.univ : Finset (Fin N)).card :=
    Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Fin N)).card = N := by
    simp [Finset.card_univ]
  exact h1.trans (le_of_eq h2)

/-- **Bridge A, composed over the active set (rank form)**.

    Paper §28.3 line 6889, composed pointwise. Given:

      * a per-vertex local-gadget family `gadgetFamily`, and
      * the family-level rank hypothesis `hRank` (the rank output of
        Y6's `bridgeA_rank_lower_bound`, threaded through `activeSet`),
        which asserts that every active vertex carries a local SPDP
        rank `≥ κ`,

    this theorem packages the two conclusions of the composition:

      1. the arithmetic identity
         `∑_{v ∈ S} κ = |S| · κ` (the pure combinatorial content of
         composing a constant per-vertex bound over the active set);
      2. the per-vertex rank bound `κ ≤ (gadgetFamily v).rank` for
         every `v ∈ S` (recorded here as a membership-indexed
         conjunction, obtained directly from `hRank`).

    Together these two conclusions are exactly what downstream §28.3
    machinery needs: a uniform lower bound on the local SPDP rank over
    the active set, packaged with the total rank budget
    `|S| · κ`. -/
theorem bridgeA_total_rank {N d : ℕ}
    (α β α0 : ℝ) (κ : ℕ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (χ : TseitinCharge N) (Φ : Fin N → ℝ)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (hRank :
        ∀ v ∈ activeSet (N := N) (d := d) α β α0 G χ Φ,
          κ ≤ (gadgetFamily v).rank) :
    (∑ _v ∈ activeSet (N := N) (d := d) α β α0 G χ Φ, κ)
        = (activeSet (N := N) (d := d) α β α0 G χ Φ).card * κ ∧
    ∀ v ∈ activeSet (N := N) (d := d) α β α0 G χ Φ,
      κ ≤ (gadgetFamily v).rank := by
  classical
  refine ⟨?_, hRank⟩
  -- Summing the constant `κ` over any `Finset` equals `|S| · κ`.
  -- This is the statement `Finset.sum_const` with `• = *` on `ℕ`.
  simp [Finset.sum_const, smul_eq_mul, mul_comm]

end PallLean.Paper93.Paper283
