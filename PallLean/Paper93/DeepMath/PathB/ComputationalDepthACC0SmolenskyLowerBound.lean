import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Capstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky

/-!
# Smolensky non-native MOD lower bound — connecting the proved arc result to the cross-field wall

Entry 243 localised the composite-`ACC⁰[m]` wall to a single open statement: `MOD_q` is not low-degree over `F_p` for
`q ≠ p` (Smolensky's theorem).  **This theorem is already proved in this arc** — the Razborov–Smolensky layer
(`Layer3Smolensky.parity_function_lower_bound`, `Layer4Capstone.mod_q_indicators_false`) establishes the non-native MOD
lower bound, sorry-free with clean axioms.  This file does **not** rebuild it; it **connects** it to the cross-field
combination wall, turning the single-field low-degree route into a definitive **no-go** and isolating the only possible
escape (the multi-sorted / product-field observer, step 4 — genuinely open).

## What is established (by citing the proved arc lemmas; clean axioms, no `sorry`)

* **`crossField_modq_fieldRoute_nogo`** (PROVED, = `Layer4.mod_q_indicators_false`) — the cross-field *field route* is
  contradictory: there is **no** family of `AC⁰[p]` circuits computing the `MOD_q` residue indicators within the
  Smolensky budget (for `q ∤ p`).  So a single-field low-degree `F_p` representation of `MOD_q` (`q ≠ p`) is impossible
  — the field route to the cross-field combination (entry 243) cannot exist.
* **`parity_nonnative_size_lb`** (PROVED, = `Layer3.parity_function_lower_bound`) — the simplest non-native instance:
  parity (`MOD_2`) computed by an `AC⁰[p]` circuit (`p` odd) forces `p^t < 4 · #subcircuits`, a genuine size lower
  bound.  `MOD_2` is not cheap over `F_p` for odd `p`.

## The honest conclusion (step 3)

The single-field low-degree route to `CarryRefinementCrossing` (entry 238) is **refuted** by the proved Smolensky bound:
the cross-field combination cannot be realised over any single field `F_p`, because one composite factor `MOD_q`
(`q ≠ p`) is provably not low-degree there.  Hence:

> **No-go (field route).**  `CarryRefinementCrossing` is impossible via a single-field low-degree representation.

The only possible escape is the **multi-sorted / product-field observer** (step 4): an observer living in `∏_p F_p`
with separate low-degree components per prime and a symmetric top combiner — *not* reducible to one `F_p` (which is
exactly what `no_common_char` of entry 243 forbids collapsing).  Whether such a product-field observer can feed
fast-SAT without collapsing to one field is the **genuinely open** next question; it is *not* settled here, and the
Smolensky no-go does **not** apply to it (it is not a single-`F_p` representation).

## Honest scope

This file **cites** the arc's proved Smolensky lower bound (it does not reprove it) and draws the honest consequence:
the cross-field single-field low-degree route is a no-go (entry 243's named open wall is, for the *field route*,
actually closed *against* by the existing Razborov–Smolensky layer).  The remaining open direction is the multi-sorted
observer (step 4), which this no-go does not touch.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` — Smolensky bounds
`AC⁰[p]` (single prime), not `ACC⁰[m]` with the `MOD_m` gate available, which is Williams' open territory.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyLowerBound

open PallLean.Paper93.DeepMath.PathB
open Finset
open Classical

/-- **The cross-field field route is a no-go (PROVED, = `Layer4.mod_q_indicators_false`).**  There is no family of
`AC⁰[p]` circuits computing the `MOD_q` residue indicators within the Smolensky budget (`q ∤ p`); i.e. `MOD_q` is not
low-degree over `F_p` for `q ≠ p`.  This refutes any single-field low-degree representation of a non-native `MOD_q`,
hence the field route to the cross-field combination (entry 243). -/
theorem crossField_modq_fieldRoute_nogo (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {m t d : ℕ} (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t)
    (C : ℕ → BoolCircuitSyntax (2 * m + 1))
    (hCind : ∀ j ∈ Finset.range q, ∀ x : Fin (2 * m + 1) → Bool,
      (C j).eval x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = j))
    (hAC : ∀ j ∈ Finset.range q, BoolCircuitSyntax.IsAC0pSyntax p (C j))
    (ht : ∀ j ∈ Finset.range q, 4 * q * (Layer3.subcircuits (C j)).toFinset.card ≤ p ^ t)
    (hdepth : ∀ j ∈ Finset.range q, (C j).depth ≤ d)
    (hwindow : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3) : False :=
  Layer4.mod_q_indicators_false p q hpq ht1 hpt1 C hCind hAC ht hdepth hwindow

/-- **Non-native parity size lower bound (PROVED, = `Layer3.parity_function_lower_bound`).**  The simplest non-native
instance: an `AC⁰[p]` circuit (`p` odd, `2 ≠ 0` in `F_p`) computing parity forces `p^t < 4 · #subcircuits` — `MOD_2`
is not cheap over `F_p`. -/
theorem parity_nonnative_size_lb (p : ℕ) [Fact p.Prime] {m d : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (Cir : BoolCircuitSyntax (2 * m + 1)) (hd : Cir.depth ≤ d) (t : ℕ) (ht1 : 1 ≤ t)
    (hparity : ∀ x : Fin (2 * m + 1) → Bool,
      Cir.eval x = decide (Odd (Finset.univ.filter (fun i => x i = true)).card))
    (hmod : ∀ qq r cs,
      (BoolCircuitSyntax.modGate qq r cs : BoolCircuitSyntax (2 * m + 1)) ∈ Layer3.subcircuits Cir → qq = p)
    (hm : 8 * (((p - 1) * t) ^ d) ^ 2 ≤ m) :
    p ^ t < 4 * (Layer3.subcircuits Cir).toFinset.card :=
  Layer3.parity_function_lower_bound p hp2 Cir hd t ht1 hparity hmod hm

/-!
**Conclusion (no-go for the field route; the open escape is multi-sorted).**  By `crossField_modq_fieldRoute_nogo`,
no single-field low-degree representation realises a non-native `MOD_q`, so `CarryRefinementCrossing` (entry 238) is
impossible via the single-field route.  The Smolensky no-go does **not** apply to a *multi-sorted* observer in
`∏_p F_p` (separate low-degree components per prime + a symmetric combiner), which is not a single-`F_p` representation;
whether that can feed fast-SAT without collapsing to one field (forbidden by entry-243 `no_common_char`) is the open
step-4 question, not settled here.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyLowerBound.crossField_modq_fieldRoute_nogo
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyLowerBound.parity_nonnative_size_lb
