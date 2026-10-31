import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExactBoundedDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pPolyFull
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearisation

/-!
# The exact BT normal form for bounded-fan-in ACC⁰[p] (PROVED)

The cash-out of the exact bounded-fan-in degree bound.  Combining
* `toPoly_eval_AC0p` — `toPoly` is **eval-exact** for ACC⁰[p] syntax (no approximation),
* `toPoly_totalDegree_le_of_faninLe` — exact degree `≤ w^depth` for bounded fan-in,
* `support_mem_lowDeg` + `beigelTarui_monomial_count_le` — degree ⇒ quasipoly support,

gives, for every **bounded-fan-in** constant-depth ACC⁰[p] circuit, an **exact** sparse polynomial
representation:

  `acc0_exact_bt_normal_form` — `toPoly p C` (i) **equals** `C` on every Boolean input, (ii) has total
  degree `≤ w^D`, (iii) has monomial support `≤ (n+1)^{w^D}` — all **exactly**, no RS error.

This is the **exact** analogue of `acc0_to_bt_normal_form` (which used the RS *approximant* `toApprox`):
for bounded fan-in, the Beigel–Tarui sparse low-degree representation holds *without approximation*.

## What is proved (clean axioms, no `sorry`)

* `acc0_exact_bt_normal_form` — exact eval + degree `≤ w^D` + quasipoly support, for bounded-fan-in ACC⁰[p].

## Honest scope

Exact (no approximation) BT normal form for **bounded fan-in** + **constant depth** (`FaninLe w` +
`IsAC0pSyntax p` + `depth ≤ D`): degree polylog, support quasipoly, eval-exact.  Unbounded fan-in is the
no-go (`ACC0ExactDegreeNoGo`); the unbounded exact-quasipoly route is the open Beigel–Tarui integer
construction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExactBTNormalForm

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0ExactBoundedDegree (FaninLe toPoly_totalDegree_le_of_faninLe)
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity (beigelTarui_monomial_count_le)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (support_mem_lowDeg)

variable {n : ℕ}

/-- **Exact BT normal form for bounded-fan-in ACC⁰[p] (proved).**  For a bounded-fan-in (`FaninLe w`),
ACC⁰[p]-syntax (`IsAC0pSyntax p`), depth-`≤ D` circuit `C`: `toPoly p C` equals `C` on every Boolean
input, has total degree `≤ w^D`, and has `≤ (n+1)^{w^D}` distinct monomial supports — all exactly. -/
theorem acc0_exact_bt_normal_form (p w D : ℕ) [Fact p.Prime] (hw : 1 ≤ w)
    (C : BoolCircuitSyntax n) (hfan : FaninLe w C)
    (hac : BoolCircuitSyntax.IsAC0pSyntax p C) (hdepth : C.depth ≤ D) :
    (∀ x : Fin n → Bool, eval (embed p x) (toPoly p C) = boolToZMod p (C.eval x))
      ∧ (toPoly p C).totalDegree ≤ w ^ D
      ∧ ((toPoly p C).support.image (fun d => d.support)).card ≤ (n + 1) ^ (w ^ D) := by
  have hdeg : (toPoly p C).totalDegree ≤ w ^ D :=
    le_trans (toPoly_totalDegree_le_of_faninLe p w hw C hfan) (Nat.pow_le_pow_right hw hdepth)
  refine ⟨fun x => toPoly_eval_AC0p p x C hac, hdeg, ?_⟩
  refine le_trans (Finset.card_le_card ?_) (beigelTarui_monomial_count_le n (w ^ D))
  intro S hS
  rw [Finset.mem_image] at hS
  obtain ⟨d, hd, rfl⟩ := hS
  exact support_mem_lowDeg (toPoly p C) hdeg hd

/-!
**Exact BT normal form proved.**  For bounded-fan-in constant-depth ACC⁰[p]: `toPoly` is eval-exact,
degree `≤ w^D`, support `≤ (n+1)^{w^D}` — the Beigel–Tarui sparse low-degree representation *without*
approximation (the exact analogue of `acc0_to_bt_normal_form`).  Unbounded fan-in is the no-go; the
unbounded exact-quasipoly route is the open Beigel–Tarui integer construction.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ExactBTNormalForm

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactBTNormalForm.acc0_exact_bt_normal_form
