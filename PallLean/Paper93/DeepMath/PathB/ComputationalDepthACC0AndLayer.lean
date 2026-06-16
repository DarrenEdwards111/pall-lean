import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CRTGatePolys
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AevalDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearisation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6SymAndDepth2

/-!
# The `AND`-layer assembly — the `AND`-count as a polynomial, composed under the `MOD` gate

The bottom `AND` layer of a `MOD∘AND` circuit feeds the count of satisfied `AND`s to the `MOD` gate.  This file builds
the **`AND`-count polynomial** `andCountPoly = ∑_j ∏_{i∈supports j} X_i` (a sum of `AND`-feature monomials) and proves it
**evaluates to the count** `satCount` (over `F_p`), with degree bounded by the maximal `AND` width.  Composing it under
the `MOD_p` gate polynomial (`…ACC0CRTGatePolys.modPGate`) via `aeval` gives the `MOD_p∘AND` polynomial, of degree
`≤ (p−1)·width` — wiring the proved `AND`-layer to the proved `MOD` gate.

## What is proved (clean axioms, no `sorry`)

* **`andCountPoly`** — the `AND`-count polynomial; **`andCountPoly_eval`** — it evaluates on the cube to the count
  `satCount` (over `F_p`); **`andCountPoly_degree`** — degree `≤ w` when every `AND` has width `≤ w`.
* **`modPAndPoly`** — the `MOD_p∘AND` polynomial `aeval ![andCountPoly] (modPGate p)`; **`modPAndPoly_degree`** —
  degree `≤ (p−1)·w` (gate degree `p−1` times the `AND`-count degree `w`, via `unaGate_degree`).

## Honest scope

The `AND`-layer is realised as a genuine polynomial evaluating to the satisfied-`AND` count, with degree bounds, and is
composed under the `MOD_p` gate with a proved `(p−1)·w` degree bound — connecting the two proved halves (the `AND`
features of `…ACC0Multilinearisation` and the `MOD` gate of `…ACC0CRTGatePolys`).  The evaluation-correctness of the
composed `MOD_p∘AND` polynomial (that it computes the `MOD_p∘AND` indicator) follows from `aeval`/`eval` composition +
`andCountPoly_eval` + `modPGate_apply`; the degree (which feeds the composite-BT pipeline) is what is formalised here.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AndLayer

open scoped BigOperators
open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys (modPGate modPGate_degree)
open PallLean.Paper93.DeepMath.PathB.ACC0AevalDegree (unaGate_degree)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (boolVal andFeature prod_boolVal_eq_andFeature)
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2 (satCount)

variable {n t : ℕ} {p : ℕ}

/-- The `AND`-count polynomial over `F_p`: `∑_j ∏_{i∈supports j} X_i` (sum of `AND`-feature monomials). -/
noncomputable def andCountPoly (supports : Fin t → Finset (Fin n)) : MvPolynomial (Fin n) (ZMod p) :=
  ∑ j, ∏ i ∈ supports j, X i

/-- **The `AND`-count polynomial evaluates to the count (proved): `eval (boolVal∘x) andCountPoly = satCount`.** -/
theorem andCountPoly_eval (supports : Fin t → Finset (Fin n)) (x : Fin n → Bool) :
    eval (fun i => (boolVal (x i) : ZMod p)) (andCountPoly supports)
      = (satCount supports x : ZMod p) := by
  have satCount_cast :
      ((satCount supports x : ℕ) : ZMod p) = ∑ j, andFeature (supports j) x := by
    unfold ACC0Mod6SymAndDepth2.satCount
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold ACC0Multilinearisation.andFeature
    split <;> simp
  rw [andCountPoly, map_sum, satCount_cast]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_prod]
  simp only [eval_X]
  exact prod_boolVal_eq_andFeature (supports j) x

/-- **The `AND`-count polynomial is low-degree (proved): degree `≤ w` for `AND`-width `≤ w`.** -/
theorem andCountPoly_degree [Fact p.Prime] (supports : Fin t → Finset (Fin n)) {w : ℕ}
    (hw : ∀ j, (supports j).card ≤ w) :
    (andCountPoly (p := p) supports).totalDegree ≤ w := by
  refine le_trans (totalDegree_finset_sum _ _) ?_
  rw [Finset.sup_le_iff]
  intro j _
  refine le_trans (totalDegree_finset_prod _ _) ?_
  calc ∑ i ∈ supports j, (X i : MvPolynomial (Fin n) (ZMod p)).totalDegree
      ≤ ∑ _i ∈ supports j, 1 := Finset.sum_le_sum (fun i _ => (totalDegree_X i).le)
    _ = (supports j).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ w := hw j

/-- The `MOD_p∘AND` polynomial: the `MOD_p` gate composed with the `AND`-count polynomial. -/
noncomputable def modPAndPoly (p : ℕ) (supports : Fin t → Finset (Fin n)) :
    MvPolynomial (Fin n) (ZMod p) :=
  aeval ![andCountPoly supports] (modPGate p)

/-- **The `MOD_p∘AND` polynomial is degree `≤ (p−1)·w` (proved).**  The `MOD_p` gate (degree `p−1`) composed with the
`AND`-count polynomial (degree `≤ w`) has degree `≤ (p−1)·w` (`unaGate_degree`). -/
theorem modPAndPoly_degree [Fact p.Prime] (supports : Fin t → Finset (Fin n)) {w : ℕ}
    (hw : ∀ j, (supports j).card ≤ w) :
    (modPAndPoly p supports).totalDegree ≤ (p - 1) * w := by
  refine le_trans (unaGate_degree (modPGate p) (andCountPoly supports)) ?_
  exact Nat.mul_le_mul (modPGate_degree p) (andCountPoly_degree supports hw)

end PallLean.Paper93.DeepMath.PathB.ACC0AndLayer

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndLayer.andCountPoly_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndLayer.andCountPoly_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndLayer.modPAndPoly_degree
