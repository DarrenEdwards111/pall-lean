import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BasisBridge

/-!
# One-layer composition of Beigel–Tarui approximants: degree multiplies by `t`, not exponentially

The basis bridge (`…ACC0BasisBridge`) built the boosted `OR` approximant out of the *input variables* `X_i`.  The
depth-composition mechanism is the same construction with the variables replaced by the **subgate approximant
polynomials** `P_j`: to approximate `OR(h_1(x), …, h_k(x))`, take random linear forms over the subgate *outputs*,
`∑_{j∈S} P_j`, and boost.  This file proves the one-layer step.

If each of the `k` subgates is computed by a polynomial `P_j` of total degree `≤ d`, then the composed `OR`-layer
polynomial

```
compPoly = 1 − ∏_{l} (1 − ∑_{j ∈ σ l} P_j)
```

has total degree `≤ t · d` — the degree multiplies by the boosting parameter `t` per layer.  So across constant depth
`D` the degree is `≤ t^D · (base)` — `(log s)^{O(D)}`, **polynomial-in-`log`, not exponential**.  That is exactly the
Razborov–Smolensky degree-composition phenomenon, the engine that keeps the whole `ACC⁰` approximant low-degree.

The basis bridge is the special case `P_j = X_j`, `d = 1` (so `t·d = t`).

## What is proved (clean axioms, no `sorry`)

* `compLinForm` / `compPoly` — the linear form over subgate outputs `∑_{j∈S} P_j` and the composed `OR`-layer
  polynomial `1 − ∏_l (1 − ∑_{j∈σ l} P_j)`.
* `compLinForm_totalDegree_le` (`≤ d`) and **`compPoly_totalDegree_le`** (`≤ t · d`) — the degree-composition crux.
* `eval_compPoly` — the composed polynomial evaluates to the boosted `OR` over the subgate values `eval … P_j`.
* **`compPoly_eval_mem_monoAND_span`** — the composed approximant lies in the degree-`≤ t·d` monomial-`AND` span.

## Honest scope

This is **one `OR`-layer** of the depth composition: subgate degree `d` → composed degree `t·d`, staying low.  The
`AND`-layer is the affine dual (`…ACC0AndBasisBridge`'s `1 + ·`), and `MOD` is its own (`CRT`/count) case.  Iterating
this through a whole constant-depth `ACC⁰` circuit — tracking the *error* accumulation across layers (each boosted
approximant is only majority-correct, and errors compound), discharging the `MOD` layer, and assembling the final
`SYM∘AND` — is the rest of the Beigel–Tarui/Yao front half, **Wall 1**.  This file supplies the degree-composition
step, not the full inductive assembly.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LayerCompose

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd

variable {n k t d : ℕ}

/-- The `F₂` **linear form over the subgate outputs**: `∑_{j∈S} P_j`, where `P_j` is subgate `j`'s approximant. -/
noncomputable def compLinForm (P : Fin k → MvPolynomial (Fin n) (ZMod 2)) (S : Finset (Fin k)) :
    MvPolynomial (Fin n) (ZMod 2) :=
  ∑ j ∈ S, P j

/-- The **composed `OR`-layer polynomial** `1 − ∏_l (1 − ∑_{j∈σ l} P_j)` — the boosted `OR` over the subgates. -/
noncomputable def compPoly (P : Fin k → MvPolynomial (Fin n) (ZMod 2)) (σ : Fin t → Finset (Fin k)) :
    MvPolynomial (Fin n) (ZMod 2) :=
  1 - ∏ l, (1 - compLinForm P (σ l))

/-- **The linear form over outputs has degree `≤ d` (proved), if each subgate approximant does.** -/
theorem compLinForm_totalDegree_le (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (hP : ∀ j, (P j).totalDegree ≤ d) (S : Finset (Fin k)) :
    (compLinForm P S).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro j _
  exact hP j

/-- `1 − (linear form over outputs)` has degree `≤ d` (proved). -/
theorem oneSubCompLin_totalDegree_le (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (hP : ∀ j, (P j).totalDegree ≤ d) (S : Finset (Fin k)) :
    ((1 : MvPolynomial (Fin n) (ZMod 2)) - compLinForm P S).totalDegree ≤ d := by
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le d) (compLinForm_totalDegree_le P hP S)

/-- **One-layer degree composition (proved): subgate degree `d` → composed degree `≤ t · d`.**  The degree multiplies
by the boosting parameter `t` per layer — polynomial-in-`log` across depth, not exponential. -/
theorem compPoly_totalDegree_le (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (hP : ∀ j, (P j).totalDegree ≤ d) (σ : Fin t → Finset (Fin k)) :
    (compPoly P σ).totalDegree ≤ t * d := by
  unfold compPoly
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  refine max_le (Nat.zero_le _) ?_
  refine le_trans (totalDegree_finset_prod Finset.univ _) ?_
  calc ∑ l : Fin t, ((1 : MvPolynomial (Fin n) (ZMod 2)) - compLinForm P (σ l)).totalDegree
      ≤ ∑ _l : Fin t, d := Finset.sum_le_sum (fun l _ => oneSubCompLin_totalDegree_le P hP (σ l))
    _ = t * d := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The composed polynomial evaluates to the boosted `OR` over the subgate values (proved). -/
theorem eval_compPoly (x : Fin n → Bool) (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (σ : Fin t → Finset (Fin k)) :
    eval (fun i => boolToZMod 2 (x i)) (compPoly P σ)
      = 1 - ∏ l, (1 - ∑ j ∈ σ l, eval (fun i => boolToZMod 2 (x i)) (P j)) := by
  unfold compPoly compLinForm
  rw [eval_sub, map_one, eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  rw [eval_sub, map_one, eval_sum]

/-- **The composed approximant lies in the degree-`≤ t·d` monomial-`AND` span (proved).**  Composing low-degree
subgate approximants through an `OR` layer keeps the result a low-monomial-`AND`-degree object. -/
theorem compPoly_eval_mem_monoAND_span (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (hP : ∀ j, (P j).totalDegree ≤ d) (σ : Fin t → Finset (Fin k)) :
    (fun x : Fin n → Bool => eval (fun i => boolToZMod 2 (x i)) (compPoly P σ))
      ∈ Submodule.span (ZMod 2)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n (t * d)} =>
          fun x : Fin n → Bool => if monoAND S.1 x then (1 : ZMod 2) else 0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact lowDegPolyEval_mem_monoAND_span 2 (t * d) (compPoly P σ) (compPoly_totalDegree_le P hP σ)

end PallLean.Paper93.DeepMath.PathB.ACC0LayerCompose

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LayerCompose.compPoly_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LayerCompose.eval_compPoly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LayerCompose.compPoly_eval_mem_monoAND_span
