import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RSToSymAnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ProbabilisticForm

/-!
# The basis bridge: parity forms ARE low monomial-`AND` degree (resolving the `F₂`-poly vs `monoAND` mismatch)

The probabilistic-method construction (`…ACC0ProbabilisticForm` … `…ACC0SamplingForms`) builds the boosted
predictors out of `F₂` **linear forms** `L_S(v) = ⊕_{i∈S} v_i`, which reference *large* sets `S`.  This looked like a
basis mismatch with the socket's `IsLowDegreeGate`, which is **monomial-`AND`**-based.  The resolution — and the
framing decision for this bridge — is:

> **The correct low-degree notion is `F₂`-polynomial total degree.**  A linear form `L_S` has *polynomial* degree `1`
> (it is the *sum* `∑_{i∈S} X_i`, not the *product*), regardless of how large `S` is.  So the boosted predictor
> `q_σ(v) = ⋁_k L_{σ k}(v) = 1 − ∏_k (1 − L_{σ k})` is a polynomial of total degree `≤ t`.  And a degree-`≤t` `F₂`
> polynomial's Boolean-cube evaluation lies in the span of monomial-`AND`s of fan-in `≤ t` (`lowDegPolyEval_mem_monoAND_span`).

So there is no mismatch: the boosted parity predictor *is* a low-monomial-`AND`-degree object (degree `≤ t`), even
though its individual forms are wide.  The "large set" lives in the *linear* part (degree 1), and only `t` of them
multiply.

## What is proved (clean axioms, no `sorry`)

* `linForm` / `boostPoly` — the `F₂` linear form `∑_{i∈S} X_i` and the boosted polynomial `1 − ∏_k (1 − L_{σ k})`.
* `linForm_totalDegree_le` (`≤ 1`) and **`boostPoly_totalDegree_le`** (`≤ t`) — the degree crux.
* `eval_boostPoly_eq` — `boostPoly` evaluates (on the Boolean cube) to the boosted predictor `[∃ k, L_{σ k}(v) = 1]`.
* **`boostPredict_mem_monoAND_span`** — the bridge: the boosted parity predictor's `F₂`-embedding lies in the span of
  the monomial-`AND` indicators of degree `≤ t` (the `SYM∘AND` bottom layer), via `lowDegPolyEval_mem_monoAND_span`.

## Honest scope

This resolves the basis bridge **for the `OR`-gate construction**: the boosted parity predictor is a genuine
degree-`≤t` `F₂` polynomial = fan-in-`≤t` monomial-`AND` combination, so the probabilistic-method family
(`…ACC0SamplingForms`) lives in the low-monomial-`AND`-degree world the socket wants.  Turning span membership into the
exact `symEval`-`IsLowDegreeGate` packaging is the coefficient-duplication step (`…ACC0PolyToSymAnd`, already proved
for the cash-out).  What this does **not** do — and does not claim — is the *full* Beigel–Tarui front half: that is
the construction for an *arbitrary `ACC⁰` circuit across constant depth* (the `(log s)^{O(d)}` degree, the `MOD`
layers, the depth composition), of which the single unbounded-fan-in `OR` handled here is one gate.  The depth
composition over all of `ACC⁰` remains **Wall 1**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm

variable {m t : ℕ}

/-- The `F₂` **linear form** `L_S = ∑_{i∈S} X_i` — *polynomial* degree `1`, regardless of `|S|`. -/
noncomputable def linForm (S : Finset (Fin m)) : MvPolynomial (Fin m) (ZMod 2) :=
  ∑ i ∈ S, X i

/-- The **boosted polynomial** `1 − ∏_k (1 − L_{σ k})` — the `OR` of `t` linear forms, of total degree `≤ t`. -/
noncomputable def boostPoly (σ : Fin t → Finset (Fin m)) : MvPolynomial (Fin m) (ZMod 2) :=
  1 - ∏ k, (1 - linForm (σ k))

/-- The boosted predictor (Bool): fires iff some form is `1`. -/
def boostPredict (σ : Fin t → Finset (Fin m)) (v : Fin m → Bool) : Bool :=
  decide (∃ k, pv v (σ k) = 1)

/-- **A linear form has total degree `≤ 1` (proved): it is a *sum*, not a product.** -/
theorem linForm_totalDegree_le (S : Finset (Fin m)) : (linForm S).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact le_of_eq (totalDegree_X i)

/-- `1 − L_S` has total degree `≤ 1` (proved). -/
theorem oneSubLin_totalDegree_le (S : Finset (Fin m)) :
    ((1 : MvPolynomial (Fin m) (ZMod 2)) - linForm S).totalDegree ≤ 1 := by
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le 1) (linForm_totalDegree_le S)

/-- **The boosted polynomial has total degree `≤ t` (proved) — the degree crux of the basis bridge.** -/
theorem boostPoly_totalDegree_le (σ : Fin t → Finset (Fin m)) : (boostPoly σ).totalDegree ≤ t := by
  unfold boostPoly
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  refine max_le (Nat.zero_le t) ?_
  refine le_trans (totalDegree_finset_prod Finset.univ _) ?_
  calc ∑ k : Fin t, ((1 : MvPolynomial (Fin m) (ZMod 2)) - linForm (σ k)).totalDegree
      ≤ ∑ _k : Fin t, 1 := Finset.sum_le_sum (fun k _ => oneSubLin_totalDegree_le (σ k))
    _ = t := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- `linForm` evaluates to the parity form `pv` on the Boolean cube (proved). -/
theorem eval_linForm (v : Fin m → Bool) (S : Finset (Fin m)) :
    eval (fun i => boolToZMod 2 (v i)) (linForm S) = pv v S := by
  unfold linForm pv
  rw [eval_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [eval_X]; rfl)

/-- `boostPoly` evaluates to `1 − ∏_k (1 − pv v (σ k))` on the Boolean cube (proved). -/
theorem eval_boostPoly (v : Fin m → Bool) (σ : Fin t → Finset (Fin m)) :
    eval (fun i => boolToZMod 2 (v i)) (boostPoly σ) = 1 - ∏ k, (1 - pv v (σ k)) := by
  unfold boostPoly
  rw [eval_sub, map_one, eval_prod]
  congr 1
  exact Finset.prod_congr rfl (fun k _ => by rw [eval_sub, map_one, eval_linForm])

/-- **`boostPoly` evaluates to the boosted predictor (proved): the polynomial really computes `⋁_k L_{σ k}`.** -/
theorem eval_boostPoly_eq (v : Fin m → Bool) (σ : Fin t → Finset (Fin m)) :
    eval (fun i => boolToZMod 2 (v i)) (boostPoly σ) = boolToZMod 2 (boostPredict σ v) := by
  rw [eval_boostPoly]
  by_cases h : ∃ k, pv v (σ k) = 1
  · rw [Finset.prod_eq_zero (Finset.mem_univ h.choose)
        (show (1 : ZMod 2) - pv v (σ h.choose) = 0 by rw [h.choose_spec]; decide), sub_zero]
    simp [boostPredict, boolToZMod, h]
  · rw [Finset.prod_eq_one (fun j _ =>
        show (1 : ZMod 2) - pv v (σ j) = 1 by
          have hj0 : pv v (σ j) = 0 := by
            by_contra hj
            exact h ⟨j, (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) (pv v (σ j)) hj⟩
          rw [hj0]; decide)]
    simp [boostPredict, boolToZMod, h]

/-- **The basis bridge (proved).**  The boosted parity predictor's `F₂`-embedding lies in the span of the monomial-`AND`
indicators of degree `≤ t` — the `SYM∘AND` bottom layer.  So the parity-form construction is a genuine
low-monomial-`AND`-degree object, despite its wide linear forms. -/
theorem boostPredict_mem_monoAND_span (σ : Fin t → Finset (Fin m)) :
    (fun v : Fin m → Bool => boolToZMod 2 (boostPredict σ v))
      ∈ Submodule.span (ZMod 2)
        (Set.range (fun S : {S // S ∈ lowDegMonomials m t} =>
          fun v : Fin m → Bool => if monoAND S.1 v then (1 : ZMod 2) else 0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkey := lowDegPolyEval_mem_monoAND_span 2 t (boostPoly σ) (boostPoly_totalDegree_le σ)
  have hfun : (fun v : Fin m → Bool => boolToZMod 2 (boostPredict σ v))
      = (fun v : Fin m → Bool => eval (fun i => boolToZMod 2 (v i)) (boostPoly σ)) := by
    funext v
    exact (eval_boostPoly_eq v σ).symm
  rw [hfun]
  exact hkey

end PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge.boostPoly_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge.eval_boostPoly_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge.boostPredict_mem_monoAND_span
