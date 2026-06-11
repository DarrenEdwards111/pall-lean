import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4DimGeneral

/-!
# Layer 4 (Route A) — the `q`-ary degree halving and reduction

This is the genuine algebraic core of the `MOD_q` degree reduction (scope §3-C, Route A), and it
**corrects** the earlier pessimistic claim in `SCOPE_LAYER4_3C_DEGREE_REDUCTION.md` that the parity
halving "has no `q > 2` analogue".

Parity (`q = 2`) used the **involution** `yᵢ² = 1`. The general-`q` analogue is not an involution but a
**`ζ`/`ζ⁻¹` pairing**: with `qFactor ζ b = 1 + (ζ-1)·b = ζ^b` (for `b ∈ {0,1}`),
\[
  \texttt{qFactor}\,\zeta\,b \cdot \texttt{qFactor}\,\zeta^{-1}\,b \;=\; \zeta^b\,(\zeta^{-1})^b \;=\; 1 ,
\]
so on the complement `Sᶜ` the `ζ` and `ζ⁻¹` factors cancel, giving the **`q`-ary halving**
\[
  \texttt{qChar}\,\zeta\,\mathrm{univ}\;\cdot\;\texttt{qChar}\,\zeta^{-1}\,S^c \;=\; \texttt{qChar}\,\zeta\,S
  \qquad(\texttt{qChar}\,\zeta\,S\,x = \textstyle\prod_{i\in S}\zeta^{x_i} = \zeta^{\#\{i\in S:x_i\}}),
\]
exactly mirroring Layer 3's `pm_monomial_halving` (`χ_univ · χ_{Sᶜ} = χ_S`) with the pairing replacing
the involution.  Consequently (`qChar_reduction`, the analogue of `pm_monomial_reduction`): once the full
weight character `qChar ζ univ = ζ^{#ones}` has a degree-`Δ` representative on `G`, every `ζ`-character
`qChar ζ S` with `|S| > n/2` agrees on `G` with a polynomial of degree `≤ Δ + (n-|S|) ≤ Δ + n/2`.

Specialising `ζ = -1` (so `ζ⁻¹ = ζ`) recovers the parity halving.  The remaining pieces of `(★)` (scope
§3-C) are: **(2)** the `ζ`-characters span the function space (a *triangular* change of basis to the
squarefree monomials — not the subalgebra argument, since `qChar` is not multiplicatively closed); and
**(3)** the genuinely circuit-side input that `ζ^{#ones}` is low-degree on `G` given `MOD_q ∈ AC⁰[p]`
(via the `q` shifted `MOD_q` indicators).  Those are still open and **not faked**.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset MvPolynomial

/-- The **`ζ`-character over `S`**: `qChar ζ S x = ∏_{i∈S} ζ^{xᵢ} = ζ^{#{i∈S : xᵢ}}` (the partial weight
character; `qChar ζ univ = weightChar ζ`). -/
noncomputable def qChar (K : Type*) [Field K] (ζ : K) {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : K :=
  ∏ i ∈ S, (1 + (ζ - 1) * (if x i then 1 else 0))

/-- **The `ζ`/`ζ⁻¹` pairing** (replacing parity's involution `y²=1`): `ζ^b · (ζ⁻¹)^b = 1` for `b ∈ {0,1}`
(needs `ζ ≠ 0`). -/
theorem qFactor_mul_inv {K : Type*} [Field K] {ζ : K} (hζ : ζ ≠ 0) (b : Bool) :
    (1 + (ζ - 1) * (if b then (1 : K) else 0)) * (1 + (ζ⁻¹ - 1) * (if b then (1 : K) else 0)) = 1 := by
  cases b
  · show (1 + (ζ - 1) * 0) * (1 + (ζ⁻¹ - 1) * 0) = 1; ring
  · show (1 + (ζ - 1) * 1) * (1 + (ζ⁻¹ - 1) * 1) = 1
    rw [show 1 + (ζ - 1) * 1 = ζ from by ring, show 1 + (ζ⁻¹ - 1) * 1 = ζ⁻¹ from by ring]
    exact mul_inv_cancel₀ hζ

/-- **The `q`-ary halving** (analogue of `pm_monomial_halving`): `qChar ζ univ · qChar ζ⁻¹ Sᶜ = qChar ζ S`
— the `ζ` and `ζ⁻¹` factors cancel on `Sᶜ`. -/
theorem qChar_halving {K : Type*} [Field K] {ζ : K} (hζ : ζ ≠ 0) {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → Bool) :
    qChar K ζ Finset.univ x * qChar K ζ⁻¹ Sᶜ x = qChar K ζ S x := by
  rw [qChar, qChar, qChar,
    ← Finset.prod_mul_prod_compl S (fun i => 1 + (ζ - 1) * (if x i then (1 : K) else 0)),
    mul_assoc, ← Finset.prod_mul_distrib]
  simp only [qFactor_mul_inv hζ, Finset.prod_const_one, mul_one]

/-- The `ζ`-character `qChar ζ S` as a polynomial: `∏_{i∈S} (1 + (ζ-1)·Xᵢ)` (degree `≤ |S|`). -/
noncomputable def qMonomial (K : Type*) [Field K] (ζ : K) {n : ℕ} (S : Finset (Fin n)) :
    MvPolynomial (Fin n) K :=
  ∏ i ∈ S, (1 + C (ζ - 1) * X i)

theorem qMonomial_totalDegree_le (K : Type*) [Field K] (ζ : K) {n : ℕ} (S : Finset (Fin n)) :
    (qMonomial K ζ S).totalDegree ≤ S.card := by
  refine le_trans (totalDegree_finset_prod S _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (by rw [Finset.sum_const, smul_eq_mul, mul_one])
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
  · rw [totalDegree_one]; exact Nat.zero_le 1
  · exact le_trans (totalDegree_mul _ _) (by rw [totalDegree_C, zero_add, totalDegree_X])

theorem qMonomial_eval (K : Type*) [Field K] (ζ : K) {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    eval (fun i => boolToField K (x i)) (qMonomial K ζ S) = qChar K ζ S x := by
  rw [qMonomial, qChar, map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [map_add, map_one, map_mul, eval_C, eval_X, boolToField]

/-- **The `q`-ary degree reduction** (analogue of `pm_monomial_reduction`).  If a degree-`Δ` polynomial `g`
represents the full weight character `qChar ζ univ = ζ^{#ones}` on `G`, then every `ζ`-character `qChar ζ S`
agrees on `G` with a polynomial of degree `≤ Δ + (n-|S|)` (namely `g · qMonomial ζ⁻¹ Sᶜ`); for `|S| > n/2`
this is `≤ Δ + n/2` — the degree-halving collapse, now for general `q`. -/
theorem qChar_reduction (K : Type*) [Field K] {ζ : K} (hζ : ζ ≠ 0) {n : ℕ}
    (G : Finset (Fin n → Bool)) (Δ : ℕ) (g : MvPolynomial (Fin n) K) (hgdeg : g.totalDegree ≤ Δ)
    (hg : ∀ x ∈ G, eval (fun i => boolToField K (x i)) g = qChar K ζ Finset.univ x)
    (S : Finset (Fin n)) :
    ∃ h : MvPolynomial (Fin n) K, h.totalDegree ≤ Δ + (n - S.card) ∧
      ∀ x ∈ G, eval (fun i => boolToField K (x i)) h = qChar K ζ S x := by
  refine ⟨g * qMonomial K ζ⁻¹ Sᶜ, ?_, fun x hx => ?_⟩
  · refine le_trans (totalDegree_mul _ _) (le_trans (Nat.add_le_add hgdeg
      (qMonomial_totalDegree_le K ζ⁻¹ Sᶜ)) (le_of_eq ?_))
    rw [Finset.card_compl, Fintype.card_fin]
  · rw [map_mul, hg x hx, qMonomial_eval]; exact qChar_halving hζ S x

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.qChar_halving
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.qChar_reduction
