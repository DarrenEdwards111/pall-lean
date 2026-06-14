import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DimensionCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky

/-!
# Socket 1: fusing the effective-dimension bound with the holonomy correlation obstruction

The `…Layer3DimensionCount` layer proves the **effective-dimension deficit**: degree-`≤D` multilinear polynomials
on the cube span a subspace `V_D` of dimension `≤ ∑_{k≤D} C(n,k) < 2^n` (`finrank_span_lowDegEval_le_card`,
`lowDegEval_span_ne_top`).  The N-frame / holonomy layer targets the parity charge, whose `±1` encoding is
`χ(x) = ∏_i pmOne(x_i)`.  This file **fuses the two**: the holonomy parity target lies *outside* the
low-effective-dimension subspace — `χ ∉ V_D` for `D < n` — so the N-frame target has effective dimension `≥ n`,
and no degree-`≤D` polynomial represents it on the cube.

**Why this, and not the per-class engine.**  The other half of the holonomy machinery, `agreement_le_sum_majority`,
bounds the agreement of a predictor `g ∘ π` with `f` by the sum of per-class majorities — useful only when `f` is
*balanced inside each `π`-class* (`restricted_fragment_low_correlation`).  That route is intrinsically
**variable**-based: balance comes from a *missed variable* `v ∈ D` whose flip preserves `π` yet flips parity.  A
degree-`≥1` monomial statistic already contains the degree-1 monomials, i.e. *every* variable, so parity is
**determined** (never balanced) inside its classes — the per-class engine yields no parity bound when fused with
linear low-degree statistics.  The genuine dimension↔correlation fusion is therefore the **span-membership**
obstruction proved here.

The proof uses a single **top-frequency linear functional** `topFunctional f = ∑_x (∏_i (2·x_i − 1))·f(x)`: it
kills every squarefree monomial `e_S` with `S ≠ univ` (a coordinate `i ∉ S` contributes `∑_b (2b−1) = 0`), hence
annihilates `V_D` for `D < n`; but `topFunctional χ = ∑_x (∏(2x_i−1))·(−1)^n·∏(2x_i−1) = (−1)^n·∑_x 1 = (−2)^n ≠ 0`.
A linear functional nonzero on `χ` and zero on `V_D` forces `χ ∉ V_D`.

## What is proved (clean axioms, no `sorry`)

* `topFunctional` (a `LinearMap`), `topFunctional_apply`.
* `topFunctional_squarefreeEvalMonomial_eq_zero` — kills `e_S` for `S ≠ univ`.
* `topFunctional_holonomyParity` — `topFunctional χ = (2^n)·(−1)^n`.
* `holonomy_parity_not_lowDegEval` — **the fusion**: for `2 ≠ 0` and `D < n`, the holonomy parity target
  `∏_i pmOne(x_i)` is not in the degree-`≤D` evaluation span.

## Honest scope

The exact-representation (effective-dimension) obstruction for the holonomy target — the linear-algebraic core of
Razborov–Smolensky specialised to the N-frame parity charge.  It is **not** the quantitative
approximate-correlation bound (RS error-set counting, already in `parity_circuit_false`), and it is the classical
`PARITY ∉ AC⁰[p]` regime, **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3LowDegHolonomy

open PallLean.Paper93.DeepMath.PathB.Layer3

variable {n : ℕ}

/-- The top-frequency weight `∏_i (2·x_i − 1)` (the discrete character at the full-support frequency). -/
noncomputable def topWeight (p : ℕ) (x : Fin n → Bool) : ZMod p :=
  ∏ i, (2 * boolToZMod p (x i) - 1)

/-- The top-frequency linear functional `f ↦ ∑_x (∏_i (2·x_i − 1))·f(x)` on cube functions. -/
noncomputable def topFunctional (p n : ℕ) : ((Fin n → Bool) → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun f := ∑ x, topWeight p x * f x
  map_add' f g := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)

@[simp] theorem topFunctional_apply (p n : ℕ) (f : (Fin n → Bool) → ZMod p) :
    topFunctional p n f = ∑ x, topWeight p x * f x := rfl

/-- Sum over the cube of a product over coordinates factors into a product of per-coordinate sums. -/
theorem sum_cube_prod_factor (p : ℕ) (g : Fin n → Bool → ZMod p) :
    (∑ x : Fin n → Bool, ∏ i, g i (x i)) = ∏ i, ∑ b : Bool, g i b := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **The functional kills every non-full squarefree monomial (proved).**  `topFunctional (e_S) = 0` for
`S ≠ univ`: the sum factorises over coordinates, and a coordinate `i ∉ S` contributes `∑_b (2b − 1) = 0`. -/
theorem topFunctional_squarefreeEvalMonomial_eq_zero (p : ℕ) {S : Finset (Fin n)}
    (hS : S ≠ Finset.univ) :
    topFunctional p n (squarefreeEvalMonomial p S) = 0 := by
  classical
  rw [topFunctional_apply]
  have hcomb : ∀ x : Fin n → Bool,
      topWeight p x * squarefreeEvalMonomial p S x
        = ∏ i, ((2 * boolToZMod p (x i) - 1) * (if i ∈ S then boolToZMod p (x i) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, topWeight,
        squarefreeEvalMonomial]
  calc (∑ x : Fin n → Bool, topWeight p x * squarefreeEvalMonomial p S x)
      = ∑ x : Fin n → Bool,
          ∏ i, ((2 * boolToZMod p (x i) - 1) * (if i ∈ S then boolToZMod p (x i) else 1)) :=
        Finset.sum_congr rfl (fun x _ => hcomb x)
    _ = ∏ i, ∑ b : Bool, ((2 * boolToZMod p b - 1) * (if i ∈ S then boolToZMod p b else 1)) :=
        sum_cube_prod_factor p (fun i b => (2 * boolToZMod p b - 1) * (if i ∈ S then boolToZMod p b else 1))
    _ = 0 := by
        obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
          by_contra hcon
          push_neg at hcon
          exact hS (Finset.eq_univ_iff_forall.mpr hcon)
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        have ht : boolToZMod p true = 1 := rfl
        have hf : boolToZMod p false = 0 := rfl
        rw [Fintype.sum_bool]
        simp only [if_neg hi, ht, hf, mul_one]
        ring

/-- **The functional separates the holonomy target (proved).**  `topFunctional χ = (2^n)·(−1)^n`, because
`χ(x) = (−1)^n · topWeight x` and `topWeight x · topWeight x = 1` on the cube. -/
theorem topFunctional_holonomyParity (p : ℕ) :
    topFunctional p n (fun x => ∏ i, pmOne p (x i))
      = ((2 ^ n : ℕ) : ZMod p) * (-1) ^ n := by
  classical
  rw [topFunctional_apply]
  have hterm : ∀ x : Fin n → Bool, topWeight p x * (∏ i, pmOne p (x i)) = (-1) ^ n := by
    intro x
    have hchi : (∏ i, pmOne p (x i)) = (-1) ^ n * topWeight p x := by
      rw [topWeight,
          show ((-1 : ZMod p)) ^ n = ∏ _i : Fin n, (-1 : ZMod p) from by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
          ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [pmOne_eq_one_sub_two_boolToZMod]
      ring
    have hsq : topWeight p x * topWeight p x = 1 := by
      rw [topWeight, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      rcases boolToZMod_mem p (x i) with h | h <;> rw [h] <;> ring
    rw [hchi,
        show topWeight p x * ((-1) ^ n * topWeight p x)
          = (-1) ^ n * (topWeight p x * topWeight p x) from by ring, hsq, mul_one]
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, nsmul_eq_mul, hcard]

/-- **Socket 1 — the effective-dimension/holonomy fusion (proved).**  For `2 ≠ 0` (so `p` odd) and `D < n`, the
holonomy parity target `χ(x) = ∏_i pmOne(x_i)` is **not** in the span of the degree-`≤D` squarefree evaluation
monomials: it has effective dimension `> ∑_{k≤D} C(n,k)`, so no degree-`≤D` polynomial computes it on the cube.
The low-effective-dimension subspace cannot represent the N-frame holonomy target. -/
theorem holonomy_parity_not_lowDegEval (p : ℕ) [Fact p.Prime] {D : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (h : D < n) :
    (fun x => ∏ i, pmOne p (x i)) ∉ Submodule.span (ZMod p)
      (Set.range (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1)) := by
  classical
  intro hmem
  have hker : Submodule.span (ZMod p)
      (Set.range (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1))
      ≤ LinearMap.ker (topFunctional p n) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨S, hS⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    apply topFunctional_squarefreeEvalMonomial_eq_zero
    intro hSeq
    rw [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset] at hS
    have hcard : (Finset.univ : Finset (Fin n)).card ≤ D := hSeq ▸ hS.2
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have h0 : topFunctional p n (fun x => ∏ i, pmOne p (x i)) = 0 := by
    have hmemker := hker hmem
    rwa [LinearMap.mem_ker] at hmemker
  rw [topFunctional_holonomyParity] at h0
  have h2n : ((2 ^ n : ℕ) : ZMod p) ≠ 0 := by
    push_cast
    exact pow_ne_zero n hp2
  exact (mul_ne_zero h2n (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero))) h0

end PallLean.Paper93.DeepMath.PathB.Layer3LowDegHolonomy

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3LowDegHolonomy.topFunctional_squarefreeEvalMonomial_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3LowDegHolonomy.topFunctional_holonomyParity
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3LowDegHolonomy.holonomy_parity_not_lowDegEval
