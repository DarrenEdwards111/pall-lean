# Handoff: Forster isotropic-position kernel (the sole remaining obligation)

**Goal:** discharge the corrected, spanning/dimension-reduced version of the
isotropic-position kernel in
`PallLean/Paper93/DeepMath/PathB/ComputationalDepthForsterScaffold.lean`
(namespace `PallLean.Paper93.DeepMath.PathB.Forster`).

**Important update:** the original same-ambient-dimension `IsotropicKernel` has
now been formally shown too strong:

```
not_isotropicKernel_as_stated :
  ¬ IsotropicKernel (m := 1) (n := 1) (fun _ _ => true)
```

The counterexample is a one-row realization in `ℝ²`: one unit vector cannot be a
tight frame for all of `ℝ²`.  So the next theorem must either require the row
vectors to span the ambient space, or first reduce to their span.  Proving the
over-strong `IsotropicKernel` directly is impossible.

Everything else in Forster is already proved (clean axioms, no sorry):
`forster_dim_ge_of_bounds` (arithmetic core), `frameLowerBound` (2),
`spectralUpperBound_proof` (3), `forster_bound_of_tightFrame`, `forster_of_kernel`.

## Already-proved interfaces (do NOT re-prove)

```
structure UnitRealization (M : Fin m → Fin n → Bool) (d : Nat) where
  u : Fin m → EuclideanSpace ℝ (Fin d)
  w : Fin n → EuclideanSpace ℝ (Fin d)
  u_unit : ∀ i, ‖u i‖ = 1
  w_unit : ∀ j, ‖w j‖ = 1
  sign_ok : ∀ i j, 0 < sgn (M i j) * ⟪u i, w j⟫

def IsTightFrame (R : UnitRealization M d) : Prop :=
  ∀ y : EuclideanSpace ℝ (Fin d), ∑ i, ⟪R.u i, y⟫ ^ 2 = ((m : ℝ) / d) * ‖y‖ ^ 2

def IsotropicKernel (M : Fin m → Fin n → Bool) : Prop :=
  ∀ {d : Nat}, Nonempty (UnitRealization M d) →
    ∃ R' : UnitRealization M d, IsTightFrame R'
```

## The core analytic theorem to prove (Forster 2002, isotropic position)

> Let `v₁,…,v_m ∈ ℝ^d`, each `≠ 0`, **spanning** `ℝ^d`. Then there is an invertible
> linear map `T : ℝ^d ≃ₗ ℝ^d` such that the normalized images `ûᵢ := T vᵢ / ‖T vᵢ‖`
> satisfy `∑ᵢ ⟪ûᵢ, y⟫² = (m/d)·‖y‖²` for all `y` (radial isotropy / tight frame).

### Proof (potential minimization)
1. Potential on SPD matrices with `det = 1`: `F(S) = ∑ᵢ log ⟪vᵢ, S vᵢ⟫` (here `S = TᵀT`).
2. **Coercivity** from the spanning hypothesis: on the `det = 1` slice, `F → +∞` as
   `S` degenerates (an eigenvalue `→ 0`), because some `vᵢ` has nonzero component in
   every eigendirection. Hence a minimizer `S⋆` exists on a compact sublevel set
   (extreme value theorem).
3. **First-order optimality** (Lagrange, constraint `det S = 1`):
   `∑ᵢ (vᵢ vᵢᵀ)/⟪vᵢ, S⋆ vᵢ⟫ = (m/d)·S⋆`. (Trace of both sides ⇒ the constant is `m/d`.)
4. Put `T = (S⋆)^{-1/2}` (matrix square root of the SPD inverse). Substituting gives
   `∑ᵢ ûᵢ ûᵢᵀ = (m/d)·I`, i.e. the tight-frame identity.

## Mathlib hooks
- Inner products / norms: `EuclideanSpace`, `real_inner_le_norm`, `PiLp.inner_apply`
  (and the file's `eucl_inner_eq_sum`, `eucl_normSq_eq_sum`).
- SPD matrices + square root: `Matrix.PosDef`, `Matrix.PosSemidef.sqrt`,
  `Matrix.PosSemidef.posSemidef_sqrt`, `Matrix.IsHermitian`.
- Spanning: `Submodule.span ℝ (Set.range v) = ⊤`, `Submodule.span_eq_top_iff_…`.
- Compactness / minimizer: `IsCompact.exists_isMinOn`, `Continuous.exists_forall_le`,
  continuity of `F` (sums of `log` of continuous positive functions).
- Determinant constraint slice: `Matrix.det`, `{S | S.PosDef ∧ S.det = 1}`.
- Invertible map / GL: `LinearEquiv`, `Matrix.GeneralLinearGroup`, or
  `Matrix.PosDef.toLinearEquiv`-style.

**The crux** (not in Mathlib) is step 3 — the first-order optimality of `F` on the
`det = 1` manifold. Two formalization options:
- (a) Lagrange multipliers via `gradient`/`fderiv` of `F` and of `log det`, using
  `IsLocalMin.fderiv_eq_zero`-style on the constraint surface (hard: manifold
  optimality).
- (b) **Variational / scaling argument** avoiding manifolds: perturb `S⋆ → S⋆ + tΔ`
  for traceless directions `Δ` and use `IsMinOn` directly with the directional
  derivative `≥ 0` both ways ⇒ `= 0`. This avoids charts and is likely the cleaner
  Lean route.

## Wiring back to Forster (the easy part, once the corrected lemma exists)
Given a realization `R` whose rows `R.u` span `ℝ^d`, apply the lemma to `v := R.u`,
obtaining invertible `T`. Define
```
R'.u i = (T (R.u i)) / ‖T (R.u i)‖
R'.w j = ((Tᵀ)⁻¹ (R.w j)) / ‖(Tᵀ)⁻¹ (R.w j)‖
```
- `sign_ok`: `⟪T uᵢ, (Tᵀ)⁻¹ wⱼ⟫ = ⟪uᵢ, wⱼ⟫` **exactly** (since `(T uᵢ)ᵀ (Tᵀ)⁻¹ wⱼ =
  uᵢᵀ Tᵀ (Tᵀ)⁻¹ wⱼ = uᵢᵀ wⱼ`); normalization multiplies by a positive scalar, so the
  sign — hence `sgn (M i j) · ⟪·,·⟫ > 0` — is preserved.
- `u_unit`, `w_unit`: by construction (normalized).
- `IsTightFrame R'`: directly from the lemma's conclusion.

## Spanning caveat (now formalized as a counterexample)
Same-ambient isotropy in `ℝ^d` requires the `R.u` to **span** `ℝ^d` (else
`∑ ûᵢûᵢᵀ` is singular, never `(m/d)I`). This is no longer just a caveat:
`not_isotropicKernel_as_stated` proves the current over-strong kernel false.
Two clean fixes remain:
- **Strengthen** `IsotropicKernel` (and `forster_of_kernel`) to take a spanning
  hypothesis on `R.u`; the Forster bound is applied at the sign-rank-achieving
  dimension where the vectors span, so this loses nothing. **Recommended.**
- Or add a dimension-reduction step (restrict to `span (R.u)`, prove the bound there,
  note `d ≥ dim span`). More work; not needed for the lower bound.

## Honest difficulty
Research-grade. Steps 1–2 (potential, coercivity, minimizer) are a real but standard
analysis formalization. Step 3 (first-order optimality, option (b) variational) is
the genuine crux and the largest risk. Step 4 (matrix sqrt substitution) and the
wiring are mechanical. Estimate: a multi-session project; the variational optimality
lemma is the piece to attack first and de-risk.
