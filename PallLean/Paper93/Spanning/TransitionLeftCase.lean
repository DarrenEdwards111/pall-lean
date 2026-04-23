/-
  PallLean/Paper93/Spanning/TransitionLeftCase.lean

  Paper §9 Lemma 31 (spanning layer, transitionLeft case) — Agent G3 of 10.

  ## Scope

  For the `transitionLeft` case of the concrete Cook-Levin factor list
  `cookLevinFactorList M n hn htb hns`, we prove that the per-factor
  Paper §9 "transitionLeft factor polynomial" lies in the ambient
  interface space

      PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4 σ

  for a suitable coordinate embedding `σ : Fin 4 ↪ Fin n`, for every
  choice of `(q, i, j)` parameterising the transitionLeft factor.

  Per Agent A (`PallLean.Paper93.CookLevinWSigma`) the transitionLeft
  template is

      transitionTemplate := X (0 : Fin 4) : MvPolynomial (Fin 4) ℚ

  (paper §9 Lemma 31 "W_σ in the compiled coefficient basis" form). The
  "transitionLeft factor polynomial" at the ambient Fin n level is
  therefore the rename of `transitionTemplate` along σ, i.e. the single
  ambient variable `X (σ 0) : MvPolynomial (Fin n) ℚ`.

  Agent F2's `Bridge.AmbientInterfaceSpace` (commit-level dependency)
  defines

      ambientInterfaceSpace n _hn σ :=
        realInterfaceSpace.map (rename σ.toFun).toLinearMap

  so membership reduces to:

    1. `transitionTemplate ∈ realInterfaceSpace` — Agent A's
       `transitionTemplate_mem_realInterfaceSpace`, and
    2. `rename σ.toFun transitionTemplate` is the image of
       `transitionTemplate` under `(rename σ.toFun).toLinearMap`, which
       by `Submodule.mem_map` is in `realInterfaceSpace.map …`.

  ## Note on `n ≥ 4`

  The task's source theorem signature mentions `hn : n ≥ 2` with an
  apparently-magical `(by omega)` coercion to `n ≥ 4`. An injective
  embedding `Fin 4 ↪ Fin n` literally requires `n ≥ 4`, so the
  existential is *false* at `n = 2, 3` (the witness `σ` cannot exist).
  We therefore include `hn4 : n ≥ 4` as an explicit extra hypothesis,
  which makes the existential well-posed and the `omega` call sound.
  This matches Agent F1's `Bridge.EmbedPerType` convention and Agent F2's
  `Bridge.AmbientInterfaceSpace` precondition.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Bridge.AmbientInterfaceSpace
import PallLean.WithinProfileBound

namespace PallLean.Paper93.Spanning

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Bridge
open TuringMachine
open SymmetricPowerBound

/-! ## The transitionLeft factor polynomial at ambient arity

We expose, at the ambient `MvPolynomial (Fin n) ℚ` level, the rename of
Agent A's `transitionTemplate` (= `X 0 : MvPolynomial (Fin 4) ℚ`) along
an embedding `σ : Fin 4 ↪ Fin n`. This is the "transitionLeft factor
polynomial" in the paper §9 Lemma 31 compiled-basis sense: a single
ambient variable `X (σ 0)`. -/

/-- **Transition-left ambient factor polynomial** at an embedding `σ`.

Per Agent A the local-coordinate template for `transitionLeft` is
`transitionTemplate = X 0 : MvPolynomial (Fin 4) ℚ`. Renaming along
`σ : Fin 4 ↪ Fin n` gives its ambient form on `Fin n`. -/
noncomputable def transitionLeftAmbientFactor
    {n : ℕ} (σ : Fin 4 ↪ Fin n) : MvPolynomial (Fin n) ℚ :=
  MvPolynomial.rename (σ : Fin 4 → Fin n) transitionTemplate

/-- The ambient factor equals `X (σ 0)`. -/
theorem transitionLeftAmbientFactor_eq_X
    {n : ℕ} (σ : Fin 4 ↪ Fin n) :
    transitionLeftAmbientFactor σ
      = (MvPolynomial.X (σ (0 : Fin 4)) : MvPolynomial (Fin n) ℚ) := by
  unfold transitionLeftAmbientFactor transitionTemplate
  -- `rename f (X k) = X (f k)` (a `simp` lemma in mathlib).
  simp [wSigmaArity]

/-! ## Membership in the ambient interface space

The core containment: Agent A's `transitionTemplate` is in
`realInterfaceSpace`, and `ambientInterfaceSpace n hn4 σ` is its image
under `(rename σ.toFun).toLinearMap`. By `Submodule.mem_map`, the rename
of any element of `realInterfaceSpace` lands in `ambientInterfaceSpace`.
-/

/-- The ambient transitionLeft factor is in the ambient interface space. -/
theorem transitionLeftAmbientFactor_mem_ambient
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    transitionLeftAmbientFactor σ ∈ ambientInterfaceSpace n hn4 σ := by
  classical
  -- Unfold the ambient W_σ to its definition as `realInterfaceSpace.map`
  -- along the rename linear map.
  unfold ambientInterfaceSpace transitionLeftAmbientFactor
  -- Membership in `Submodule.map L W` is: ∃ x ∈ W, L x = target.
  refine Submodule.mem_map.mpr ?_
  refine ⟨transitionTemplate, ?_, ?_⟩
  · -- `transitionTemplate ∈ realInterfaceSpace`  — Agent A.
    exact transitionTemplate_mem_realInterfaceSpace
  · -- The image under `(rename σ.toFun).toLinearMap` is the renamed
    -- polynomial itself by definition of the algebra-hom → linear-map
    -- underlying function.
    rfl

/-! ## The task theorem: existential form

The task's signature asks for an existential witness `σ` satisfying the
ambient-space membership for any `(q, i, j)`. Since Agent A's template
does not actually use `(q, i, j)` (the local template depends only on
`ConstraintType`, not on the per-instance parameters), the witness is
uniform in `(q, i, j)`: we use the canonical `Fin.castLEEmb` embedding
coming from `hn4 : n ≥ 4`. The membership then reduces to
`transitionLeftAmbientFactor_mem_ambient`.
-/

/-- **Agent G3 main theorem** (spanning layer, `transitionLeft` case).

For every transitionLeft factor instance `(q, i, j)` of the Cook-Levin
compiled factor list, there exists an embedding `σ : Fin 4 ↪ Fin n`
such that the transitionLeft factor polynomial (Agent A's template,
renamed along σ) lies in the ambient interface space
`PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4 σ`.

The embedding is the canonical `Fin.castLEEmb hn4` (uniform in
`(q, i, j)`, matching Agent F1's `Bridge.EmbedPerType`). The membership
holds by `Submodule.mem_map` applied to Agent A's
`transitionTemplate_mem_realInterfaceSpace`.

*Note on the `n ≥ 4` hypothesis.* An injective `Fin 4 ↪ Fin n` requires
`n ≥ 4`, so the existential is only well-posed in that regime; we
therefore include `hn4 : n ≥ 4` as an additional hypothesis beyond the
task source's `hn : n ≥ 2`. This matches Agent F1/F2's bridge-layer
convention. The original `hn : n ≥ 2` is kept in the signature for
signature compatibility with the task spec. -/
theorem transitionLeft_factor_mem_ambient
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (q : Fin M.numStates) (i : Fin n) (j : Fin n) :
    ∃ σ : Fin 4 ↪ Fin n,
      transitionLeftAmbientFactor σ ∈
        PallLean.Paper93.Bridge.ambientInterfaceSpace n (by omega) σ := by
  -- Silence unused-binder warnings: `M, hn, htb, hns, q, i, j` are
  -- part of the task's signature but the canonical embedding does not
  -- use them at this layer (Agent F1 convention).
  let _ := M; let _ := hn; let _ := htb; let _ := hns
  let _ := q; let _ := i; let _ := j
  refine ⟨Fin.castLEEmb hn4, ?_⟩
  exact transitionLeftAmbientFactor_mem_ambient n hn4 (Fin.castLEEmb hn4)

/-! ## Auxiliary: type-signature variant

A direct restatement in terms of `typeSignaturePolynomial
ConstraintType.transitionLeft` (which is definitionally
`transitionTemplate`), useful to callers who index by `ConstraintType`
rather than by per-instance parameters. -/

/-- The ambient form of `typeSignaturePolynomial ConstraintType.transitionLeft`
(i.e. Agent A's type-signature polynomial for the transitionLeft type)
lies in `ambientInterfaceSpace n hn4 σ` for any `σ`. -/
theorem typeSignaturePolynomial_transitionLeft_ambient_mem
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    MvPolynomial.rename (σ : Fin 4 → Fin n)
        (typeSignaturePolynomial ConstraintType.transitionLeft) ∈
      ambientInterfaceSpace n hn4 σ := by
  classical
  -- `typeSignaturePolynomial transitionLeft = transitionTemplate` by
  -- definition; reduce to `transitionLeftAmbientFactor_mem_ambient`.
  have h := transitionLeftAmbientFactor_mem_ambient n hn4 σ
  simpa [transitionLeftAmbientFactor, typeSignaturePolynomial] using h

end PallLean.Paper93.Spanning
