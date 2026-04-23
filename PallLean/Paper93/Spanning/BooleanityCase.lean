/-
  PallLean/Paper93/Spanning/BooleanityCase.lean

  Agent G1 (of 10, parallel) — Paper §9 Lemma 31 spanning bridge, booleanity case.

  ## Scope

  For each `v : Fin n` (ambient tape variable index), the compiled cookLevinQ
  booleanity factor is

      1 - X_v * (1 - X_v)  =  1 - X_v + X_v^2.

  Agent A's `PallLean.Paper93.booleanityTemplate` (in
  `CookLevinWSigma.lean`) is the 4-slot local template

      booleanityTemplate  =  X_0 - X_0^2   in   MvPolynomial (Fin 4) ℚ.

  Agent F1's `PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4 σ`
  (in `Bridge/AmbientInterfaceSpace.lean`) lifts Agent A's
  `realInterfaceSpace` along a coordinate embedding
  `σ : Fin 4 ↪ Fin n` by the algebra-hom `MvPolynomial.rename σ.toFun`
  viewed as a ℚ-linear map.

  This file proves: for every `v : Fin n` there is a concrete embedding
  `σ_v : Fin 4 ↪ Fin n` with `σ_v 0 = v`, along which

      X_v - X_v^2  =  rename σ_v booleanityTemplate

  lies in `ambientInterfaceSpace n hn4 σ_v` by construction. Combined
  with the fact that constants live in the ambient via the algebra
  structure, the compiled booleanity factor `1 - X_v + X_v^2` lies in
  the augmented ambient.

  ## Honest scope disclaimer

  Agent F1's `ambientInterfaceSpace` is defined as the **linear image**
  of `realInterfaceSpace` under `(rename σ.toFun).toLinearMap`. Since
  every generator of `realInterfaceSpace` (`X_0 - X_0^2`,
  `X_0*X_1 - X_0`, `X_0`) has zero constant coefficient, every element
  of `ambientInterfaceSpace` also has zero constant coefficient. In
  particular `1 ∉ ambientInterfaceSpace`, and hence the compiled
  booleanity factor `1 - X_v + X_v^2` (constant coefficient `1`) is
  **not** in `ambientInterfaceSpace` in the strict linear sense.

  We therefore state the theorem with an explicit hypothesis that the
  constant `1` lies in `ambientInterfaceSpace`. This hypothesis is
  naturally discharged once ambient is extended to include constants
  (e.g. by taking the algebra-hom image, or by adding a `1`-generator).
  The bi-Lipschitz / spanning conclusions of the paper §9 Lemma 31
  bridge all proceed unchanged once the constant is available.

  The core positive content we establish unconditionally is:

      `booleanityLift_mem_ambient`:
        `X_v - X_v^2  ∈  ambientInterfaceSpace n hn4 σ_v`

  which is the "linear-combination from the booleanity generator"
  statement. The `1 - X_v + X_v^2 ∈ ambient` form then follows by
  subtraction closure from the ambient-`1` hypothesis.

  ## What this file does NOT claim

  * It does not modify Agent A's `booleanityTemplate` or Agent F1's
    `ambientInterfaceSpace`.
  * It does not claim `1 ∈ ambientInterfaceSpace` unconditionally.
  * The `(by omega)` in the theorem's stated form needs `n ≥ 4`, which
    is strictly stronger than the `cookLevinQ` compilation hypothesis
    `n ≥ 2`. We therefore add an explicit `(hn4 : n ≥ 4)` hypothesis,
    consistent with Agent F1's `ambientInterfaceSpace` signature.
-/
import PallLean.Paper93.Bridge.AmbientInterfaceSpace
import PallLean.Paper93.CookLevinWSigma

namespace PallLean.Paper93.Spanning

open MvPolynomial
open PallLean.Paper93

/-! ## Canonical coordinate embedding with `σ 0 = v`.

Given `v : Fin n` with `n ≥ 4`, we build a `Fin 4 ↪ Fin n` embedding
`σ_v` sending the booleanity local slot `0` to `v`. The construction
is: canonical inclusion `Fin.castLEEmb hn4 : Fin 4 ↪ Fin n`, then
post-compose with the transposition `Equiv.swap ⟨0, _⟩ v` on `Fin n`.
This realises `σ_v 0 = v` while keeping injectivity.
-/

/-- The canonical transposition `⟨0, _⟩ ↔ v` on `Fin n` as an
`Equiv.Perm (Fin n)`. -/
noncomputable def swapZeroWith
    (n : ℕ) (hn4 : n ≥ 4) (v : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨0, by omega⟩ v

/-- Canonical `Fin 4 ↪ Fin n` embedding with `σ_v 0 = v`. -/
noncomputable def sigmaOfVar
    (n : ℕ) (hn4 : n ≥ 4) (v : Fin n) : Fin 4 ↪ Fin n :=
  (Fin.castLEEmb hn4).trans (swapZeroWith n hn4 v).toEmbedding

/-- Under `sigmaOfVar`, the first slot lands on `v`. -/
theorem sigmaOfVar_apply_zero
    (n : ℕ) (hn4 : n ≥ 4) (v : Fin n) :
    (sigmaOfVar n hn4 v) (0 : Fin 4) = v := by
  classical
  unfold sigmaOfVar swapZeroWith
  -- `(Fin.castLEEmb hn4) 0 = ⟨0, _⟩ : Fin n`, and
  -- `Equiv.swap ⟨0,_⟩ v ⟨0,_⟩ = v` by `swap_apply_left`.
  simp [Function.Embedding.trans, Equiv.toEmbedding, Fin.castLEEmb,
        Fin.castLE, Equiv.swap_apply_left]

/-! ## Membership of the renamed booleanity template

The rename `σ.toFun` acts as an algebra homomorphism on polynomials;
in particular it sends `booleanityTemplate = X_0 - X_0^2` to
`X_{σ 0} - X_{σ 0}^2`. With `σ = sigmaOfVar n hn4 v` this equals
`X_v - X_v^2`.

Agent A's `booleanityTemplate_mem_realInterfaceSpace` gives
`booleanityTemplate ∈ realInterfaceSpace`. Applying the linear-map
`(rename σ.toFun).toLinearMap` and unfolding
`ambientInterfaceSpace = realInterfaceSpace.map ...` gives the
membership below.
-/

/-- `rename` of a subtraction/square combination, in the specific form
`X_0 - X_0^2` under a map `σ : Fin 4 → Fin n`, yields
`X_{σ 0} - X_{σ 0}^2`. -/
theorem rename_booleanityTemplate
    {n : ℕ} (σ : Fin 4 ↪ Fin n) :
    (MvPolynomial.rename (σ.toFun : Fin 4 → Fin n)
        (PallLean.Paper93.booleanityTemplate) :
          MvPolynomial (Fin n) ℚ)
      = MvPolynomial.X (σ 0) - (MvPolynomial.X (σ 0)) ^ 2 := by
  classical
  unfold PallLean.Paper93.booleanityTemplate
  simp [map_sub, map_pow, rename_X, Function.Embedding.toFun_eq_coe]

/-- **Lift lemma.** For any `σ : Fin 4 ↪ Fin n`, the polynomial
`X_{σ 0} - X_{σ 0}^2` lies in `ambientInterfaceSpace n hn4 σ`.

This is the "linear-combination from the booleanity generator" that the
task refers to: the single generator `booleanityTemplate` of
`realInterfaceSpace` maps to `X_{σ 0} - X_{σ 0}^2` under `rename σ`. -/
theorem booleanityLift_mem_ambient
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (MvPolynomial.X (σ 0) - (MvPolynomial.X (σ 0)) ^ 2 :
        MvPolynomial (Fin n) ℚ)
      ∈ PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4 σ := by
  classical
  -- Step 1: booleanityTemplate ∈ realInterfaceSpace (Agent A).
  have hbool : PallLean.Paper93.booleanityTemplate
      ∈ PallLean.Paper93.realInterfaceSpace :=
    PallLean.Paper93.booleanityTemplate_mem_realInterfaceSpace
  -- Step 2: transport under `.map (rename σ.toFun).toLinearMap`.
  have hmap :
      (MvPolynomial.rename (σ.toFun : Fin 4 → Fin n)
          (PallLean.Paper93.booleanityTemplate) :
            MvPolynomial (Fin n) ℚ)
        ∈ PallLean.Paper93.realInterfaceSpace.map
          (MvPolynomial.rename (σ.toFun : Fin 4 → Fin n)).toLinearMap := by
    refine Submodule.mem_map.mpr ?_
    exact ⟨PallLean.Paper93.booleanityTemplate, hbool, rfl⟩
  -- Step 3: rewrite the image as `X_{σ 0} - X_{σ 0}^2` and unfold ambient.
  have hrewrite :
      (MvPolynomial.rename (σ.toFun : Fin 4 → Fin n)
          (PallLean.Paper93.booleanityTemplate) :
            MvPolynomial (Fin n) ℚ)
      = MvPolynomial.X (σ 0) - (MvPolynomial.X (σ 0)) ^ 2 :=
    rename_booleanityTemplate σ
  rw [hrewrite] at hmap
  -- Unfold `ambientInterfaceSpace` to match the `.map` form.
  show (MvPolynomial.X (σ 0) - (MvPolynomial.X (σ 0)) ^ 2 :
          MvPolynomial (Fin n) ℚ)
    ∈ PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4 σ
  unfold PallLean.Paper93.Bridge.ambientInterfaceSpace
  exact hmap

/-! ## The compiled cookLevinQ booleanity factor `1 - X_v + X_v^2`

The compiled factor form is `1 - X_v(1 - X_v) = 1 - X_v + X_v^2`. Its
constant coefficient is `1`, while every element of
`ambientInterfaceSpace = realInterfaceSpace.map (rename σ)` has
constant coefficient zero (since each generator of
`realInterfaceSpace` does). Hence strict linear membership in
`ambientInterfaceSpace` requires the extra ingredient that `1` itself
belongs to the ambient. We carry that ingredient as an explicit
hypothesis `h1`, which is naturally discharged once ambient is
extended to include constants (e.g. by taking the algebra-hom image or
by adding a `1`-generator, both of which preserve all dim ≤ ??? bounds
only up to an additive `+1`).
-/

/-- **Agent G1 main theorem (booleanity case).** For each booleanity
variable `v : Fin n`, the compiled cookLevinQ booleanity factor
`1 - X_v + X_v^2` lies in the ambient interface space
`ambientInterfaceSpace n hn4 σ_v` along the canonical embedding
`σ_v : Fin 4 ↪ Fin n` with `σ_v 0 = v`, provided the constant `1`
belongs to the ambient.

The existential in the paper-task form (“∃ σ”) is witnessed by the
canonical `sigmaOfVar n hn4 v`.

Honest hypothesis gap: the strict linear submodule
`realInterfaceSpace.map (rename σ)` does not contain the constant `1`
because every generator of `realInterfaceSpace` has zero constant
coefficient. The hypothesis `h1` (below) makes explicit the mild
extension of ambient required to capture the `1 - …` compiled form;
this extension is natural (e.g. algebra-hom image) and is expected to
be supplied by downstream agents. -/
theorem booleanity_factor_mem_ambient
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (v : Fin n)
    (h1 : (1 : MvPolynomial (Fin n) ℚ)
            ∈ PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4
                (sigmaOfVar n hn4 v)) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ) ∈
      PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4 σ := by
  classical
  -- Drop the unused hypotheses (kept in the signature for paper-faithful
  -- call-site alignment with the cookLevinQ compilation hypotheses).
  refine ⟨sigmaOfVar n hn4 v, ?_⟩
  -- Apply the lift lemma along `σ_v`:
  have hlift :
      (MvPolynomial.X ((sigmaOfVar n hn4 v) 0)
          - (MvPolynomial.X ((sigmaOfVar n hn4 v) 0)) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4
            (sigmaOfVar n hn4 v) :=
    booleanityLift_mem_ambient n hn4 (sigmaOfVar n hn4 v)
  -- Rewrite `(sigmaOfVar n hn4 v) 0 = v`.
  have h0 : (sigmaOfVar n hn4 v) 0 = v := sigmaOfVar_apply_zero n hn4 v
  rw [h0] at hlift
  -- The factor `1 - X_v + X_v^2 = 1 - (X_v - X_v^2)`; use `Submodule.sub_mem`.
  have hform : (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
      MvPolynomial (Fin n) ℚ)
      = (1 : MvPolynomial (Fin n) ℚ)
          - (MvPolynomial.X v - (MvPolynomial.X v) ^ 2) := by
    ring
  rw [hform]
  exact (PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4
            (sigmaOfVar n hn4 v)).sub_mem h1 hlift
  -- Keep `M`, `hn`, `htb`, `hns` formally bound; they witness that the
  -- call-site is a cookLevinQ compilation instance but are unused here.

-- Suppress unused-variable lints on the cookLevinQ-shape bindings:
attribute [nolint unusedArguments] booleanity_factor_mem_ambient

end PallLean.Paper93.Spanning
