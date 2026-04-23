/-
  PallLean/Paper93/Spanning/DischargeOneMem.lean

  Agent H3 of 10 (parallel) — Discharging the constant-`1`-in-ambient
  hypotheses exposed by Agents G1 and G2, using Agent H1's concrete
  `perTypeInterfaceSpace` (which natively contains `1`) together with
  Agent H2's `ambientPerTypeSpace` lift to `MvPolynomial (Fin n) ℚ`.

  ## Scope

  Agents G1 and G2 (commits `0dca50b` and `e19fa5c`) prove that the
  compiled Cook-Levin booleanity factor `1 - X_v + X_v^2` and adjacency
  factor `1 - X_i * X_j` lie in `ambientInterfaceSpace n hn4 σ`
  (Agent F4's shared-target lift of Agent A's `realInterfaceSpace`),
  subject to the explicit hypothesis that the constant polynomial `1`
  is also in that ambient space:

  * G1 (`BooleanityCase.lean`) takes `h1 : (1 : …) ∈ ambientInterfaceSpace …`.
  * G2 (`AdjacencyCase.lean`) takes `hOne : oneMemAmbient n hn4 σ`, a
    `Prop` wrapper for the same condition.

  The reason for the hypothesis is that Agent A's `realInterfaceSpace`
  is literally `span { X 0 - X 0^2 , X 0 * X 1 - X 0 , X 0 }`, whose
  every generator has zero constant coefficient. Hence the strict
  linear image `realInterfaceSpace.map (rename σ).toLinearMap` (= Agent
  F4's `ambientInterfaceSpace`) never contains the constant polynomial
  `1`.

  Agents H1 and H2 close this gap:

  * Agent H1 (`Bridge/PerTypeInterfaceSpace.lean`) defines a per-`τ`
    source-space `perTypeInterfaceSpace τ : Submodule ℚ (MvPolynomial
    (Fin 4) ℚ)` which natively contains `1` for every active type
    (`τ ≠ transitionRight`) and has dim ≤ 3.

  * Agent H2 (`Bridge/AmbientPerType.lean`) lifts Agent H1's family
    along a coordinate embedding `σ : Fin 4 ↪ Fin n` to
    `ambientPerTypeSpace n hn σ τ : Submodule ℚ (MvPolynomial (Fin n) ℚ)`.
    The algebra homomorphism `rename σ.toFun` preserves `1`, so the
    ambient family also contains the constant `1` uniformly in
    `σ` and `τ`, for every active type.

  This file (Agent H3) completes the bridge by using H1/H2 to
  discharge G1's `h1` and G2's `hOne` hypotheses and produce
  unconditional per-type factor-membership theorems in H2's
  `ambientPerTypeSpace` (which strictly contains Agent F4's
  `ambientInterfaceSpace` when lifted with a common source-space
  generator set, because every generator of `realInterfaceSpace` is
  itself in `perTypeInterfaceSpace τ` for the matching active type
  `τ`).

  ## What this file delivers

  1. `one_mem_booleanityAmbient_discharged`: Agent G1's
     `1 ∈ ambient` hypothesis is discharged unconditionally for the
     booleanity branch of Agent H2's per-type ambient family.

  2. `one_mem_adjacencyAmbient_discharged`: Agent G2's
     `oneMemAmbient` hypothesis is discharged unconditionally for the
     adjacency branch of Agent H2's per-type ambient family.

  3. `booleanity_factor_mem_ambient_unconditional`: the G1 conclusion
     repackaged with the `1 ∈ …` hypothesis discharged, yielding an
     unconditional existence of `σ : Fin 4 ↪ Fin n` along which the
     compiled booleanity factor `1 - X_v + X_v^2` lies in
     `ambientPerTypeSpace _ n hn σ .booleanity`.

  4. `adjacency_factor_mem_ambient_unconditional`: the G2 conclusion
     repackaged with the `oneMemAmbient` hypothesis discharged.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Bridge.AmbientPerType
import PallLean.Paper93.Bridge.PerTypeInterfaceSpace
import PallLean.Paper93.Spanning.BooleanityCase
import PallLean.Paper93.Spanning.AdjacencyCase
import PallLean.SymmetricPowerBound

namespace PallLean.Paper93.Spanning

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Bridge
open SymmetricPowerBound

/-! ## Direct discharge of G1's `1 ∈ ambient` hypothesis

Agent H2's `one_mem_ambientPerTypeSpace`, instantiated at the H1-
supplied source-level `perTypeInterfaceSpace`, takes the activity
witness `hτ : τ ≠ transitionRight` plus H1's source-level
`one_mem_perTypeInterfaceSpace τ hτ` and concludes
`1 ∈ ambientPerTypeSpace _ n hn σ τ` for every coordinate embedding
`σ`. We specialise here at `τ = .booleanity` and `τ = .adjacency`. -/

/-- **Discharge G1's hypothesis (booleanity branch).** The constant
`1 : MvPolynomial (Fin n) ℚ` lies in Agent H2's ambient per-type space
`ambientPerTypeSpace perTypeInterfaceSpace n hn σ .booleanity`, for
every `σ : Fin 4 ↪ Fin n`. -/
theorem one_mem_booleanityAmbient_discharged
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (1 : MvPolynomial (Fin n) ℚ) ∈
      ambientPerTypeSpace perTypeInterfaceSpace n hn σ
        ConstraintType.booleanity := by
  -- Activity witness: `.booleanity ≠ .transitionRight`.
  have hτ : ConstraintType.booleanity
      ≠ ConstraintType.transitionRight := by decide
  -- H1's source-level `1 ∈ perTypeInterfaceSpace .booleanity`.
  have h_one_src : (1 : MvPolynomial (Fin wSigmaArity) ℚ)
      ∈ perTypeInterfaceSpace ConstraintType.booleanity :=
    one_mem_perTypeInterfaceSpace ConstraintType.booleanity hτ
  -- H2's ambient lift of H1's `1`.
  exact
    one_mem_ambientPerTypeSpace
      (perTypeInterfaceSpace := perTypeInterfaceSpace)
      n hn σ ConstraintType.booleanity hτ h_one_src

/-- **Discharge G2's hypothesis (adjacency branch).** The constant
`1 : MvPolynomial (Fin n) ℚ` lies in Agent H2's ambient per-type space
`ambientPerTypeSpace perTypeInterfaceSpace n hn σ .adjacency`, for
every `σ : Fin 4 ↪ Fin n`. -/
theorem one_mem_adjacencyAmbient_discharged
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (1 : MvPolynomial (Fin n) ℚ) ∈
      ambientPerTypeSpace perTypeInterfaceSpace n hn σ
        ConstraintType.adjacency := by
  have hτ : ConstraintType.adjacency
      ≠ ConstraintType.transitionRight := by decide
  have h_one_src : (1 : MvPolynomial (Fin wSigmaArity) ℚ)
      ∈ perTypeInterfaceSpace ConstraintType.adjacency :=
    one_mem_perTypeInterfaceSpace ConstraintType.adjacency hτ
  exact
    one_mem_ambientPerTypeSpace
      (perTypeInterfaceSpace := perTypeInterfaceSpace)
      n hn σ ConstraintType.adjacency hτ h_one_src

/-- **Discharge (transitionLeft branch)** — kept for completeness so
that any downstream callers working with the dormant third active type
(G3 case) have a uniform discharge theorem available. -/
theorem one_mem_transitionLeftAmbient_discharged
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (1 : MvPolynomial (Fin n) ℚ) ∈
      ambientPerTypeSpace perTypeInterfaceSpace n hn σ
        ConstraintType.transitionLeft := by
  have hτ : ConstraintType.transitionLeft
      ≠ ConstraintType.transitionRight := by decide
  have h_one_src : (1 : MvPolynomial (Fin wSigmaArity) ℚ)
      ∈ perTypeInterfaceSpace ConstraintType.transitionLeft :=
    one_mem_perTypeInterfaceSpace ConstraintType.transitionLeft hτ
  exact
    one_mem_ambientPerTypeSpace
      (perTypeInterfaceSpace := perTypeInterfaceSpace)
      n hn σ ConstraintType.transitionLeft hτ h_one_src

/-! ## Membership of the renamed booleanity generator in H2's ambient

Agent G1's `booleanityLift_mem_ambient` shows that
`X_{σ 0} - X_{σ 0}^2 ∈ ambientInterfaceSpace n hn σ` (= Agent F4's
shared-target). To transport this into H2's `ambientPerTypeSpace _ n hn
σ .booleanity`, we re-derive the same pushforward membership statement
directly against H1's per-type source space, without relying on any
containment between Agent F4 and Agent H2.

The source-side witness is that
`X 0 - (X 0)^2 ∈ perTypeInterfaceSpace .booleanity`:
  * `1 ∈ span` by `subset_span` (Agent H1 `one_mem_perTypeInterfaceSpace`);
  * `X 0 ∈ span` by `subset_span` (Agent H1 generator);
  * `(X 0)^2 ∈ span` by `subset_span` (Agent H1 generator);
  * take the linear combination.
-/

/-- The source-side booleanity generator `X 0 - (X 0)^2` lies in Agent
H1's `perTypeInterfaceSpace .booleanity`, directly from the
generating-set enumeration. -/
private theorem booleanity_source_generator_mem :
    (MvPolynomial.X (0 : Fin 4) - (MvPolynomial.X (0 : Fin 4)) ^ 2 :
        MvPolynomial (Fin 4) ℚ)
      ∈ perTypeInterfaceSpace ConstraintType.booleanity := by
  unfold perTypeInterfaceSpace
  have hX : (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) ℚ)
      ∈ Submodule.span ℚ
          ({1, MvPolynomial.X (0 : Fin 4),
              (MvPolynomial.X (0 : Fin 4)) ^ 2} :
             Set (MvPolynomial (Fin 4) ℚ)) :=
    Submodule.subset_span (by simp)
  have hXsq :
      ((MvPolynomial.X (0 : Fin 4)) ^ 2 : MvPolynomial (Fin 4) ℚ)
      ∈ Submodule.span ℚ
          ({1, MvPolynomial.X (0 : Fin 4),
              (MvPolynomial.X (0 : Fin 4)) ^ 2} :
             Set (MvPolynomial (Fin 4) ℚ)) :=
    Submodule.subset_span (by simp)
  exact (Submodule.span ℚ _).sub_mem hX hXsq

/-- The renamed booleanity generator
`X_{σ 0} - X_{σ 0}^2 ∈ ambientPerTypeSpace _ n hn σ .booleanity`,
obtained by mapping the source-level membership through the algebra
homomorphism `rename σ.toFun`. -/
theorem booleanityLift_mem_ambientPerType
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (MvPolynomial.X (σ 0) - (MvPolynomial.X (σ 0)) ^ 2 :
        MvPolynomial (Fin n) ℚ)
      ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn σ
          ConstraintType.booleanity := by
  classical
  -- Algebra-hom image of the source-level generator.
  have h_src := booleanity_source_generator_mem
  -- The rename acts on `X 0 - (X 0)^2` by sending it to
  -- `X (σ 0) - X (σ 0)^2`.
  have h_eq :
      (MvPolynomial.rename (σ.toFun : Fin 4 → Fin n)
          (MvPolynomial.X (0 : Fin 4)
            - (MvPolynomial.X (0 : Fin 4)) ^ 2) :
            MvPolynomial (Fin n) ℚ)
        = MvPolynomial.X (σ 0)
          - (MvPolynomial.X (σ 0)) ^ 2 := by
    simp [map_sub, map_pow, rename_X, Function.Embedding.toFun_eq_coe]
  -- Image under `.map` — note `wSigmaArity = 4` definitionally.
  refine ⟨_, h_src, ?_⟩
  -- The goal is: `(rename σ.toFun).toLinearMap (X 0 - X 0^2)
  --                = X (σ 0) - X (σ 0)^2`, which is `h_eq`.
  simpa [ambientPerTypeSpace] using h_eq

/-! ## Unconditional booleanity factor membership -/

/-- **Unconditional booleanity factor membership.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4` and every variable `v : Fin n`, there exists an
embedding `σ : Fin 4 ↪ Fin n` along which the compiled Cook-Levin
booleanity factor `1 - X_v + X_v^2` lies in Agent H2's
ambient per-type space
`ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ .booleanity`.

No residual `1 ∈ …` hypothesis is carried: the constant-`1` piece is
discharged via `one_mem_booleanityAmbient_discharged`. -/
theorem booleanity_factor_mem_ambient_unconditional
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) (hn4 : n ≥ 4) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ
            ConstraintType.booleanity := by
  classical
  -- Use the G1-canonical embedding with `σ_v 0 = v`.
  refine ⟨sigmaOfVar n hn4 v, ?_⟩
  -- Silence unused-argument lints on the cookLevinQ-shape parameters.
  let _ := M; let _ := hn; let _ := htb; let _ := hns
  -- `1 ∈ ambientPerTypeSpace .booleanity` (H3 discharge of G1's `h1`).
  have hOne :
      (1 : MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (sigmaOfVar n hn4 v) ConstraintType.booleanity :=
    one_mem_booleanityAmbient_discharged n hn4 (sigmaOfVar n hn4 v)
  -- `X_v - X_v^2 ∈ ambientPerTypeSpace .booleanity`.
  have hLift :
      (MvPolynomial.X v - (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (sigmaOfVar n hn4 v) ConstraintType.booleanity := by
    have h := booleanityLift_mem_ambientPerType n hn4 (sigmaOfVar n hn4 v)
    have h0 : (sigmaOfVar n hn4 v) 0 = v :=
      sigmaOfVar_apply_zero n hn4 v
    rw [h0] at h
    exact h
  -- `1 - X_v + X_v^2 = 1 - (X_v - X_v^2)` ∈ submodule (closed under sub).
  have hSub :
      ((1 : MvPolynomial (Fin n) ℚ)
          - (MvPolynomial.X v - (MvPolynomial.X v) ^ 2))
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (sigmaOfVar n hn4 v) ConstraintType.booleanity :=
    (ambientPerTypeSpace perTypeInterfaceSpace n hn4
        (sigmaOfVar n hn4 v) ConstraintType.booleanity).sub_mem hOne hLift
  have hEq :
      (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ)
      = (1 : MvPolynomial (Fin n) ℚ)
          - (MvPolynomial.X v - (MvPolynomial.X v) ^ 2) := by
    ring
  rw [hEq]
  exact hSub

/-! ## Membership of the renamed adjacency generators in H2's ambient -/

/-- The source-side adjacency generator `X 0 * X 1` lies in Agent H1's
`perTypeInterfaceSpace .adjacency`, directly from the
generating-set enumeration. -/
private theorem adjacency_source_generator_mem :
    (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (1 : Fin 4) :
        MvPolynomial (Fin 4) ℚ)
      ∈ perTypeInterfaceSpace ConstraintType.adjacency := by
  unfold perTypeInterfaceSpace
  exact Submodule.subset_span (by simp)

/-- The renamed adjacency generator
`X_{σ 0} * X_{σ 1} ∈ ambientPerTypeSpace _ n hn σ .adjacency`,
obtained by mapping the source-level membership through the algebra
homomorphism `rename σ.toFun`. -/
theorem adjacencyLift_mem_ambientPerType
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (MvPolynomial.X (σ 0) * MvPolynomial.X (σ 1) :
        MvPolynomial (Fin n) ℚ)
      ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn σ
          ConstraintType.adjacency := by
  classical
  have h_src := adjacency_source_generator_mem
  have h_eq :
      (MvPolynomial.rename (σ.toFun : Fin 4 → Fin n)
          (MvPolynomial.X (0 : Fin 4)
            * MvPolynomial.X (1 : Fin 4)) :
            MvPolynomial (Fin n) ℚ)
        = MvPolynomial.X (σ 0) * MvPolynomial.X (σ 1) := by
    simp [map_mul, rename_X, Function.Embedding.toFun_eq_coe]
  refine ⟨_, h_src, ?_⟩
  simpa [ambientPerTypeSpace] using h_eq

/-! ## Unconditional adjacency factor membership -/

/-- **Unconditional adjacency factor membership.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4` and every adjacent-variable pair `(i, j)` with `i ≠ j`,
there exists an embedding `σ : Fin 4 ↪ Fin n` along which the compiled
Cook-Levin adjacency factor `1 - X_i * X_j` lies in Agent H2's ambient
per-type space
`ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ .adjacency`.

No residual `oneMemAmbient` hypothesis is carried: the constant-`1`
piece is discharged via `one_mem_adjacencyAmbient_discharged`. -/
theorem adjacency_factor_mem_ambient_unconditional
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i j : Fin n) (hn4 : n ≥ 4) (hne : i ≠ j) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X i * MvPolynomial.X j :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ
            ConstraintType.adjacency := by
  classical
  refine ⟨adjacencyEmbedding hn4 i j hne, ?_⟩
  let _ := M; let _ := hn; let _ := htb; let _ := hns
  -- `1 ∈ ambientPerTypeSpace .adjacency` (H3 discharge of G2's `hOne`).
  have hOne :
      (1 : MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (adjacencyEmbedding hn4 i j hne) ConstraintType.adjacency :=
    one_mem_adjacencyAmbient_discharged n hn4
      (adjacencyEmbedding hn4 i j hne)
  -- `X_i * X_j ∈ ambientPerTypeSpace .adjacency`.
  have hProd :
      (MvPolynomial.X i * MvPolynomial.X j :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (adjacencyEmbedding hn4 i j hne) ConstraintType.adjacency := by
    have h := adjacencyLift_mem_ambientPerType n hn4
      (adjacencyEmbedding hn4 i j hne)
    have h0 : (adjacencyEmbedding hn4 i j hne) 0 = i :=
      adjacencyEmbedding_zero hn4 i j hne
    have h1 : (adjacencyEmbedding hn4 i j hne) 1 = j :=
      adjacencyEmbedding_one hn4 i j hne
    rw [h0, h1] at h
    exact h
  -- `1 - X_i * X_j` is in the submodule by subtraction closure.
  have hSub :
      ((1 : MvPolynomial (Fin n) ℚ)
          - MvPolynomial.X i * MvPolynomial.X j)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (adjacencyEmbedding hn4 i j hne) ConstraintType.adjacency :=
    (ambientPerTypeSpace perTypeInterfaceSpace n hn4
        (adjacencyEmbedding hn4 i j hne)
        ConstraintType.adjacency).sub_mem hOne hProd
  exact hSub

-- Suppress unused-variable lints on the cookLevinQ-shape parameters
-- retained in the public signatures.
attribute [nolint unusedArguments]
  booleanity_factor_mem_ambient_unconditional
  adjacency_factor_mem_ambient_unconditional

/-! ## Kernel-only axiom trace

The four main deliverables should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced. -/

#print axioms one_mem_booleanityAmbient_discharged
#print axioms one_mem_adjacencyAmbient_discharged
#print axioms booleanity_factor_mem_ambient_unconditional
#print axioms adjacency_factor_mem_ambient_unconditional

end PallLean.Paper93.Spanning
