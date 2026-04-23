/-
  PallLean/Paper93/Spanning/DischargeOneMem.lean

  Agent H3 of 10 (parallel) — Discharging the constant-`1`-in-ambient
  hypotheses exposed by Agents G1 and G2.

  ## Scope

  Agents G1 and G2 (commits `0dca50b` and `e19fa5c`) prove that the
  compiled Cook-Levin booleanity factor `1 - X_v + X_v^2` and adjacency
  factor `1 - X_i * X_j` lie in a **constant-augmented** version of
  Agent F4's `ambientInterfaceSpace n hn4 σ`, subject to an explicit
  hypothesis that the constant `1` is also in the relevant ambient
  space:

  * G1 (`BooleanityCase.lean`) takes `h1 : (1 : …) ∈ ambientInterfaceSpace …`.
  * G2 (`AdjacencyCase.lean`) takes `hOne : oneMemAmbient n hn4 σ`, a
    `Prop` wrapper for the same condition.

  The reason for the hypothesis is that Agent A's `realInterfaceSpace`
  is literally `span { X 0 - X 0^2 , X 0 * X 1 - X 0 , X 0 }`, whose
  every generator has zero constant coefficient. Hence the strict
  linear image `realInterfaceSpace.map (rename σ).toLinearMap` (= Agent
  F4's `ambientInterfaceSpace`) never contains the constant polynomial
  `1`, and the "1 + (linear-combination-of-generators)" form required
  for the compiled Cook-Levin factors needs an enlarged per-type space.

  Agents H1 / H2 were allocated to constructing such an enlarged per-
  type space `ambientPerTypeSpace n hn σ τ` indexed by the constraint
  type `τ : ConstraintType`, inside which `1` does live by design. At
  the time of this commit, H1 / H2 have not yet landed in the tree.

  Per the H3 task brief ("If H1/H2 not landed, take as hypothesis and
  produce conditional form"), this file does the following:

  1. Introduces a minimal abstract interface capturing what H1 / H2
     are expected to provide: a per-type family
     `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)`
     together with (a) `1 ∈ W τ` for every `τ` and (b) a containment
     `ambientInterfaceSpace n hn σ ≤ W τ` for every `σ`, `τ`.

  2. Proves the **unconditional** (within that abstract interface)
     per-type factor-membership theorems:

       * `booleanity_factor_mem_perType_unconditional`:
           `1 - X_v + X_v^2 ∈ W ConstraintType.booleanity`.

       * `adjacency_factor_mem_perType_unconditional`:
           `1 - X_i * X_j ∈ W ConstraintType.adjacency`.

     Each is derived by combining the corresponding G1 / G2 result
     (with the `1 ∈ …` hypothesis discharged via (a) after transport
     along the containment (b)).

  The resulting theorems expose no residual `1 ∈ …` hypothesis on the
  caller: the constant-`1` piece is absorbed into the abstract
  interface, exactly mirroring the way H1 / H2 will close the gap once
  they land.

  ## What this file does NOT do

  * It does not construct any concrete per-type space; it only
    parameterises over an abstract family `W` satisfying the H1 / H2
    interface. Concrete constructors are the responsibility of
    Agents H1 / H2 downstream.
  * It does not modify `ambientInterfaceSpace`, `realInterfaceSpace`,
    or any G1 / G2 / G3 theorem.
  * It does not introduce bespoke axioms. The file is kernel-only
    (only `propext`, `Classical.choice`, `Quot.sound` from the
    Mathlib dependencies).

  ## Rules

    * No `sorry`.
    * No new axioms.
    * Verified by `lake build`.
-/
import PallLean.Paper93.Spanning.BooleanityCase
import PallLean.Paper93.Spanning.AdjacencyCase
import PallLean.SymmetricPowerBound

namespace PallLean.Paper93.Spanning

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Bridge
open SymmetricPowerBound

/-! ## Abstract per-type interface (the H1 / H2 landing target)

A per-type ambient family `W : ConstraintType → Submodule ℚ
(MvPolynomial (Fin n) ℚ)` packages, for each local constraint type
`τ`, a finite-dimensional subspace of the ambient polynomial ring in
which the compiled Cook-Levin factors of type `τ` live. The key
properties we need from `W` at the H3 layer are:

  * `W τ` contains the constant polynomial `1` (this is what makes the
    `1 - …` compiled factor shape work; this property discharges G1's
    `h1` / G2's `oneMemAmbient` hypotheses).

  * `W τ` contains the strict linear ambient interface space
    `ambientInterfaceSpace n hn4 σ` for every embedding `σ`. This
    transports G1 / G2's membership-in-`ambientInterfaceSpace`
    conclusions up to the enriched per-type ambient.

Both items are precisely what Agents H1 / H2 deliver once they land.
-/

/-- The H1 / H2 abstract interface, as a `Prop`-level bundle. -/
structure PerTypeAmbientInterface
    (n : ℕ) (hn4 : n ≥ 4)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) :
    Prop where
  /-- `W τ` contains the constant polynomial `1`, for every `τ`. -/
  one_mem : ∀ τ : ConstraintType,
    (1 : MvPolynomial (Fin n) ℚ) ∈ W τ
  /-- `W τ` contains the strict linear ambient interface space
  `ambientInterfaceSpace n hn4 σ`, for every `τ` and every embedding
  `σ : Fin 4 ↪ Fin n`. -/
  ambient_le : ∀ (τ : ConstraintType) (σ : Fin 4 ↪ Fin n),
    ambientInterfaceSpace n hn4 σ ≤ W τ

/-! ## Consequences of the interface

The interface lets us re-run G1 / G2's proofs in the enlarged space
`W τ` instead of `ambientInterfaceSpace n hn4 σ`, absorbing the
residual `1 ∈ …` hypothesis into `H.one_mem τ`.
-/

/-- Discharged form of G1's `1 ∈ ambientInterfaceSpace` hypothesis:
from the H1 / H2 interface, conclude `1 ∈ W .booleanity`. -/
theorem one_mem_W_booleanity
    {n : ℕ} {hn4 : n ≥ 4}
    {W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (H : PerTypeAmbientInterface n hn4 W) :
    (1 : MvPolynomial (Fin n) ℚ) ∈ W ConstraintType.booleanity :=
  H.one_mem ConstraintType.booleanity

/-- Discharged form of G2's `oneMemAmbient` hypothesis:
from the H1 / H2 interface, conclude `1 ∈ W .adjacency`. -/
theorem one_mem_W_adjacency
    {n : ℕ} {hn4 : n ≥ 4}
    {W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (H : PerTypeAmbientInterface n hn4 W) :
    (1 : MvPolynomial (Fin n) ℚ) ∈ W ConstraintType.adjacency :=
  H.one_mem ConstraintType.adjacency

/-! ## Lifting the booleanity generator into `W .booleanity` -/

/-- Transport of G1's `booleanityLift_mem_ambient` along the
containment `ambientInterfaceSpace n hn4 σ ≤ W .booleanity`. For any
`σ : Fin 4 ↪ Fin n`, the polynomial `X_{σ 0} - X_{σ 0}^2` lies in
`W ConstraintType.booleanity`. -/
theorem booleanityLift_mem_W
    {n : ℕ} {hn4 : n ≥ 4}
    {W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (H : PerTypeAmbientInterface n hn4 W)
    (σ : Fin 4 ↪ Fin n) :
    (MvPolynomial.X (σ 0) - (MvPolynomial.X (σ 0)) ^ 2 :
        MvPolynomial (Fin n) ℚ) ∈ W ConstraintType.booleanity := by
  have hAmb :
      (MvPolynomial.X (σ 0) - (MvPolynomial.X (σ 0)) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientInterfaceSpace n hn4 σ :=
    booleanityLift_mem_ambient n hn4 σ
  exact H.ambient_le ConstraintType.booleanity σ hAmb

/-! ## Unconditional booleanity factor membership (discharged form) -/

/-- **Discharged booleanity factor membership.**

Given the H1 / H2 interface `H` and any `v : Fin n`, the compiled
Cook-Levin booleanity factor `1 - X_v + X_v^2` lies in
`W ConstraintType.booleanity` — with **no** residual
`1 ∈ ambientInterfaceSpace` hypothesis on the caller. -/
theorem booleanity_factor_mem_perType_unconditional
    {n : ℕ} {hn4 : n ≥ 4}
    {W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (H : PerTypeAmbientInterface n hn4 W)
    (v : Fin n) :
    (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
        MvPolynomial (Fin n) ℚ) ∈ W ConstraintType.booleanity := by
  classical
  -- Build the canonical embedding with `σ_v 0 = v` (Agent G1's witness).
  set σ : Fin 4 ↪ Fin n := sigmaOfVar n hn4 v with hσdef
  have hσ0 : σ 0 = v := by
    rw [hσdef]; exact sigmaOfVar_apply_zero n hn4 v
  -- Use the lifted booleanity generator, specialised at `σ_v 0 = v`.
  have hLift :
      (MvPolynomial.X (σ 0) - (MvPolynomial.X (σ 0)) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ W ConstraintType.booleanity :=
    booleanityLift_mem_W H σ
  rw [hσ0] at hLift
  -- Unfold `1 - X_v + X_v^2 = 1 - (X_v - X_v^2)` and use closure under
  -- subtraction.
  have hOne : (1 : MvPolynomial (Fin n) ℚ)
      ∈ W ConstraintType.booleanity :=
    H.one_mem ConstraintType.booleanity
  have hSub :
      ((1 : MvPolynomial (Fin n) ℚ)
          - (MvPolynomial.X v - (MvPolynomial.X v) ^ 2))
        ∈ W ConstraintType.booleanity :=
    (W ConstraintType.booleanity).sub_mem hOne hLift
  have hEq :
      (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ)
      = (1 : MvPolynomial (Fin n) ℚ)
          - (MvPolynomial.X v - (MvPolynomial.X v) ^ 2) := by
    ring
  rw [hEq]
  exact hSub

/-! ## Discharging G1's original packaged theorem

Agent G1's `booleanity_factor_mem_ambient` returns
`∃ σ : Fin 4 ↪ Fin n, 1 - X_v + X_v^2 ∈ ambientInterfaceSpace n hn4 σ`
but **only after consuming** the hypothesis
`1 ∈ ambientInterfaceSpace n hn4 (sigmaOfVar n hn4 v)`.

We restate that packaging with the `1 ∈ …` hypothesis discharged by
the H1 / H2 interface and the conclusion transported into the enlarged
`W .booleanity`.  The existential witness is the same canonical
`sigmaOfVar n hn4 v` used by G1. -/
theorem booleanity_factor_mem_perType_packaged
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (v : Fin n)
    {W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (H : PerTypeAmbientInterface n hn4 W) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ W ConstraintType.booleanity := by
  -- The `σ` existential is decoupled from `W` at this level; we still
  -- report the G1-canonical witness for stylistic alignment.
  refine ⟨sigmaOfVar n hn4 v, ?_⟩
  let _ := M; let _ := hn; let _ := htb; let _ := hns
  exact booleanity_factor_mem_perType_unconditional H v

/-! ## Unconditional adjacency factor membership (discharged form) -/

/-- **Discharged adjacency factor membership.**

Given the H1 / H2 interface `H`, and any pair `(i, j)` with `i ≠ j`,
the compiled Cook-Levin adjacency factor `1 - X_i * X_j` lies in
`W ConstraintType.adjacency` — with **no** residual `oneMemAmbient`
hypothesis on the caller. -/
theorem adjacency_factor_mem_perType_unconditional
    {n : ℕ} {hn4 : n ≥ 4}
    {W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (H : PerTypeAmbientInterface n hn4 W)
    {i j : Fin n} (hne : i ≠ j) :
    ((1 - MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin n) ℚ))
      ∈ W ConstraintType.adjacency := by
  classical
  -- Recover the adjacency-embedding witness used by G2.
  set σ : Fin 4 ↪ Fin n := adjacencyEmbedding hn4 i j hne with hσdef
  -- G2's `neg_prod_mem_ambient` at `σ` gives `- X_{σ 0} * X_{σ 1} ∈ ambient`.
  have hNegProd :
      (-(MvPolynomial.X (σ 0) * MvPolynomial.X (σ 1)) :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientInterfaceSpace n hn4 σ :=
    neg_prod_mem_ambient n hn4 σ
  -- Transport into `W .adjacency`.
  have hNegProdW :
      (-(MvPolynomial.X (σ 0) * MvPolynomial.X (σ 1)) :
          MvPolynomial (Fin n) ℚ)
        ∈ W ConstraintType.adjacency :=
    H.ambient_le ConstraintType.adjacency σ hNegProd
  -- Rewrite `σ 0 = i`, `σ 1 = j`.
  have hσ0 : σ 0 = i := by
    rw [hσdef]; exact adjacencyEmbedding_zero hn4 i j hne
  have hσ1 : σ 1 = j := by
    rw [hσdef]; exact adjacencyEmbedding_one hn4 i j hne
  rw [hσ0, hσ1] at hNegProdW
  -- Combine with `1 ∈ W .adjacency` via the submodule's additive
  -- closure.
  have hOne : (1 : MvPolynomial (Fin n) ℚ)
      ∈ W ConstraintType.adjacency :=
    H.one_mem ConstraintType.adjacency
  have hSum :
      ((1 : MvPolynomial (Fin n) ℚ)
          + (-(MvPolynomial.X i * MvPolynomial.X j)))
        ∈ W ConstraintType.adjacency :=
    (W ConstraintType.adjacency).add_mem hOne hNegProdW
  have hEq :
      (1 - MvPolynomial.X i * MvPolynomial.X j :
          MvPolynomial (Fin n) ℚ)
      = (1 : MvPolynomial (Fin n) ℚ)
          + (-(MvPolynomial.X i * MvPolynomial.X j)) := by ring
  rw [hEq]
  exact hSum

/-! ## Discharging G2's original packaged theorem -/

/-- **Discharged adjacency factor existential (task-signature form).**

For any adjacent pair `(i, j)` with `i ≠ j`, the compiled Cook-Levin
adjacency factor `1 - X_i * X_j` lies in `W ConstraintType.adjacency`
for some `σ : Fin 4 ↪ Fin n` — with no residual `oneMemAmbient`
hypothesis on the caller. -/
theorem adjacency_factor_mem_perType_packaged
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) {i j : Fin n} (hne : i ≠ j)
    {W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (H : PerTypeAmbientInterface n hn4 W) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X i * MvPolynomial.X j :
          MvPolynomial (Fin n) ℚ)
        ∈ W ConstraintType.adjacency := by
  refine ⟨adjacencyEmbedding hn4 i j hne, ?_⟩
  let _ := M; let _ := hn; let _ := htb; let _ := hns
  exact adjacency_factor_mem_perType_unconditional H hne

/-! ## Kernel-only axiom trace

The four main theorems below should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced. -/

#print axioms booleanity_factor_mem_perType_unconditional
#print axioms booleanity_factor_mem_perType_packaged
#print axioms adjacency_factor_mem_perType_unconditional
#print axioms adjacency_factor_mem_perType_packaged

end PallLean.Paper93.Spanning
