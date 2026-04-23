/-
  PallLean/Paper93/Direct/TransitionLeftDirect.lean

  Paper §9 Lemma 31 — direct transitionLeft factor membership in the
  concrete `W_σ(τ)` family.

  Agent M11 of M (parallel).

  ## Scope

  Agent J1 (commit `b36a8b1`) introduces the concrete per-type interface
  family

      concreteW n hn4 σ τ :=
          ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ τ

  as a `Submodule ℚ (MvPolynomial (Fin n) ℚ)`.

  Agent G3 (commit `2ee6131`,
  `PallLean/Paper93/Spanning/TransitionLeftCase.lean`) exposes the
  ambient-level "transitionLeft factor polynomial"

      transitionLeftAmbientFactor σ
        := MvPolynomial.rename σ.toFun transitionTemplate
         = X (σ 0) : MvPolynomial (Fin n) ℚ,

  and proves its membership in Agent F4's *shared-target*
  `ambientInterfaceSpace n hn4 σ` (the rename-image of Agent A's
  `realInterfaceSpace = span {booleanityTemplate, adjacencyTemplate,
  transitionTemplate}`).

  Agent H1 (`PallLean/Paper93/Bridge/PerTypeInterfaceSpace.lean`) defines
  the per-type source space

      perTypeInterfaceSpace .transitionLeft
        = Submodule.span ℚ {1, X 0} ⊆ MvPolynomial (Fin 4) ℚ,

  and Agent H2 (`PallLean/Paper93/Bridge/AmbientPerType.lean`) lifts this
  to `ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ .transitionLeft`
  along the coordinate embedding `σ : Fin 4 ↪ Fin n`.

  The content of Agent G3's witness σ is that `X (σ 0)` is the rename of
  `X 0 = transitionTemplate`, and `X 0` already lies in
  `perTypeInterfaceSpace .transitionLeft` (as a generator of its span).
  Hence by `Submodule.mem_map` applied to the rename algebra-hom's
  underlying linear map, `X (σ 0) ∈ ambientPerTypeSpace …`, i.e.
  `∈ concreteW n hn4 σ .transitionLeft` by J1's definition.

  ## What this file delivers

  * `transitionLeft_factor_direct_mem` — for every Turing-machine
    parameter tuple `(M, n, hn, htb, hns, q, i, j)` with `hn4 : n ≥ 4`,
    there exists an embedding `σ : Fin 4 ↪ Fin n` along which the
    compiled Cook-Levin transitionLeft factor polynomial
    `transitionLeftAmbientFactor σ = X (σ 0)` lies in Agent J1's
    concrete `W_σ` family at the transitionLeft constraint type,
    `concreteW n hn4 σ .transitionLeft`.

  The witness σ is the canonical `Fin.castLEEmb hn4` (matching Agent G3
  and Agents F1 / H3 convention). The trailing parameters
  `(q, i, j)` from the cookLevinQ-shape signature are retained in the
  public signature for downstream chain compatibility but are not used
  in the proof — the transitionLeft factor polynomial at the ambient
  `Fin n` level depends only on the type `.transitionLeft`, not on the
  per-instance parameters.

  ## Proof strategy

  1. Choose σ := `Fin.castLEEmb hn4` (G3's canonical witness).
  2. Source-side: `X 0 ∈ perTypeInterfaceSpace .transitionLeft` by
     `Submodule.subset_span`, since the H1 generating set is
     `{1, X 0}`.
  3. Rename lift: by `Submodule.mem_map` applied to the linear map
     underlying the algebra-hom `MvPolynomial.rename σ.toFun`,
     `rename σ.toFun (X 0) = X (σ 0) ∈ ambientPerTypeSpace
     perTypeInterfaceSpace n hn4 σ .transitionLeft`.
  4. J1's `concreteW` unfolds definitionally to Step 3's ambient space,
     yielding the stated membership.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Spanning.TransitionLeftCase
import PallLean.Paper93.Spanning.DischargeOneMem
import PallLean.Paper93.Wiring.ConcreteW

namespace PallLean.Paper93.Direct

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Bridge
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring
open SymmetricPowerBound (ConstraintType)

/-! ## Source-side: `X 0 ∈ perTypeInterfaceSpace .transitionLeft`

Agent H1's per-type source space at `.transitionLeft` is
`span {1, X 0}`. The generator `X 0` lies in this span by
`Submodule.subset_span`. This mirrors the `adjacency_source_generator_mem`
and `booleanity_source_generator_mem` private lemmas of Agent H3
(`DischargeOneMem`), adapted to the transitionLeft single-variable
generator. -/

/-- The source-side transitionLeft generator `X 0` lies in Agent H1's
`perTypeInterfaceSpace .transitionLeft`, directly from the
generating-set enumeration. -/
private theorem transitionLeft_source_generator_mem :
    (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) ℚ)
      ∈ perTypeInterfaceSpace ConstraintType.transitionLeft := by
  unfold perTypeInterfaceSpace
  exact Submodule.subset_span (by simp)

/-! ## Lift to `ambientPerTypeSpace`

The rename algebra-hom `MvPolynomial.rename σ.toFun` sends `X 0` to
`X (σ 0)`. Combined with the source-side membership above, this places
`X (σ 0) ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn σ
.transitionLeft`, which is J1's `concreteW n hn σ .transitionLeft` by
definition. -/

/-- The renamed transitionLeft generator
`X (σ 0) ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn σ
.transitionLeft`, obtained by mapping the source-level membership
through the algebra homomorphism `rename σ.toFun`. This is the per-type
analogue of G3's `transitionLeftAmbientFactor_mem_ambient`, landing in
H2's per-type space rather than F4's shared-target space. -/
theorem transitionLeftLift_mem_ambientPerType
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (MvPolynomial.X (σ 0) : MvPolynomial (Fin n) ℚ)
      ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn σ
          ConstraintType.transitionLeft := by
  classical
  have h_src := transitionLeft_source_generator_mem
  -- The rename acts on `X 0` by sending it to `X (σ 0)`.
  have h_eq :
      (MvPolynomial.rename (σ.toFun : Fin 4 → Fin n)
          (MvPolynomial.X (0 : Fin 4)) :
            MvPolynomial (Fin n) ℚ)
        = MvPolynomial.X (σ 0) := by
    simp [rename_X, Function.Embedding.toFun_eq_coe]
  refine ⟨_, h_src, ?_⟩
  -- The goal reduces by definition of `ambientPerTypeSpace` to
  -- `(rename σ.toFun).toLinearMap (X 0) = X (σ 0)`, i.e. `h_eq`.
  simpa [ambientPerTypeSpace] using h_eq

/-! ## Main theorem: direct transitionLeft factor membership in `concreteW`

Combining Agent G3's canonical σ-witness convention (`Fin.castLEEmb hn4`)
with the per-type lift above, we obtain the direct membership of the
transitionLeft factor polynomial `transitionLeftAmbientFactor σ = X
(σ 0)` in `concreteW n hn4 σ .transitionLeft`.

The proof strategy follows Agents M1 / M6 (booleanity / adjacency
direct discharges) by unfolding `concreteW` to `ambientPerTypeSpace
perTypeInterfaceSpace …` and appealing to the per-type lift. -/

/-- **Agent M11: direct transitionLeft factor membership in the concrete
`W_σ` family.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4` and every triple `(q, i, j)` parameterising a
transitionLeft factor, there exists an embedding `σ : Fin 4 ↪ Fin n`
along which the compiled Cook-Levin transitionLeft factor polynomial
`transitionLeftAmbientFactor σ = X (σ 0)` lies in Agent J1's concrete
`W_σ` family at the transitionLeft constraint type,
`concreteW n hn4 σ .transitionLeft`.

The witness σ is the canonical `Fin.castLEEmb hn4` (matching Agent G3's
`transitionLeft_factor_mem_ambient` choice and Agents F1 / H3 convention).

The parameters `(q, i, j)` are retained in the signature for
downstream cookLevinQ-shape compatibility but are not used in the
proof — the transitionLeft factor polynomial at the ambient `Fin n`
level depends only on the constraint type, not on the per-instance
parameters, matching Agent G3's observation that the local template is
uniform in `(q, i, j)`.

The proof combines:

  * Agent G3's σ := `Fin.castLEEmb hn4` canonical witness choice
    (`transitionLeft_factor_mem_ambient`, commit `2ee6131`), and
  * Agent J1's definitional equality
    `concreteW n hn4 σ τ = ambientPerTypeSpace perTypeInterfaceSpace
    n hn4 σ τ` (commit `b36a8b1`),

  via the per-type lift `transitionLeftLift_mem_ambientPerType`
  (Agent H1 source-side `X 0 ∈ perTypeInterfaceSpace .transitionLeft`
  + Agent H2 rename-pushforward to ambient). -/
theorem transitionLeft_factor_direct_mem
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (q : Fin M.numStates) (i : Fin n) (j : Fin n) (hn4 : n ≥ 4) :
    ∃ σ : Fin 4 ↪ Fin n,
      (transitionLeftAmbientFactor σ : MvPolynomial (Fin n) ℚ)
        ∈ PallLean.Paper93.Wiring.concreteW n hn4 σ
            ConstraintType.transitionLeft := by
  classical
  -- G3 canonical σ-witness: `Fin.castLEEmb hn4`.
  refine ⟨Fin.castLEEmb hn4, ?_⟩
  -- Silence unused-argument lints on the cookLevinQ-shape parameters
  -- retained in the public signature for downstream chain compatibility.
  let _ := M; let _ := hn; let _ := htb; let _ := hns
  let _ := q; let _ := i; let _ := j
  -- Unfold J1's `concreteW` to H2's `ambientPerTypeSpace perTypeInterfaceSpace`.
  show (transitionLeftAmbientFactor (Fin.castLEEmb hn4) :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (Fin.castLEEmb hn4) ConstraintType.transitionLeft
  -- Reduce `transitionLeftAmbientFactor σ` to `X (σ 0)` via G3's
  -- `transitionLeftAmbientFactor_eq_X` lemma.
  rw [transitionLeftAmbientFactor_eq_X]
  -- The goal is now `X (σ 0) ∈ ambientPerTypeSpace … .transitionLeft`,
  -- which is the per-type lift of `X 0 ∈ perTypeInterfaceSpace
  -- .transitionLeft`.
  exact transitionLeftLift_mem_ambientPerType n hn4 (Fin.castLEEmb hn4)

-- Suppress unused-variable lints on the cookLevinQ-shape parameters
-- retained in the public signature for downstream chain compatibility.
attribute [nolint unusedArguments] transitionLeft_factor_direct_mem

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced. -/

#print axioms transitionLeft_factor_direct_mem

end PallLean.Paper93.Direct
