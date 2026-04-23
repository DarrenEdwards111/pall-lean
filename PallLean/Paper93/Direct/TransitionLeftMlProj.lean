/-
  PallLean/Paper93/Direct/TransitionLeftMlProj.lean

  Agent M14 (of 10+, parallel) — Direct bridge: for the `transitionLeft`
  case of the Cook-Levin factor list, `mlProj (shift * iterDerivList S g)`
  lies in the `mlProjClosure` of the shift-closure of the derivative
  submodule of any per-type ambient space containing the `transitionLeft`
  ambient factor.

  ## Scope

  Agent G3 (`Paper93/Spanning/TransitionLeftCase.lean`, commit
  `2ee6131`) supplied `transitionLeftAmbientFactor_mem_ambient`, which
  places the ambient `transitionLeft` factor polynomial
  `transitionLeftAmbientFactor σ` in the ambient interface space
  `ambientInterfaceSpace n hn4 σ`.

  Agent H4 (`Paper93/Spanning/DerivativeClosure.lean`, commit
  `8fba527`) provides `iterDerivSubmodule` (iterated-derivative
  submodule) and the transport lemma
  `iterDerivList_mem_iterDerivSubmodule`.

  Agent I1 (`Paper93/Closure/ShiftMultiplication.lean`, commit
  `f7cf8ca`) provides `mulByPoly` as a `ℚ`-linear endomorphism.

  Agent I3 (`Paper93/Closure/ShiftClosure.lean`, commit `295e346`)
  provides `shiftClosure` and `mul_mem_shiftClosure`.

  Agent I4 (`Paper93/Closure/MlProjClosure.lean`, commit `736c1db`)
  provides `mlProjLM`, `mlProjClosure`, and `mlProjClosure_def`.

  This file (M14) composes those layers into a single per-factor
  containment statement for the `transitionLeft` case. The theorem
  says: for any submodule `W ≤ MvPolynomial (Fin n) ℚ` containing
  the ambient `transitionLeft` factor, any list of indices `S`,
  any shift polynomial `shift` of total degree ≤ `ℓ`, we have

      mlProj (shift * iterDerivList S (transitionLeftAmbientFactor σ))
        ∈ mlProjClosure (shiftClosure (iterDerivSubmodule W S) ℓ).

  This is the `transitionLeft`-specialised instance of the general
  "Route C ⇒ Route A" per-factor containment argument, i.e. the
  statement that the SPDP generator `mlProj (shift * iterDerivList S g)`
  for `g = transitionLeftAmbientFactor σ` lies in the `mlProj`-closure
  of the shift-closure of the derivative submodule of the ambient
  `W_σ` / `W τ` containing `g`.

  ## Faithfulness

  All content is module-theoretic linear algebra over `ℚ`:

    1. H4's `iterDerivList_mem_iterDerivSubmodule` transports the
       membership `g ∈ W` into
       `iterDerivList S g ∈ iterDerivSubmodule W S`.
    2. I3's `mul_mem_shiftClosure` transports that into
       `shift * iterDerivList S g ∈ shiftClosure (iterDerivSubmodule W S) ℓ`,
       provided `shift.totalDegree ≤ ℓ`.
    3. I4's `mlProjClosure_def` + `Submodule.mem_map_of_mem` (via the
       linear map `mlProjLM`) transport that into
       `mlProj (shift * iterDerivList S g) ∈ mlProjClosure (…)`.

  No new axioms, no `sorry`, no bespoke `axiom`. Kernel-only.

  Expected `#print axioms` output:
      [propext, Classical.choice, Quot.sound].
-/
import PallLean.Paper93.Closure.MlProjClosure
import PallLean.Paper93.Closure.ShiftClosure
import PallLean.Paper93.Spanning.DerivativeClosure
import PallLean.Paper93.Spanning.TransitionLeftCase

namespace PallLean
namespace Paper93
namespace Direct

open MvPolynomial SPDP
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Closure

/-! ## 1. Generic per-factor route (Route C ⇒ Route A skeleton)

The route is purely module-theoretic and does not use any property of
the `transitionLeft` factor beyond its membership in `W`. We state it
here in generic form so that the `transitionLeft` specialisation
below is a one-line corollary, and parallel agents handling other
factor types (booleanity, adjacency, …) can consume the same helper. -/

/-- **Generic containment.** For any submodule `W ≤ MvPolynomial (Fin n) ℚ`,
any list `S` of variable indices, any shift polynomial `shift` of total
degree ≤ `ℓ`, and any polynomial `g ∈ W`, the SPDP generator
`mlProj (shift * iterDerivList S g)` lies in

    mlProjClosure (shiftClosure (iterDerivSubmodule W S) ℓ).

The proof is a three-step chase through the H4 / I3 / I4 closure
layers. -/
theorem mlProj_shift_iterDeriv_mem_mlProjClosure_generic
    {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ) (ℓ : ℕ)
    (hshift : shift.totalDegree ≤ ℓ)
    (g : MvPolynomial (Fin n) ℚ) (hg : g ∈ W) :
    MultilinearSPDP.mlProj (shift * iterDerivList S g)
      ∈ mlProjClosure
          (shiftClosure (iterDerivSubmodule W S) ℓ) := by
  classical
  -- Step 1 (H4): iterDerivList S g ∈ iterDerivSubmodule W S.
  have h1 : iterDerivList S g ∈ iterDerivSubmodule W S :=
    iterDerivList_mem_iterDerivSubmodule W g hg S
  -- Step 2 (I3): shift * iterDerivList S g ∈ shiftClosure (iterDerivSubmodule W S) ℓ.
  have h2 :
      shift * iterDerivList S g
        ∈ shiftClosure (iterDerivSubmodule W S) ℓ := by
    -- `mul_mem_shiftClosure` is stated as `f * s ∈ …` for `f ∈ W, s.totalDegree ≤ ℓ`.
    -- We want `shift * iterDerivList S g`; apply commutativity of `MvPolynomial`.
    have := mul_mem_shiftClosure
      (W := iterDerivSubmodule W S) (ℓ := ℓ)
      (f := iterDerivList S g) (s := shift) h1 hshift
    -- `iterDerivList S g * shift = shift * iterDerivList S g` in the commutative algebra.
    simpa [mul_comm] using this
  -- Step 3 (I4): apply `mlProjLM` (linear) and land in `mlProjClosure`.
  -- Unfold `mlProjClosure = W.map mlProjLM`; use `Submodule.mem_map_of_mem`.
  have h3 :
      mlProjLM (N := n) (shift * iterDerivList S g)
        ∈ (shiftClosure (iterDerivSubmodule W S) ℓ).map (mlProjLM (N := n)) :=
    Submodule.mem_map_of_mem h2
  -- Identify `mlProjLM p = MultilinearSPDP.mlProj p` and rewrite the goal
  -- through `mlProjClosure_def`. By definition
  -- `mlProjLM = MultilinearSPDP.mlProjLinearMap (Fin n) ℚ` and the
  -- latter's `toFun` is `MultilinearSPDP.mlProj`, so equality is `rfl`.
  have happ :
      mlProjLM (N := n) (shift * iterDerivList S g)
        = MultilinearSPDP.mlProj (shift * iterDerivList S g) := rfl
  rw [mlProjClosure_def]
  rw [happ] at h3
  exact h3

/-! ## 2. `transitionLeft` specialisation

We specialise `mlProj_shift_iterDeriv_mem_mlProjClosure_generic` to
`g := transitionLeftAmbientFactor σ` and a submodule `W` that
contains it. The canonical choice is
`W = ambientInterfaceSpace n hn4 σ` (via G3's
`transitionLeftAmbientFactor_mem_ambient`), but we keep `W` as a
hypothesis to permit any over-approximation. -/

/-- **`transitionLeft` specialisation.**

For any submodule `W ≤ MvPolynomial (Fin n) ℚ` containing the ambient
`transitionLeft` factor `transitionLeftAmbientFactor σ`, any list `S`
of variable indices, and any shift polynomial `shift` of total
degree ≤ `ℓ`, the SPDP generator

    mlProj (shift * iterDerivList S (transitionLeftAmbientFactor σ))

lies in `mlProjClosure (shiftClosure (iterDerivSubmodule W S) ℓ)`.

This is the per-factor Route C ⇒ Route A containment at the
`transitionLeft` case, consumed downstream by the per-type profile
composition and the closure layer's `mlProj` closure hypothesis. -/
theorem transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure
    {n : ℕ} (σ : Fin 4 ↪ Fin n)
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hWg : transitionLeftAmbientFactor σ ∈ W)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ) (ℓ : ℕ)
    (hshift : shift.totalDegree ≤ ℓ) :
    MultilinearSPDP.mlProj
        (shift * iterDerivList S (transitionLeftAmbientFactor σ))
      ∈ mlProjClosure
          (shiftClosure (iterDerivSubmodule W S) ℓ) :=
  mlProj_shift_iterDeriv_mem_mlProjClosure_generic
    W S shift ℓ hshift (transitionLeftAmbientFactor σ) hWg

/-- **`transitionLeft` specialisation at the canonical ambient `W_σ`.**

Direct corollary: when `W = ambientInterfaceSpace n hn4 σ` (G3's
canonical ambient per-σ space), the hypothesis
`transitionLeftAmbientFactor σ ∈ W` is discharged by G3's
`transitionLeftAmbientFactor_mem_ambient`, yielding an unconditional
containment statement at the ambient `W_σ`. -/
theorem transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure_ambient
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ) (ℓ : ℕ)
    (hshift : shift.totalDegree ≤ ℓ) :
    MultilinearSPDP.mlProj
        (shift * iterDerivList S (transitionLeftAmbientFactor σ))
      ∈ mlProjClosure
          (shiftClosure
            (iterDerivSubmodule
              (PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4 σ)
              S)
            ℓ) :=
  transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure
    (n := n) σ
    (PallLean.Paper93.Bridge.ambientInterfaceSpace n hn4 σ)
    (transitionLeftAmbientFactor_mem_ambient n hn4 σ)
    S shift ℓ hshift

end Direct
end Paper93
end PallLean
