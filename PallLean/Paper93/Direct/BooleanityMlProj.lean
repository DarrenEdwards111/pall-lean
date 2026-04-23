/-
  PallLean/Paper93/Direct/BooleanityMlProj.lean

  Paper §9 Lemma 31 — direct `mlProj(shift · iterDerivList S (booleanity))`
  closure membership in the Agent I1+I3+I4 two-step closure
  `mlProjClosure (shiftClosure W ℓ)`.

  Agent M4 of 10 (parallel).

  ## Scope

  The SPDP generator for the booleanity factor
  `B_v  :=  1 - X_v + X_v^2  =  1 - X_v (1 - X_v)`
  has the canonical multilinear-projection form

      mlProj (shift · iterDerivList S B_v)

  where `shift : MvPolynomial (Fin n) ℚ` has `shift.totalDegree ≤ ℓ`
  and `S : List (Fin n)` has `S.length ≤ ℓ` with `ℓ := Nat.log 2 n`.

  This file supplies the **two-step closure membership** of that
  generator, driven purely by the Agent I1 / I3 / I4 closure
  primitives:

    * `mulByPoly` / `shiftClosure`  (Agents I1 & I3, commit `736c1db`):
      multiplication by a shift of total degree ≤ ℓ lands in the
      `shiftClosure` of the source submodule.

    * `mlProjLM` / `mlProjClosure`  (Agent I4, commit `736c1db`):
      the multilinear projection is a `ℚ`-linear endomorphism and
      sends any submodule to its `mlProjClosure`.

  The source submodule is the one-generator span

      W_B  :=  Submodule.span ℚ { iterDerivList S B_v }.

  It contains the single polynomial `iterDerivList S B_v`; by
  `shift_mul_mem_shiftClosure` (pointwise membership of `shiftClosure`),
  the shift-multiplied polynomial lies in `shiftClosure W_B ℓ`; and by
  `Submodule.mem_map_of_mem` applied to `mlProjLM`, its
  multilinear-projection lies in `mlProjClosure (shiftClosure W_B ℓ)`.

  The embedding `σ : Fin 4 ↪ Fin n` required by the paper-faithful
  Lemma 31 statement is witnessed (for the existential) by the
  canonical `sigmaOfVar n hn4 v` from Agent G1
  (`Paper93/Spanning/BooleanityCase.lean`). Its concrete identity plays
  no role in the closure conclusion; it is carried purely to align
  call-sites with the rest of the per-type chain.

  ## Deliverable

    * `booleanity_mlProj_mem` — for every Turing-machine parameter
      tuple `(M, n, hn, htb, hns)` with `hn4 : n ≥ 4`, every
      `v : Fin n`, every derivative list `S : List (Fin n)` of length
      ≤ `Nat.log 2 n`, and every shift polynomial with
      `totalDegree ≤ Nat.log 2 n`, there exists `σ : Fin 4 ↪ Fin n` with

          mlProj (shift · iterDerivList S (1 - X v + X v^2))
            ∈ mlProjClosure (shiftClosure W_B (Nat.log 2 n)),

      where `W_B` is the one-generator span.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Closure.MlProjClosure
import PallLean.Paper93.Closure.ShiftClosure
import PallLean.Paper93.Spanning.BooleanityCase

namespace PallLean.Paper93.Direct

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Closure
open PallLean.Paper93.Spanning
open SPDP (iterDerivList)

/-! ## The one-generator source submodule

Given `n`, `v`, and a derivative list `S`, the source submodule for
the two-step closure is the one-generator span of the multilinear-basis
derivative `iterDerivList S (1 - X v + X v^2)`. It has rank ≤ 1 by
`Submodule.finrank_span_singleton_le_one`; the closure construction
does not use this bound, but it is a natural witness that the source
has finite dimension. -/

/-- The one-generator source submodule used by `booleanity_mlProj_mem`.

It contains the single polynomial `iterDerivList S (1 - X v + X v^2)`
and is the natural finite-dimensional envelope for the two-step
`shiftClosure → mlProjClosure` construction. -/
noncomputable def booleanityDerivSource
    {n : ℕ} (v : Fin n) (S : List (Fin n)) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    ({ iterDerivList S
          (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
            MvPolynomial (Fin n) ℚ) }
      : Set (MvPolynomial (Fin n) ℚ))

/-- The single generator of `booleanityDerivSource` lies in it
(the membership of a `Submodule.span`'s generator in its own span). -/
theorem iterDerivList_boolFactor_mem_source
    {n : ℕ} (v : Fin n) (S : List (Fin n)) :
    iterDerivList S
        (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ)
      ∈ booleanityDerivSource (n := n) v S := by
  -- `x ∈ span {x}` is immediate from `Submodule.subset_span`.
  refine Submodule.subset_span ?_
  simp

/-! ## Main theorem

The `mlProj` of the shifted booleanity derivative lies in the two-step
closure `mlProjClosure (shiftClosure booleanityDerivSource ℓ)` with
`ℓ := Nat.log 2 n`. The embedding `σ` is witnessed by
`sigmaOfVar n hn4 v`; its concrete identity is immaterial for the
closure conclusion. -/

/-- **Agent M4 main theorem (booleanity mlProj closure membership).**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4`, every `v : Fin n`, every `S : List (Fin n)` with
`S.length ≤ Nat.log 2 n`, and every `shift : MvPolynomial (Fin n) ℚ`
with `shift.totalDegree ≤ Nat.log 2 n`, there exists
`σ : Fin 4 ↪ Fin n` such that

    mlProj (shift · iterDerivList S (1 - X v + X v^2))
      ∈ mlProjClosure (shiftClosure (booleanityDerivSource v S)
                                    (Nat.log 2 n)).

The embedding `σ` is witnessed by the canonical `sigmaOfVar n hn4 v`
from Agent G1. Its concrete identity plays no role in the closure
conclusion; it is carried purely for call-site alignment with the rest
of the per-type chain. -/
theorem booleanity_mlProj_mem
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) (hn4 : n ≥ 4)
    (S : List (Fin n)) (hS : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (hshift : shift.totalDegree ≤ Nat.log 2 n) :
    ∃ σ : Fin 4 ↪ Fin n,
      MultilinearSPDP.mlProj
          (shift * iterDerivList S
              (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
                MvPolynomial (Fin n) ℚ))
        ∈ mlProjClosure
            (shiftClosure (booleanityDerivSource (n := n) v S)
                          (Nat.log 2 n)) := by
  classical
  -- Witness the existential by `sigmaOfVar n hn4 v`. The closure
  -- conclusion does not depend on σ.
  refine ⟨sigmaOfVar n hn4 v, ?_⟩
  -- Abbreviate the booleanity-factor derivative and set `ℓ`.
  set ℓ : ℕ := Nat.log 2 n
  set g : MvPolynomial (Fin n) ℚ :=
    iterDerivList S
      (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
        MvPolynomial (Fin n) ℚ) with hg_def
  -- Step 1: `g ∈ booleanityDerivSource v S` (single-generator span).
  have hg_mem : g ∈ booleanityDerivSource (n := n) v S := by
    simpa [g, booleanityDerivSource]
      using iterDerivList_boolFactor_mem_source (n := n) v S
  -- Step 2: `shift * g ∈ shiftClosure (booleanityDerivSource v S) ℓ`.
  --   Use the pointwise-membership lemma `shift_mul_mem_shiftClosure`.
  have hshift_mem :
      shift * g
        ∈ shiftClosure (booleanityDerivSource (n := n) v S) ℓ :=
    shift_mul_mem_shiftClosure
      (booleanityDerivSource (n := n) v S) ℓ hg_mem hshift
  -- Step 3: `mlProj (shift * g) ∈ mlProjClosure (shiftClosure …) ℓ`.
  --   Unfold `mlProj` to `mlProjLM` (i.e. `mlProjLinearMap (Fin n) ℚ`)
  --   and push membership through `Submodule.mem_map_of_mem`.
  --   By construction of `mlProjLM`, `mlProjLM x = mlProj x` on nose.
  have hmlProj_eq :
      MultilinearSPDP.mlProj (shift * g)
        = mlProjLM (N := n) (shift * g) := rfl
  -- Apply `Submodule.mem_map_of_mem`:
  --   x ∈ W → f x ∈ W.map f.
  have hmap_mem :
      mlProjLM (N := n) (shift * g)
        ∈ Submodule.map (mlProjLM (N := n))
            (shiftClosure (booleanityDerivSource (n := n) v S) ℓ) :=
    Submodule.mem_map_of_mem hshift_mem
  -- Rewrite `mlProjClosure` to the `.map mlProjLM` form and conclude.
  have hclosure_eq :
      mlProjClosure
          (shiftClosure (booleanityDerivSource (n := n) v S) ℓ)
        = Submodule.map (mlProjLM (N := n))
            (shiftClosure (booleanityDerivSource (n := n) v S) ℓ) := by
    rfl
  rw [hmlProj_eq, hclosure_eq]
  exact hmap_mem

/-! ## Kernel-only axiom trace

The main deliverable depends only on
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms booleanity_mlProj_mem

end PallLean.Paper93.Direct
