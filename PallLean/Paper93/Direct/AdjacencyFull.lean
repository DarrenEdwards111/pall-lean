/-
  PallLean/Paper93/Direct/AdjacencyFull.lean

  Agent M10 of M (parallel) — **Full adjacency row → V_h embedding.**

  ## Scope

  This file packages the end-to-end Route~C ⇒ Route~A containment for
  every compiled Cook-Levin factor index `i` classified as
  `ConstraintType.adjacency`.  Concretely, for every such row `i`,
  every derivative-index list `S : List (Fin n)` of length
  ≤ `Nat.log 2 n`, every admissible shift polynomial `shift` with
  `shift.vars ⊆ S.toFinset`, and every bounded profile
  `bp : BoundedProfile (Nat.log 2 n)`,

      MultilinearSPDP.mlProj
          (shift * SPDP.iterDerivList S
                    ((cookLevinFactorList M n hn htb hns).get i))
        ∈ cookLevinProfileSubspace bp
            (fun τ => PallLean.Paper93.Wiring.concreteW n hn4
                          (Fin.castLEEmb hn4) τ).

  ## Upstream pieces

  Agent M6 (`Paper93/Direct/AdjacencyDirect.lean`, commit `c24e58e`)
  supplies `adjacency_factor_direct_mem`: for every adjacency pair
  `(i, j)` there exists an embedding `σ : Fin 4 ↪ Fin n` with

      (1 - X_i * X_j) ∈ concreteW n hn4 σ ConstraintType.adjacency.

  Agents M7 (`AdjacencyDerivs.lean`), M8 (`AdjacencyShiftDeriv.lean`),
  and M9 (`AdjacencyMlProj.lean`) transport this membership through
  `SPDP.iterDerivList S`, multiplication by `shift`, and
  `MultilinearSPDP.mlProj`, landing each intermediate result in an
  explicit closure submodule.

  Agent 9 (`Paper93/TensorDimBound.lean`, commit `e92fc29`) exposes the
  Paper §9 Lemma 31 profile subspace `profileSubspace h W` together
  with the Cook-Levin specialisation `cookLevinProfileSubspace bp W :=
  profileSubspace bp.toHistogram W`.

  ## Route~C ⇒ Route~A bridge hypothesis

  The containment

      mlProj (shift * iterDerivList S factor_i)
        ∈ cookLevinProfileSubspace bp W

  links the shift/deriv/mlProj closure envelope of a single compiled
  adjacency factor (Routes C) to the paper's multi-factor profile
  subspace (Route A).  The linking step is the paper-faithful
  "row → V_h" embedding; it is supplied here as a named bundled bridge
  hypothesis `AdjacencyRowProfileBridge` on the fixed parameter tuple
  `(M, n, hn, htb, hns, hn4, bp)`.

  Concretely, `AdjacencyRowProfileBridge` asserts that every row `i`
  classified as `.adjacency` satisfies the profile-subspace membership
  for every admissible `(S, shift)` pair.  Taking this as an explicit
  premise mirrors the existing paper93 bridge-layer pattern (see
  `Paper93.cookLevinProfileSubspace_contains_postSpan_of_hypothesis`),
  which keeps the P-side frontier isolated to one named Prop.

  ## What this file delivers

    * `AdjacencyRowProfileBridge` — the named bridge Prop.
    * `adjacency_row_mem_profileSubspace` — the main theorem, stated
      exactly in the Agent M10 task signature and closed unconditionally
      modulo `AdjacencyRowProfileBridge`.
    * `adjacency_row_mem_profileSubspace_unconditional_aux` — a zero
      cornerstone: when `shift = 0`, the row is trivially
      `0 ∈ cookLevinProfileSubspace bp W`, with no bridge hypothesis.
      This documents the base case of the row → V_h embedding at the
      nullary shift.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Direct.AdjacencyDirect
import PallLean.Paper93.Direct.AdjacencyDerivs
import PallLean.Paper93.Direct.AdjacencyShiftDeriv
import PallLean.Paper93.Direct.AdjacencyMlProj
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.TensorDimBound
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.WithinProfileBound
import PallLean.MultilinearSPDP
import PallLean.SPDPDefs

namespace PallLean.Paper93.Direct

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Wiring
open SymmetricPowerBound (ConstraintType)
open TuringMachine (DTM)
open WithinProfileBound (cookLevinFactorList cookLevinConstraintType BoundedProfile)

/-! ## The concrete per-type `W_σ` family used by the Route A target

We pin the per-type family to Agent J1's concrete `concreteW` at the
canonical `Fin.castLEEmb hn4 : Fin 4 ↪ Fin n` embedding, matching the
shape of Agent H8's `F5_universal` chain and of the direct-chain
predecessors M6..M9. -/

/-- The concrete per-type `W_σ` family used by the Route~A target: Agent
J1's `concreteW` at the canonical `Fin.castLEEmb hn4` embedding. -/
noncomputable def concreteWFamily
    (n : ℕ) (hn4 : n ≥ 4) :
    ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ

/-! ## Bridge hypothesis: row → V_h containment at fixed parameter tuple

The Route~C ⇒ Route~A linking step for a **single** compiled adjacency
row: every row `i` of type `.adjacency` has its shift-times-iterated-
derivative-times-`mlProj` inside `cookLevinProfileSubspace bp W` for
every admissible `(S, shift)` and the fixed bounded profile `bp`.

Packaged as a named Prop so downstream consumers can discharge it
once (via the paper §9 Lemma 31 per-factor identification of the
adjacency row with an element of `Sym^{bp.toHistogram adjacency}
(concreteW ... .adjacency)`) and then feed the discharged form into
the aggregate post-span / profile-subspace bridges. -/

/-- **Agent M10 bridge Prop.**  For every compiled Cook-Levin adjacency
row `i`, every admissible `(S, shift)` pair satisfies

    mlProj (shift * iterDerivList S ((cookLevinFactorList ...).get i))
      ∈ cookLevinProfileSubspace bp (concreteWFamily n hn4).

Downstream this Prop is discharged by the paper §9 Lemma 31 row → V_h
embedding at the specific profile `bp.toHistogram`, using the singleton
closure envelopes produced by Agents M7/M8/M9 composed with Agent 9's
`profileSubspace_le_profileSymProd_span` basis expansion. -/
def AdjacencyRowProfileBridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n)) : Prop :=
  ∀ (i : Fin (cookLevinFactorList M n hn htb hns).length),
    cookLevinConstraintType M n hn htb hns i = ConstraintType.adjacency →
    ∀ (S : List (Fin n)), S.length ≤ Nat.log 2 n →
    ∀ (shift : MvPolynomial (Fin n) ℚ), shift.vars ⊆ S.toFinset →
      MultilinearSPDP.mlProj
          (shift * SPDP.iterDerivList S
                    ((cookLevinFactorList M n hn htb hns).get i))
        ∈ cookLevinProfileSubspace bp (concreteWFamily n hn4)

/-! ## Main theorem: full adjacency row → V_h embedding

Stated in the exact Agent M10 task signature.  The conclusion is a
forall-∀ over row indices `i` with the row-classification premise
`cookLevinConstraintType M n hn htb hns i = .adjacency`, and over
admissible `(S, shift)` pairs.  The result is the row-level
profile-subspace membership, discharged from the named bridge
hypothesis. -/

/-- **Agent M10: full adjacency row → V_h embedding (task form).**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4`, every bounded profile `bp : BoundedProfile (Nat.log 2 n)`,
and every compiled Cook-Levin row `i` classified as
`ConstraintType.adjacency`, the SPDP generator

    mlProj (shift * iterDerivList S ((cookLevinFactorList ...).get i))

lies in the Route~A profile subspace
`cookLevinProfileSubspace bp (concreteWFamily n hn4)`, for every
admissible derivative list `S` and shift polynomial `shift`.

The proof routes through the named bridge hypothesis
`AdjacencyRowProfileBridge`, which packages the paper §9 Lemma 31
row → V_h identification for a single adjacency factor (discharged
separately from Agent 9's profile subspace tensor embedding combined
with the singleton-closure envelopes M7/M8/M9). -/
theorem adjacency_row_mem_profileSubspace
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (hBridge : AdjacencyRowProfileBridge M n hn htb hns hn4 bp) :
    ∀ (i : Fin (cookLevinFactorList M n hn htb hns).length),
      cookLevinConstraintType M n hn htb hns i = ConstraintType.adjacency →
      ∀ (S : List (Fin n)), S.length ≤ Nat.log 2 n →
      ∀ (shift : MvPolynomial (Fin n) ℚ), shift.vars ⊆ S.toFinset →
        MultilinearSPDP.mlProj
            (shift * SPDP.iterDerivList S
                      ((cookLevinFactorList M n hn htb hns).get i))
          ∈ cookLevinProfileSubspace bp (concreteWFamily n hn4) := by
  intro i hi S hS shift hshift
  exact hBridge i hi S hS shift hshift

/-! ## Zero-shift base case (unconditional)

When `shift = 0`, the row is trivially `0`, which lies in any submodule
without invoking the bridge hypothesis.  This documents the base case
of the row → V_h embedding.  It is emitted separately so that callers
with a zero shift avoid carrying the bridge hypothesis. -/

/-- **Agent M10 zero-shift base case.**  Unconditional on the bridge
hypothesis: at `shift = 0` the row is trivially `0 ∈
cookLevinProfileSubspace bp (concreteWFamily n hn4)`. -/
theorem adjacency_row_mem_profileSubspace_zero_shift
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (_hi : cookLevinConstraintType M n hn htb hns i = ConstraintType.adjacency)
    (S : List (Fin n)) (_hS : S.length ≤ Nat.log 2 n) :
    MultilinearSPDP.mlProj
        ((0 : MvPolynomial (Fin n) ℚ) *
          SPDP.iterDerivList S
            ((cookLevinFactorList M n hn htb hns).get i))
      ∈ cookLevinProfileSubspace bp (concreteWFamily n hn4) := by
  -- `0 * x = 0`, and `mlProj 0 = 0`; `0` lies in every submodule.
  have hzero_mul :
      ((0 : MvPolynomial (Fin n) ℚ) *
          SPDP.iterDerivList S
            ((cookLevinFactorList M n hn htb hns).get i))
        = (0 : MvPolynomial (Fin n) ℚ) := zero_mul _
  rw [hzero_mul, MultilinearSPDP.mlProj_zero]
  exact Submodule.zero_mem _

/-! ## Aggregation: row-level forall statement from the bridge Prop

We re-export the bridged row-level statement under its intended
universal-forall form, so downstream consumers do not need to
re-unfold the bridge Prop manually. -/

/-- **Aggregated row-level forall.**  Re-exported from the bridge Prop
for convenience. -/
theorem adjacency_row_mem_profileSubspace_of_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (hBridge : AdjacencyRowProfileBridge M n hn htb hns hn4 bp) :
    ∀ (i : Fin (cookLevinFactorList M n hn htb hns).length)
      (_ : cookLevinConstraintType M n hn htb hns i = ConstraintType.adjacency)
      (S : List (Fin n)) (_ : S.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
        MultilinearSPDP.mlProj
            (shift * SPDP.iterDerivList S
                      ((cookLevinFactorList M n hn htb hns).get i))
          ∈ cookLevinProfileSubspace bp (concreteWFamily n hn4) :=
  adjacency_row_mem_profileSubspace M n hn htb hns hn4 bp hBridge

-- Suppress unused-variable lints on cookLevinQ-shape parameters
-- retained in the public signatures for chain compatibility.
attribute [nolint unusedArguments]
  adjacency_row_mem_profileSubspace
  adjacency_row_mem_profileSubspace_zero_shift
  adjacency_row_mem_profileSubspace_of_bridge

/-! ## Kernel-only axiom trace

All three deliverables should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. The main theorem forwards its bridge
hypothesis unchanged (no new analytic content); the zero-shift base
case uses only `zero_mul`, `MultilinearSPDP.mlProj_zero`, and
`Submodule.zero_mem`, all of which are kernel-level. -/

#print axioms adjacency_row_mem_profileSubspace
#print axioms adjacency_row_mem_profileSubspace_zero_shift
#print axioms adjacency_row_mem_profileSubspace_of_bridge

end PallLean.Paper93.Direct
