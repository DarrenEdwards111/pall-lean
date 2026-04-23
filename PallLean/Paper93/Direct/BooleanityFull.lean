/-
  PallLean/Paper93/Direct/BooleanityFull.lean

  Agent M5 of M (parallel) — full row→V_h embedding at `concreteW` for
  the booleanity constraint type.

  ## Scope

  This file closes the chain M1 → M2 → M3 → M4 by lifting the direct
  booleanity-factor ambient membership (Agent M1), the derivative
  closure transport (Agent M2, via H4), the shift / iterated-derivative
  product (Agent M3, via I1 / I2), and the per-derivative `iterDerivList`
  transport through the multilinear projection `mlProj` into an
  *explicit row-in-profile-subspace* statement.

  Concretely, for every cookLevinQ parameter tuple `(M, n, hn, htb, hns)`
  with `hn4 : n ≥ 4`, every bounded profile `bp`, every factor index
  `i` of type `booleanity`, every bounded derivative list
  `S : List (Fin n)`, and every shift polynomial whose variables are
  contained in `S.toFinset`, the SPDP row

      mlProj (shift * iterDerivList S ((cookLevinFactorList …).get i))

  lies in Agent B's `cookLevinProfileSubspace bp (concreteW …)` — the
  Paper §9 Lemma 31 profile subspace specialised to Agent J1's concrete
  per-type ambient family.

  The proof is a direct composition of:

    * Agent H3's `CookLevinFactorMemPerType`-style per-factor
      membership at `concreteW` — each booleanity factor of the compiled
      Cook-Levin list lies in `concreteW n hn4 σ .booleanity`;

    * Agent H4's `DerivClosurePerType`-style derivative-closure
      transport at `concreteW` — derivative submodule of
      `concreteW τ` is contained in `concreteW τ`;

    * Agent I5's `PerTypeShiftMlprojClosure`-style shift-and-mlProj
      closure at `concreteW` — products of per-factor derivatives with
      matching derivative-count profile, shifted by a bounded polynomial
      and projected by `mlProj`, remain in the profile subspace.

  The "appropriate bp" condition is made explicit as a hypothesis
  `hbp_shape` on the shape of `bp.toHistogram`: the booleanity mass
  equals `S.length` and all other coordinates vanish. This matches the
  derivative-count profile of the singleton distribution that places
  all `S.length` derivatives on the booleanity factor `i`.

  ## Deliverable

    * `booleanity_row_mem_profileSubspace` — the row-in-profileSubspace
      statement at `concreteW`.

  ## Upstream content used

    * Agent M1 (`booleanity_factor_direct_mem`,
      `Paper93/Direct/BooleanityDirect.lean`) for the base per-factor
      membership, used indirectly through the `CookLevinFactorMemPerType`
      hypothesis.

    * Agent H4 (`iterDerivList_mem_iterDerivSubmodule`,
      `Paper93/Spanning/DerivativeClosure.lean`) for the derivative
      transport, used indirectly through the `DerivClosurePerType`
      hypothesis.

    * Agent I5 (`PerTypeShiftMlprojClosure`,
      `Paper93/Spanning/PerDerivativeSpanning.lean`) for the final
      shift/mlProj closure step, taken as an explicit hypothesis at the
      concrete `concreteW` family.

    * Agent B (`cookLevinProfileSubspace`,
      `Paper93/CookLevinProfileSubspace.lean`) for the target profile
      subspace.

    * Agent J1 (`concreteW`, `Paper93/Wiring/ConcreteW.lean`) for the
      concrete ambient W family.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; all upstream ingredients are taken as Prop-level
      hypotheses at the concrete W.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Direct.BooleanityDirect
import PallLean.Paper93.Spanning.PerDerivativeSpanning
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.CookLevinProfileSubspace

namespace PallLean.Paper93.Direct

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound SPDP MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring

/-! ## Auxiliary: the singleton derivative distribution has the expected
    derivative-count profile.

For the single-factor case `L = 1` with
`constraintType := fun _ => .booleanity` and `d := fun _ => S`, the
`derivCountProfile` assigns `S.length` to `.booleanity` and `0` to every
other constraint type. This matches the "appropriate bp" hypothesis. -/

/-- Singleton derivative-count profile for a single booleanity factor
covering the full list `S` of derivatives. The booleanity coordinate is
`S.length` and all other coordinates vanish. -/
def singletonBooleanityProfile {n : ℕ} (S : List (Fin n)) : ProfileHistogram :=
  fun τ => if τ = ConstraintType.booleanity then S.length else 0

@[simp] theorem singletonBooleanityProfile_booleanity {n : ℕ}
    (S : List (Fin n)) :
    singletonBooleanityProfile S ConstraintType.booleanity = S.length := by
  simp [singletonBooleanityProfile]

@[simp] theorem singletonBooleanityProfile_not_booleanity {n : ℕ}
    (S : List (Fin n)) (τ : ConstraintType) (hτ : τ ≠ ConstraintType.booleanity) :
    singletonBooleanityProfile S τ = 0 := by
  simp [singletonBooleanityProfile, hτ]

/-- The derivative-count profile of the singleton `L = 1` distribution
with constraint type `.booleanity` and derivative list `S` equals
`singletonBooleanityProfile S`. -/
theorem derivCountProfile_singleton_booleanity {n : ℕ}
    (S : List (Fin n)) :
    derivCountProfile (fun _ : Fin 1 => ConstraintType.booleanity)
        (fun _ : Fin 1 => S)
      = singletonBooleanityProfile S := by
  classical
  funext τ
  -- `derivCountProfile` sums `(d i).length` over `{i : Fin 1 // ctype i = τ}`.
  -- For `ctype = const booleanity`, this subtype is either the whole
  -- `Fin 1` (when τ = booleanity) or empty (otherwise).
  unfold derivCountProfile
  by_cases hτ : τ = ConstraintType.booleanity
  · -- Case τ = booleanity: the subtype contains `⟨0, rfl⟩` uniquely.
    subst hτ
    rw [singletonBooleanityProfile_booleanity]
    -- Evaluate the sum over the unique element: use `Finset.sum_const`
    -- plus `Fintype.card_subtype_eq_one` for the `Fin 1` / true predicate.
    have hcard :
        Finset.univ.card
          (α := { i : Fin 1 //
              (fun _ : Fin 1 => ConstraintType.booleanity) i
                = ConstraintType.booleanity }) = 1 := by
      -- The predicate `(fun _ => booleanity) i = booleanity` is True,
      -- so the subtype is equiv to `Fin 1`, hence card = 1.
      have : Fintype.card { i : Fin 1 //
          (fun _ : Fin 1 => ConstraintType.booleanity) i
            = ConstraintType.booleanity } = 1 := by
        rw [Fintype.subtype_card]
        simp
      simp [Finset.card_univ]
    rw [Finset.sum_const]
    rw [hcard, one_smul]
  · -- Case τ ≠ booleanity: the subtype is empty.
    rw [singletonBooleanityProfile_not_booleanity S τ hτ]
    -- The subtype is empty since `(fun _ => booleanity) i = booleanity`
    -- but `τ ≠ booleanity`.
    have hempty : IsEmpty { i : Fin 1 //
        (fun _ : Fin 1 => ConstraintType.booleanity) i = τ } := by
      refine ⟨fun ⟨_, hi⟩ => ?_⟩
      exact hτ hi.symm
    -- Sum over an empty type is 0.
    exact Finset.sum_of_isEmpty _

/-! ## Main theorem — the full row→V_h embedding at concreteW for the
    booleanity case.

The row

  `mlProj (shift * iterDerivList S (factor_i))`

for a booleanity factor `i` lies in `cookLevinProfileSubspace bp
(concreteW n hn4 (Fin.castLEEmb hn4))` whenever `bp` matches the
singleton derivative profile. The proof composes

  * the hypothesis `hFactor : CookLevinFactorMemPerType … concreteW` —
    `factor_i ∈ concreteW n hn4 σ .booleanity` with σ pinned to
    `Fin.castLEEmb hn4`;

  * the hypothesis `hDerivClos : DerivClosurePerType … concreteW` —
    derivative closure of `concreteW τ` under `iterDerivList S`;

  * the hypothesis `hShiftMlproj : PerTypeShiftMlprojClosure … concreteW`
    — shift+mlProj closure of `cookLevinProfileSubspace bp (concreteW)`,
    applied to the singleton product `L = 1, factors = fun _ => factor_i,
    d = fun _ => S`.

The `bp` argument is kept explicit on the signature so downstream
callers can instantiate at any bounded profile whose histogram matches
`singletonBooleanityProfile S`. -/

/-- **Agent M5 main theorem: booleanity-row profile-subspace membership
at `concreteW`.**

For every cookLevinQ parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4`, every bounded profile `bp` at radius `Nat.log 2 n` whose
underlying histogram matches `singletonBooleanityProfile S`, every
factor index `i` of constraint type `.booleanity`, every bounded
derivative list `S` with `S.length ≤ Nat.log 2 n`, and every shift
polynomial with `shift.vars ⊆ S.toFinset`, the SPDP row
`mlProj (shift * iterDerivList S (cookLevinFactorList.get i))` lies in
`cookLevinProfileSubspace bp (concreteW n hn4 (Fin.castLEEmb hn4))`.

The proof constructs the singleton `L = 1` witness consumed by the
`PerTypeShiftMlprojClosure` hypothesis at `concreteW`, using
`hFactor` for the per-factor ambient membership and `hDerivClos` for
the derivative closure into `concreteW .booleanity`. No new analytic
content is introduced: this is a pure composition. -/
theorem booleanity_row_mem_profileSubspace
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (hFactor : CookLevinFactorMemPerType M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hDerivClos : DerivClosurePerType (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hShiftMlproj : PerTypeShiftMlprojClosure (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)) :
    ∀ (i : Fin (cookLevinFactorList M n hn htb hns).length)
      (_hi : cookLevinConstraintType M n hn htb hns i
              = ConstraintType.booleanity)
      (S : List (Fin n)) (_hS : S.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin n) ℚ)
      (_hshift : shift.vars ⊆ S.toFinset)
      (_hbp_shape_S : bp.toHistogram = singletonBooleanityProfile S),
      MultilinearSPDP.mlProj
          (shift * SPDP.iterDerivList S
            ((cookLevinFactorList M n hn htb hns).get i))
        ∈ cookLevinProfileSubspace bp
            (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) := by
  classical
  intro i hi S hSlen shift hshiftvars hbp_shape_S
  -- Abbreviations.
  set W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ with hW_def
  -- Step 1: H3+H4 transport — the iterated derivative of factor_i
  -- lies in `W .booleanity`.
  have hDerivMem :
      iterDerivList S ((cookLevinFactorList M n hn htb hns).get i)
        ∈ W ConstraintType.booleanity :=
    iterDerivList_factor_mem_W
      M n hn htb hns W hFactor hDerivClos i
      ConstraintType.booleanity hi S hSlen
  -- Step 2: package the singleton `L = 1` witness for
  -- `PerTypeShiftMlprojClosure`.
  -- The singleton has factors = fun _ => factor_i, d = fun _ => S,
  -- constraintType = fun _ => .booleanity.
  have hg_prod_witness :
      ∃ (L : ℕ) (factors : Fin L → MvPolynomial (Fin n) ℚ)
        (constraintType : Fin L → ConstraintType)
        (d : Fin L → List (Fin n)),
        (∀ j, ∀ v ∈ d j, v ∈ S) ∧
        (∀ j, iterDerivList (d j) (factors j) ∈ W (constraintType j)) ∧
        iterDerivList S ((cookLevinFactorList M n hn htb hns).get i)
          = Finset.univ.prod (fun j => iterDerivList (d j) (factors j)) ∧
        derivCountProfile constraintType d = bp.toHistogram ∧
        ∑ j : Fin L, (d j).length ≤ S.length := by
    refine ⟨1,
      fun _ : Fin 1 => (cookLevinFactorList M n hn htb hns).get i,
      fun _ : Fin 1 => ConstraintType.booleanity,
      fun _ : Fin 1 => S,
      ?_, ?_, ?_, ?_, ?_⟩
    · -- `∀ j, ∀ v ∈ d j, v ∈ S` : for `d := fun _ => S`, this is `v ∈ S → v ∈ S`.
      intro _ v hv
      exact hv
    · -- `∀ j, iterDerivList (d j) (factors j) ∈ W (constraintType j)`:
      -- at `j : Fin 1`, this is `iterDerivList S factor_i ∈ W .booleanity`,
      -- which is `hDerivMem`.
      intro _
      exact hDerivMem
    · -- `iterDerivList S factor_i = Finset.univ.prod …`: the `Fin 1`
      -- product has one factor, equal to its sole index.
      simp
    · -- `derivCountProfile (const .booleanity) (const S) = bp.toHistogram`:
      -- follows from the singleton profile lemma and the shape hypothesis.
      rw [derivCountProfile_singleton_booleanity]
      exact hbp_shape_S.symm
    · -- `∑ j : Fin 1, (d j).length ≤ S.length`: the sum has one
      -- summand, equal to `S.length`.
      simp
  -- Step 3: feed the witness into `PerTypeShiftMlprojClosure`.
  have hClosureApp :
      mlProj (shift *
          iterDerivList S ((cookLevinFactorList M n hn htb hns).get i))
        ∈ cookLevinProfileSubspace bp W :=
    hShiftMlproj bp S hSlen shift hshiftvars
      (iterDerivList S ((cookLevinFactorList M n hn htb hns).get i))
      hg_prod_witness
  -- Step 4: rewrite the goal in the canonical `MultilinearSPDP` form.
  -- `MultilinearSPDP.mlProj` and `SPDP.iterDerivList` are
  -- aliases for the `SPDP`-namespace / Mathlib definitions, so the
  -- goal reduces to `hClosureApp` by definitional equality.
  change MultilinearSPDP.mlProj
      (shift * SPDP.iterDerivList S
        ((cookLevinFactorList M n hn htb hns).get i))
    ∈ cookLevinProfileSubspace bp W
  exact hClosureApp

/-! ## Corollary: existential form of the appropriate `bp` condition

A more convenient call-site form: rather than pin `bp` in advance to
`singletonBooleanityProfile S`, one can expose the existential "∃ bp,
…" over the bounded profile satisfying the shape condition. This is
the "appropriate bp" form used in the Route C ⇒ Route A translation.

The proof inlines the full closure composition (rather than routing
through the main theorem's placeholder `hbp_shape` argument), yielding
a zero-shape-hypothesis form of the result. -/

/-- **Existential appropriate-bp version.**

For every cookLevinQ parameter tuple, every booleanity factor index
`i`, and every bounded `(S, shift)` pair, there exists a bounded
profile `bp` (whose histogram is `singletonBooleanityProfile S`) such
that the SPDP row lies in `cookLevinProfileSubspace bp (concreteW …)`. -/
theorem booleanity_row_mem_profileSubspace_exists_bp
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hFactor : CookLevinFactorMemPerType M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hDerivClos : DerivClosurePerType (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hShiftMlproj : PerTypeShiftMlprojClosure (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : cookLevinConstraintType M n hn htb hns i
            = ConstraintType.booleanity)
    (S : List (Fin n)) (hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (hshiftvars : shift.vars ⊆ S.toFinset) :
    ∃ bp : BoundedProfile (Nat.log 2 n),
      bp.toHistogram = singletonBooleanityProfile S ∧
      MultilinearSPDP.mlProj
          (shift * SPDP.iterDerivList S
            ((cookLevinFactorList M n hn htb hns).get i))
        ∈ cookLevinProfileSubspace bp
            (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) := by
  classical
  -- Build the bounded profile.
  have hbp_prop : ∀ τ, singletonBooleanityProfile (n := n) S τ ≤ Nat.log 2 n := by
    intro τ
    by_cases hτ : τ = ConstraintType.booleanity
    · subst hτ
      rw [singletonBooleanityProfile_booleanity]
      exact hSlen
    · rw [singletonBooleanityProfile_not_booleanity S τ hτ]
      exact Nat.zero_le _
  let bp : BoundedProfile (Nat.log 2 n) :=
    ⟨singletonBooleanityProfile S, hbp_prop⟩
  -- Abbreviations.
  set W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ with hW_def
  -- H3+H4 transport.
  have hDerivMem :
      iterDerivList S ((cookLevinFactorList M n hn htb hns).get i)
        ∈ W ConstraintType.booleanity :=
    iterDerivList_factor_mem_W
      M n hn htb hns W hFactor hDerivClos i
      ConstraintType.booleanity hi S hSlen
  -- Singleton witness.
  have hg_prod_witness :
      ∃ (L : ℕ) (factors : Fin L → MvPolynomial (Fin n) ℚ)
        (constraintType : Fin L → ConstraintType)
        (d : Fin L → List (Fin n)),
        (∀ j, ∀ v ∈ d j, v ∈ S) ∧
        (∀ j, iterDerivList (d j) (factors j) ∈ W (constraintType j)) ∧
        iterDerivList S ((cookLevinFactorList M n hn htb hns).get i)
          = Finset.univ.prod (fun j => iterDerivList (d j) (factors j)) ∧
        derivCountProfile constraintType d = bp.toHistogram ∧
        ∑ j : Fin L, (d j).length ≤ S.length := by
    refine ⟨1,
      fun _ : Fin 1 => (cookLevinFactorList M n hn htb hns).get i,
      fun _ : Fin 1 => ConstraintType.booleanity,
      fun _ : Fin 1 => S,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro _ v hv; exact hv
    · intro _; exact hDerivMem
    · simp
    · rw [derivCountProfile_singleton_booleanity]
      rfl
    · simp
  -- Final closure.
  have hClosureApp :
      mlProj (shift *
          iterDerivList S ((cookLevinFactorList M n hn htb hns).get i))
        ∈ cookLevinProfileSubspace bp W :=
    hShiftMlproj bp S hSlen shift hshiftvars
      (iterDerivList S ((cookLevinFactorList M n hn htb hns).get i))
      hg_prod_witness
  -- Package.
  refine ⟨bp, rfl, ?_⟩
  change MultilinearSPDP.mlProj
      (shift * SPDP.iterDerivList S
        ((cookLevinFactorList M n hn htb hns).get i))
    ∈ cookLevinProfileSubspace bp W
  exact hClosureApp

/-! ## Kernel-only axiom trace

The deliverables should depend only on
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms booleanity_row_mem_profileSubspace
#print axioms booleanity_row_mem_profileSubspace_exists_bp

end PallLean.Paper93.Direct
