/-
  PallLean/Paper93/Closure/PerTypeClosure.lean

  Paper §9 Lemma 31 closure composition layer — Agent I5 of 10 (parallel).

  ## Scope

  Agent H5 (`Paper93/Spanning/PerDerivativeSpanning.lean`, commit
  `0629d49`) left three hypotheses open on its way to the discharged
  `CookLevinPerTypeSpanning` bundle:

    * H3 (`CookLevinFactorMemPerType`) — per-factor ambient membership;
    * H4 (`DerivClosurePerType`)       — derivative closure of `W τ`;
    * `PerTypeShiftMlprojClosure`      — closure of `cookLevinProfileSubspace`
      under the SPDP generator construction `g ↦ mlProj (shift * g)`.

  Agent I5 of 10 discharges the third hypothesis, by composing the
  per-component closure properties on the `cookLevinProfileSubspace`:

    * (I1) **Product grouping**: if `g` is a product of per-factor
      derivatives each lying in `W (constraintType i)` and the
      derivative-count profile of that decomposition equals
      `bp.toHistogram`, then `g ∈ cookLevinProfileSubspace bp W`.
      This is the "product → symPower regrouping" step.

    * (I2) **Shift closure**: if `p ∈ cookLevinProfileSubspace bp W`
      and `shift.vars ⊆ S.toFinset` with `S.length ≤ Nat.log 2 n`, then
      `shift * p ∈ cookLevinProfileSubspace bp W`.

    * (I3) **mlProj closure**: if `p ∈ cookLevinProfileSubspace bp W`
      then `mlProj p ∈ cookLevinProfileSubspace bp W`.

  These three Prop-level interfaces are the I1/I2/I3 agents of the
  parallel cohort. Because none of I1–I4 are landed in repo at the
  time this file is produced, we take them as explicit Prop-level
  hypotheses; the composition is then a straightforward three-step
  chain through the closure properties, matching the pattern set by
  `cookLevinPerTypeSpanning_discharged`.

  The main theorem delivers

    `perTypeShiftMlprojClosure_discharged`
      (I1 I2 I3 inputs) : `PerTypeShiftMlprojClosure W`

  which is the Prop precisely expected by H5's
  `cookLevinPerTypeSpanning_discharged` hypothesis slot.

  ## Inputs taken as hypotheses (Prop-level)

  We expose I1, I2, I3 as three named Props:

    * `PerTypeProductGrouping W`
    * `PerTypeShiftClosure n W`
    * `PerTypeMlprojClosure n W`

  Each is the minimal-scope closure Prop sufficient to drive the
  composition; no algebraic content on `W` beyond the closure is used.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; all hypotheses are `Prop`-level inputs.
    * Verified by `lake build`.

  Expected `#print axioms`:  [propext, Classical.choice, Quot.sound].
-/
import PallLean.Paper93.Spanning.PerDerivativeSpanning

namespace PallLean.Paper93.Closure

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound SPDP MultilinearSPDP
open PallLean.Paper93 PallLean.Paper93.Spanning

/-! ## 1. I1: product grouping into the profile subspace

Given a product `g = ∏_i iterDerivList (d i) (factors i)` whose
per-factor derivatives each lie in the ambient `W (constraintType i)`,
and whose derivative-count profile matches the bounded profile
`bp.toHistogram`, `g` lies in `cookLevinProfileSubspace bp W`.

This is the "product → ∏_τ Sym^{h τ}(W τ)" regrouping step, i.e. the
re-expression of an `L`-fold product indexed by factor indices as an
element of the tensor-product submodule indexed by constraint types.

We take it as a Prop-level hypothesis here; the I1 agent is expected
to supply this content by a multilinear / Leibniz argument that
regroups the `i`-indexed product into `τ`-indexed symmetric powers,
using `derivCountProfile constraintType d = bp.toHistogram` to match
the per-type exponent. -/

/-- **I1 interface**: product grouping. Any `L`-fold product of
per-factor derivatives that matches `bp.toHistogram` as its derivative
-count profile lies in `cookLevinProfileSubspace bp W`. -/
def PerTypeProductGrouping {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (L : ℕ) (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (d : Fin L → List (Fin n))
    (_hd_elts : ∀ i, ∀ v ∈ d i, v ∈ S)
    (_hFactorMem : ∀ i, iterDerivList (d i) (factors i) ∈ W (constraintType i))
    (_hprof : derivCountProfile constraintType d = bp.toHistogram)
    (_hsum : ∑ i : Fin L, (d i).length ≤ S.length),
    (Finset.univ.prod (fun i => iterDerivList (d i) (factors i)))
      ∈ cookLevinProfileSubspace bp W

/-! ## 2. I2: shift closure of the profile subspace

The profile subspace is closed under multiplication by polynomials
whose variables are a subset of a bounded index list `S.toFinset`
(with `S.length ≤ Nat.log 2 n`). This is the "shift-by-polynomial"
closure step corresponding to the SPDP `shift` factor.

We take it as a Prop-level hypothesis; the I2 agent is expected to
supply this content by showing that the generating family of
`profileSubspace bp.toHistogram W` is closed under left-multiplication
by `shift`, using the polynomial ring structure. -/

/-- **I2 interface**: shift closure. Multiplication by a polynomial
`shift` with `shift.vars ⊆ S.toFinset` preserves membership in the
profile subspace. -/
def PerTypeShiftClosure {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (p : MvPolynomial (Fin n) ℚ)
    (_hp : p ∈ cookLevinProfileSubspace bp W),
    shift * p ∈ cookLevinProfileSubspace bp W

/-! ## 3. I3: mlProj closure of the profile subspace

The profile subspace is closed under the multilinear projection
operator `mlProj`. This is the "mlProj closure" step corresponding to
the `mlProj` wrapping in the SPDP generator.

We take it as a Prop-level hypothesis; the I3 agent is expected to
supply this content by showing that `mlProj` preserves the generating
family of `profileSubspace bp.toHistogram W`, typically via linearity
of `mlProj` and invariance of the generating set under multilinear
restriction. -/

/-- **I3 interface**: mlProj closure. The multilinear projection
`mlProj` preserves membership in the profile subspace. -/
def PerTypeMlprojClosure {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (p : MvPolynomial (Fin n) ℚ)
    (_hp : p ∈ cookLevinProfileSubspace bp W),
    mlProj p ∈ cookLevinProfileSubspace bp W

/-! ## 4. Main composition: I1 + I2 + I3 ⇒ `PerTypeShiftMlprojClosure`

The discharge of H5's `PerTypeShiftMlprojClosure` hypothesis is a
direct three-step composition:

    I1 regroups the `L`-fold product into the profile subspace;
    I2 multiplies by `shift`, preserving membership;
    I3 applies `mlProj`, preserving membership.

No further algebraic content is needed. -/

/-- **Main theorem (I5).**

Given the three closure interfaces I1 (product grouping), I2 (shift
closure), and I3 (mlProj closure), the H5 hypothesis
`PerTypeShiftMlprojClosure W` holds. -/
theorem perTypeShiftMlprojClosure_discharged {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hI1 : PerTypeProductGrouping (n := n) W)
    (hI2 : PerTypeShiftClosure (n := n) W)
    (hI3 : PerTypeMlprojClosure (n := n) W) :
    PerTypeShiftMlprojClosure (n := n) W := by
  classical
  intro bp S hSlen shift hshiftvars g hg_prod
  -- Unpack the existential witness of `hg_prod`.
  obtain ⟨L, factors, constraintType, d,
          hd_elts, hFactorMem, hg_prod_eq, hprof, hsum⟩ := hg_prod
  -- Step 1 (I1): the product lies in `cookLevinProfileSubspace bp W`.
  have hProdMem :
      (Finset.univ.prod (fun i => iterDerivList (d i) (factors i)))
        ∈ cookLevinProfileSubspace bp W :=
    hI1 bp S hSlen L factors constraintType d
        hd_elts hFactorMem hprof hsum
  -- Rewrite `g` as that product using `hg_prod_eq`.
  have hgMem : g ∈ cookLevinProfileSubspace bp W := by
    rw [hg_prod_eq]; exact hProdMem
  -- Step 2 (I2): multiply by `shift`, preserving membership.
  have hShiftMem : shift * g ∈ cookLevinProfileSubspace bp W :=
    hI2 bp S hSlen shift hshiftvars g hgMem
  -- Step 3 (I3): apply `mlProj`, preserving membership.
  exact hI3 bp (shift * g) hShiftMem

/-! ## 5. End-to-end composition with H5

Chaining `perTypeShiftMlprojClosure_discharged` (I5) with the H5
composition theorem `cookLevinPerTypeSpanning_discharged` produces
the full `CookLevinPerTypeSpanning` bundle from H3, H4, I1, I2, I3.

This is the single-call entry point that makes H5's three hypotheses
into two (H3 + H4) plus the three closure interfaces (I1, I2, I3). -/

/-- **Composition: H3 + H4 + I1 + I2 + I3 ⇒ `CookLevinPerTypeSpanning`.**

Given the H3 and H4 per-type bundles together with the I1/I2/I3
closure interfaces, H5's `cookLevinPerTypeSpanning_discharged` fires
unconditionally. -/
theorem cookLevinPerTypeSpanning_from_H3_H4_I1_I2_I3
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hFactor : CookLevinFactorMemPerType M n hn htb hns W)
    (hClosure : DerivClosurePerType (n := n) W)
    (hI1 : PerTypeProductGrouping (n := n) W)
    (hI2 : PerTypeShiftClosure (n := n) W)
    (hI3 : PerTypeMlprojClosure (n := n) W) :
    CookLevinPerTypeSpanning M n hn htb hns W :=
  cookLevinPerTypeSpanning_discharged
    M n hn htb hns W hFactor hClosure
    (perTypeShiftMlprojClosure_discharged W hI1 hI2 hI3)

/-! ## 6. End-to-end template-collapse bridge from H3 + H4 + I1 + I2 + I3

For caller convenience, we also expose the full end-to-end chain
from H3 + H4 + I1 + I2 + I3 (+ per-type dim ≤ 3 data) directly to
Agent B's template-collapse lemma. -/

/-- **End-to-end template-collapse from H3 + H4 + I1 + I2 + I3 + dim ≤ 3.**

Given H3, H4, I1, I2, I3, and the per-type finite-dimensionality /
dim ≤ 3 hypotheses on `W`, produces Agent B's
`CookLevinProfileTemplateCollapseLemmaBoundedProfile`. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_H3_H4_I1_I2_I3
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hFactor : CookLevinFactorMemPerType M n hn htb hns W)
    (hClosure : DerivClosurePerType (n := n) W)
    (hI1 : PerTypeProductGrouping (n := n) W)
    (hI2 : PerTypeShiftClosure (n := n) W)
    (hI3 : PerTypeMlprojClosure (n := n) W) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_H3_H4
    M n hn htb hns W hW_fin hW_dim hFactor hClosure
    (perTypeShiftMlprojClosure_discharged W hI1 hI2 hI3)

#print axioms perTypeShiftMlprojClosure_discharged
#print axioms cookLevinPerTypeSpanning_from_H3_H4_I1_I2_I3
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_H3_H4_I1_I2_I3

end PallLean.Paper93.Closure
