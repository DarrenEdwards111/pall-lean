/-
  PaperFaithfulCompilation.lean — u/v variable split for Path A
  ===============================================================

  ## Paper reference

  Paper `p vs np1.pdf`, §§6, 29 (Theorem 203, Lemma 204, Lemma 205,
  Definition 7):

  Paper's polynomial compilation distinguishes two variable types:
  - **u**: clause-sheet variables (input x_i, selectors z_C)
  - **v**: tableau variables (tape bits b_{t,i}, state indicators s_{t,q},
    head positions h_{t,i}, with t ∈ [0, T], i ∈ [0, S])

  The compiled polynomial P_{M,n}(u, v) spans both. The coupled sheet
  Q^×_Φ(u, z) is defined over clause-sheet variables only (no tableau),
  via `Q^×_Φ = ∏_C (1 - z_C · V_C(x)²)`.

  Lemma 205: `Π_Φ := (basis) ∘ (affine relabel) ∘ (restriction) ∘ (projection)`
  where restriction fixes v to constants and projection extracts u.

  ## Rationale for this refactor

  The existing `cook_levin_compilation` uses a flat `Fin n` variable space
  (no u/v split), making rank bounds conflate:
  - `compiled_np_lower_bound_any_dtm` (axiom-free): `rank(compiledPoly) ≥ C(n/3, log n)`
  - `spdp_profile_generators` (false axiom): `rank(compiledPoly) ≤ (log n + 1)^12`

  These are incompatible BECAUSE they're stated about the same polynomial
  object. The paper reconciles by giving them to different objects:
  P_{M,n} (with tableau) vs. Q^×_Φ (clause-sheet only).

  This file introduces the u/v split framework so the P-side and
  NP-side bounds apply to clearly distinct polynomial objects.

  ## Status: ON-CHAIN scaffolding — axiom-free, no sorry.
-/

import PallLean.SPDPDefs
import PallLean.MultilinearSPDP
import PallLean.TuringMachine
import PallLean.PiStarConcrete
import PallLean.GaugeMonotonicity
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace PaperFaithfulCompilation

open MvPolynomial TuringMachine

/-! ## Section 1: The u/v variable split -/

/-- **UVSplit**: a partition of a variable index set into clause-sheet (`u`)
and tableau (`v`) parts. The total variable count is `numU + numV`.

Concrete instantiation for Cook-Levin:
- `numU = n` (input/clause-sheet variables)
- `numV = poly(n)` (tableau: tape × state × head × time)
-/
structure UVSplit where
  numU : ℕ
  numV : ℕ

/-- Total variable count. -/
def UVSplit.total (σ : UVSplit) : ℕ := σ.numU + σ.numV

/-- The total variable index type as `Fin (numU + numV)`. -/
abbrev UVSplit.Idx (σ : UVSplit) : Type := Fin σ.total

/-- Injection of u-indices into the total index space. -/
def UVSplit.inlU (σ : UVSplit) (i : Fin σ.numU) : σ.Idx :=
  ⟨i.val, by
    unfold UVSplit.total
    have := i.isLt
    omega⟩

/-- Injection of v-indices into the total index space. -/
def UVSplit.inlV (σ : UVSplit) (j : Fin σ.numV) : σ.Idx :=
  ⟨σ.numU + j.val, by
    unfold UVSplit.total
    have := j.isLt
    omega⟩

/-- Decide whether a total index is a u-index. -/
def UVSplit.isU (σ : UVSplit) (k : σ.Idx) : Prop := k.val < σ.numU

instance UVSplit.isU_decidable (σ : UVSplit) : DecidablePred σ.isU :=
  fun k => Nat.decLt _ _

/-- Extract the u-index if `k.isU`, else return a default. Helper for splits. -/
def UVSplit.toUIdx? (σ : UVSplit) (k : σ.Idx) : Option (Fin σ.numU) :=
  if h : k.val < σ.numU then some ⟨k.val, h⟩ else none

/-- Extract the v-index if `¬ k.isU`. -/
def UVSplit.toVIdx? (σ : UVSplit) (k : σ.Idx) : Option (Fin σ.numV) :=
  if h : σ.numU ≤ k.val then
    if h' : k.val - σ.numU < σ.numV then
      some ⟨k.val - σ.numU, h'⟩
    else none
  else none

/-! ## Section 2: The `keep u / restrict v` predicate -/

/-- **Keep-u predicate**: keep clause-sheet (u) variables, substitute tableau
(v) variables. This is the paper's Definition 6(i)/(ii) at the predicate
level: the `keep` underlying the `piZero` construction of Π_Φ. -/
def keepU (σ : UVSplit) : σ.Idx → Prop := σ.isU

instance keepU_decidable (σ : UVSplit) : DecidablePred (keepU σ) :=
  UVSplit.isU_decidable σ

/-- A u-index is kept: `keepU σ (inlU i)` always holds. -/
theorem keepU_inlU (σ : UVSplit) (i : Fin σ.numU) :
    keepU σ (σ.inlU i) := by
  show (σ.inlU i).val < σ.numU
  exact i.isLt

/-- A v-index is NOT kept: `keepU σ (inlV j)` always fails. -/
theorem not_keepU_inlV (σ : UVSplit) (j : Fin σ.numV) :
    ¬ keepU σ (σ.inlV j) := by
  show ¬ (σ.inlV j).val < σ.numU
  show ¬ (σ.numU + j.val) < σ.numU
  omega

/-! ## Section 3: Ambient cardinality sanity -/

/-- `numU ≤ total`. -/
theorem numU_le_total (σ : UVSplit) : σ.numU ≤ σ.total := by
  unfold UVSplit.total; omega

/-- `numV ≤ total`. -/
theorem numV_le_total (σ : UVSplit) : σ.numV ≤ σ.total := by
  unfold UVSplit.total; omega

/-- The u-inclusion is injective. -/
theorem inlU_injective (σ : UVSplit) : Function.Injective σ.inlU := by
  intro i j h
  have : (σ.inlU i).val = (σ.inlU j).val := congrArg Fin.val h
  exact Fin.ext this

/-- The v-inclusion is injective. -/
theorem inlV_injective (σ : UVSplit) : Function.Injective σ.inlV := by
  intro i j h
  have : (σ.inlV i).val = (σ.inlV j).val := congrArg Fin.val h
  show i = j
  apply Fin.ext
  show i.val = j.val
  have hi : (σ.inlV i).val = σ.numU + i.val := rfl
  have hj : (σ.inlV j).val = σ.numU + j.val := rfl
  omega

/-- The u- and v-injections have disjoint images. -/
theorem inlU_inlV_disjoint (σ : UVSplit) (i : Fin σ.numU) (j : Fin σ.numV) :
    σ.inlU i ≠ σ.inlV j := by
  intro heq
  have := congrArg Fin.val heq
  have hi : (σ.inlU i).val = i.val := rfl
  have hj : (σ.inlV j).val = σ.numU + j.val := rfl
  have hilt : i.val < σ.numU := i.isLt
  omega

/-! ## Section 4: Polynomial objects over the split

Two key polynomial types:
- `PMnPoly`: the compiled polynomial `P_{M,n}(u, v)` over all total variables
- `CoupledSheetPoly`: the coupled sheet `Q^×_Φ(u)` over u-variables only -/

/-- **Compiled polynomial over UVSplit**. Ambient type for `P_{M,n}(u, v)`. -/
abbrev PMnPoly (σ : UVSplit) : Type := MvPolynomial σ.Idx ℚ

/-- **Coupled sheet polynomial** over u-variables only. Type for `Q^×_Φ(u)`. -/
abbrev CoupledSheetPoly (σ : UVSplit) : Type := MvPolynomial (Fin σ.numU) ℚ

/-- **Embed a coupled-sheet polynomial into the ambient PMn space** via
the u-injection `inlU`. This realizes `Q^×_Φ(u)` as a special `P_{M,n}(u, v)`
that happens to not depend on v. -/
noncomputable def CoupledSheetPoly.embed (σ : UVSplit) (q : CoupledSheetPoly σ) :
    PMnPoly σ :=
  MvPolynomial.rename σ.inlU q

/-- `embed` is a ℚ-linear map. -/
theorem embed_linear (σ : UVSplit) :
    ∃ φ : CoupledSheetPoly σ →ₗ[ℚ] PMnPoly σ,
      ∀ q, φ q = CoupledSheetPoly.embed σ q :=
  ⟨(MvPolynomial.rename σ.inlU).toLinearMap, fun q => by
    show (MvPolynomial.rename σ.inlU).toLinearMap q = MvPolynomial.rename σ.inlU q
    rfl⟩

/-- `embed 0 = 0`. -/
theorem embed_zero (σ : UVSplit) :
    CoupledSheetPoly.embed σ 0 = 0 := by
  unfold CoupledSheetPoly.embed
  exact map_zero _

/-- `embed` preserves addition. -/
theorem embed_add (σ : UVSplit) (q r : CoupledSheetPoly σ) :
    CoupledSheetPoly.embed σ (q + r) =
      CoupledSheetPoly.embed σ q + CoupledSheetPoly.embed σ r := by
  unfold CoupledSheetPoly.embed
  exact map_add _ q r

/-- `embed` preserves multiplication (it's a ring hom). -/
theorem embed_mul (σ : UVSplit) (q r : CoupledSheetPoly σ) :
    CoupledSheetPoly.embed σ (q * r) =
      CoupledSheetPoly.embed σ q * CoupledSheetPoly.embed σ r := by
  unfold CoupledSheetPoly.embed
  exact map_mul _ q r

/-! ## Section 5: The Π_Φ gauge over a UVSplit

Paper Lemma 205: `Π_Φ = (basis) ∘ (affine relabel) ∘ (restriction) ∘ (projection)`.

We realize Π_Φ in the paper-faithful split setting as `piZero (keepU σ)`:
the "restriction" substitutes v-variables to 0, and the "projection"
keeps u-variables.

`(basis)` and `(affine relabel)` are (trivially) identity in our abstract
setup; a fully paper-faithful treatment would add a change-of-basis layer
(not essential for rank properties). -/

/-- **Π_Φ gauge** for a UVSplit: piZero with `keepU` predicate.
Paper's Lemma 205 gauge realized at the "restriction + projection" level. -/
noncomputable def piPhi (σ : UVSplit) :
    PMnPoly σ →ₗ[ℚ] PMnPoly σ :=
  PiStarConcrete.piZero (keepU σ)

/-- `piPhi` is a projection gauge (inherits from piZero). -/
theorem piPhi_isProjectionGauge (σ : UVSplit) :
    GaugeMonotonicity.IsProjectionGauge (piPhi σ) :=
  PiStarConcrete.piZero_isProjectionGauge (keepU σ)

/-- `piPhi` is rank-monotone over any block partition: this is the
paper-faithful rank monotonicity of Π_Φ (Lemma 205 output), at the
abstract SPDP level. -/
theorem piPhi_isRankMonotoneGauge (σ : UVSplit)
    (B : SPDP.BlockPartition σ.total) :
    GaugeMonotonicity.IsRankMonotoneGauge B (piPhi σ) :=
  PiStarConcrete.piZero_isRankMonotoneGauge (keepU σ) B

/-- `piPhi` evaluated on `X (inlU i)` returns `X (inlU i)` (u is kept). -/
theorem piPhi_X_u (σ : UVSplit) (i : Fin σ.numU) :
    piPhi σ (MvPolynomial.X (σ.inlU i)) = MvPolynomial.X (σ.inlU i) := by
  unfold piPhi
  rw [PiStarConcrete.piZero_X]
  rw [if_pos (keepU_inlU σ i)]

/-- `piPhi` evaluated on `X (inlV j)` returns `0` (v is substituted). -/
theorem piPhi_X_v (σ : UVSplit) (j : Fin σ.numV) :
    piPhi σ (MvPolynomial.X (σ.inlV j)) = 0 := by
  unfold piPhi
  rw [PiStarConcrete.piZero_X]
  rw [if_neg (not_keepU_inlV σ j)]

end PaperFaithfulCompilation
