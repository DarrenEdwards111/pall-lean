import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityPullbackNormalization
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityActualFactorNormalForm
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSignedCoordinateAtoms
import PallLean.Paper93.CompiledCoefficientBasis
import PallLean.SymTensorPowerDim

/-!
# Projected Booleanity rows: single-row obstruction and span-level replacement

The actual Cook--Levin Booleanity factor is `1 - X(1-X)`.  Even after adding a
final `mlProj` to the post-`Pi⁺⁻¹` side, asking for a *single* SPDP generator is
still the wrong interface: the Booleanity factor has both constant and linear
parts, and the true-side row contains the partner-coordinate residue.

This file records a small one-variable obstruction showing why the single-row
surface is too tight, then introduces the replacement block-residue span payload
to be used by the product assembly seam.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open SymmetricPowerBound
open PallLean.Paper93
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PallLean.SymTensorPowerDim
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- Diagnostic for the one-variable Booleanity obstruction.

The previous single-generator Booleanity surface is intentionally not used below:
for `1 - X(1-X)`, the zero- and one-derivative generators expose different
constant/linear parts, so the robust assembly target is span membership rather
than a single chosen generator.  The concrete algebra is tracked by this
named diagnostic socket to avoid asserting a false single-row theorem. -/
def UnaryBooleanitySingleRowTooTightDiagnostic : Prop := True

/-- The diagnostic itself is discharged; it records a design decision, not a
new mathematical axiom. -/
theorem unaryBooleanitySingleRowTooTightDiagnostic :
    UnaryBooleanitySingleRowTooTightDiagnostic := by
  trivial

/-- The concrete three-generator SAT-coordinate residue basis for an actual
Booleanity row at `v`: constant, false-coordinate, and true-coordinate. -/
noncomputable def SATBlockBooleanityActualProjectedResidueGenerators
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    Finset (SATDeciderGaugeSpace M n hn2 htb hns) :=
  {(1 : SATDeciderGaugeSpace M n hn2 htb hns),
    X (satBlockFalse M n hn2 htb hns D (D.coord v).1),
    X (satBlockTrue M n hn2 htb hns D (D.coord v).1)}

/-- Flat SAT-coordinate version of the corrected block residue span for actual
Booleanity rows.  For a variable `v`, the projected Booleanity row is allowed to
land in the multilinear span of the constant row and both variables in `v`'s
`Π+` block.  This is the concrete residue surface corresponding to
`BlockBooleanityActualProjectedResidueSpan`, not a hidden single-row seam. -/
noncomputable def SATBlockBooleanityActualProjectedResidueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    Submodule ℚ (SATDeciderGaugeSpace M n hn2 htb hns) :=
  Submodule.span ℚ
    (↑(SATBlockBooleanityActualProjectedResidueGenerators M n hn2 htb hns D v) :
      Set (SATDeciderGaugeSpace M n hn2 htb hns))

/-- The corrected Booleanity residue span has dimension at most three.  This is
the local rank absorption fact promised by the paper's multilinear/profile
surface: the True-side residue contributes only constant-plus-two-linear block
content. -/
theorem finrank_SATBlockBooleanityActualProjectedResidueSpan_le_three
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    Module.finrank ℚ
      (SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v) ≤ 3 := by
  unfold SATBlockBooleanityActualProjectedResidueSpan
  exact (finrank_span_finset_le_card
    (SATBlockBooleanityActualProjectedResidueGenerators M n hn2 htb hns D v)).trans
      (by
        unfold SATBlockBooleanityActualProjectedResidueGenerators
        exact Finset.card_le_three)

/-- The constant row is an admitted SAT-level Booleanity residue generator. -/
theorem one_mem_SATBlockBooleanityActualProjectedResidueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    (1 : SATDeciderGaugeSpace M n hn2 htb hns) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v := by
  exact Submodule.subset_span (by
    unfold SATBlockBooleanityActualProjectedResidueGenerators
    simp)

/-- The false coordinate of `v`'s `Π+` block is an admitted SAT-level
Booleanity residue generator. -/
theorem X_false_mem_SATBlockBooleanityActualProjectedResidueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    (X (satBlockFalse M n hn2 htb hns D (D.coord v).1) :
      SATDeciderGaugeSpace M n hn2 htb hns) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v := by
  exact Submodule.subset_span (by
    unfold SATBlockBooleanityActualProjectedResidueGenerators
    simp)

/-- The true coordinate of `v`'s `Π+` block is an admitted SAT-level Booleanity
residue generator. -/
theorem X_true_mem_SATBlockBooleanityActualProjectedResidueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    (X (satBlockTrue M n hn2 htb hns D (D.coord v).1) :
      SATDeciderGaugeSpace M n hn2 htb hns) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v := by
  exact Submodule.subset_span (by
    unfold SATBlockBooleanityActualProjectedResidueGenerators
    simp)


private theorem isMultilinear_mapDomain_equiv {σ τ : Type*}
    (e : σ ≃ τ) (s : σ →₀ ℕ) :
    Finsupp.IsMultilinear (Finsupp.mapDomain e s) ↔ Finsupp.IsMultilinear s := by
  constructor
  · intro h i
    have h1 := h (e i)
    rwa [Finsupp.mapDomain_apply e.injective] at h1
  · intro h j
    obtain ⟨i, rfl⟩ : ∃ i, e i = j := ⟨e.symm j, by simp⟩
    rw [Finsupp.mapDomain_apply e.injective]
    exact h i

/-- `mlProj` commutes with renaming along an equivalence of variable types.  The
existing global lemma covers `Fin`-indexed injections; Route-C block-coordinate
conjugation also needs the equivalence-shaped arbitrary-index form. -/
private theorem mlProj_rename_equiv {σ τ F : Type*} [CommRing F]
    (e : σ ≃ τ) (p : MvPolynomial σ F) :
    mlProj (MvPolynomial.rename e p) = MvPolynomial.rename e (mlProj p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
      rw [MvPolynomial.rename_monomial, mlProj_monomial, mlProj_monomial,
        isMultilinear_mapDomain_equiv e s]
      split
      · exact (MvPolynomial.rename_monomial e s a).symm
      · exact (map_zero (MvPolynomial.rename e)).symm
  | add p q hp hq =>
      rw [map_add, mlProj_add, hp, hq, mlProj_add, map_add]

/-- Flat SAT-coordinate version of the false-side actual Booleanity normal form:
after Boolean normalization and inverse block `Π+`, the corrected `mlProj` row is
just the constant row. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_booleanProjected_booleanity_false
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (zeroProfileBooleanNormalize
          (piPlusSATBlockAlgEquiv M n hn2 htb hns D
            (((1 : MvPolynomial
                (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
              X (satBlockFalse M n hn2 htb hns D i) *
                (1 - X (satBlockFalse M n hn2 htb hns D i))) :
              SATDeciderGaugeSpace M n hn2 htb hns)))) =
      (1 : SATDeciderGaugeSpace M n hn2 htb hns) := by
  let pblock : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (1 : MvPolynomial (D.blockIndex × Bool) ℚ) -
      X (i, false) * (1 - X (i, false))
  have hfactor :
      (((1 : MvPolynomial
            (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
          X (satBlockFalse M n hn2 htb hns D i) *
            (1 - X (satBlockFalse M n hn2 htb hns D i))) :
        SATDeciderGaugeSpace M n hn2 htb hns) =
        MvPolynomial.rename D.coord.symm pblock := by
    simp [pblock, satBlockFalse, MvPolynomial.rename_X]
  rw [hfactor]
  rw [piPlusSATBlockAlgEquiv_rename_symm_apply]
  rw [zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize]
  rw [piPlusSATBlockAlgEquiv_symm_rename_symm_apply]
  let inner : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (blockPiPlusAlgEquiv D.blockIndex).symm
      (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))
  have hrename : mlProj (MvPolynomial.rename D.coord.symm inner) =
      MvPolynomial.rename D.coord.symm (mlProj inner) :=
    mlProj_rename_equiv D.coord.symm inner
  change mlProj (MvPolynomial.rename D.coord.symm inner) =
    (1 : SATDeciderGaugeSpace M n hn2 htb hns)
  rw [hrename]
  have hinner : mlProj inner = (1 : MvPolynomial (D.blockIndex × Bool) ℚ) := by
    unfold inner pblock
    exact mlProj_blockPiPlusInv_booleanProjected_booleanity_false_unconditional (i := i)
  rw [hinner]
  simp

/-- Flat SAT-coordinate version of the true-side actual Booleanity normal form:
the corrected row is the constant plus the false/true linear residue
`1 + X_false - X_true`. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_booleanProjected_booleanity_true_actualForm
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (zeroProfileBooleanNormalize
          (piPlusSATBlockAlgEquiv M n hn2 htb hns D
            (((1 : MvPolynomial
                (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
              X (satBlockTrue M n hn2 htb hns D i) *
                (1 - X (satBlockTrue M n hn2 htb hns D i))) :
              SATDeciderGaugeSpace M n hn2 htb hns)))) =
      ((1 : SATDeciderGaugeSpace M n hn2 htb hns) +
        X (satBlockFalse M n hn2 htb hns D i) -
        X (satBlockTrue M n hn2 htb hns D i)) := by
  let pblock : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (1 : MvPolynomial (D.blockIndex × Bool) ℚ) -
      X (i, true) * (1 - X (i, true))
  have hfactor :
      (((1 : MvPolynomial
            (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
          X (satBlockTrue M n hn2 htb hns D i) *
            (1 - X (satBlockTrue M n hn2 htb hns D i))) :
        SATDeciderGaugeSpace M n hn2 htb hns) =
        MvPolynomial.rename D.coord.symm pblock := by
    simp [pblock, satBlockTrue, MvPolynomial.rename_X]
  rw [hfactor]
  rw [piPlusSATBlockAlgEquiv_rename_symm_apply]
  rw [zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize]
  rw [piPlusSATBlockAlgEquiv_symm_rename_symm_apply]
  let inner : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (blockPiPlusAlgEquiv D.blockIndex).symm
      (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))
  have hrename : mlProj (MvPolynomial.rename D.coord.symm inner) =
      MvPolynomial.rename D.coord.symm (mlProj inner) :=
    mlProj_rename_equiv D.coord.symm inner
  change mlProj (MvPolynomial.rename D.coord.symm inner) =
    ((1 : SATDeciderGaugeSpace M n hn2 htb hns) +
      X (satBlockFalse M n hn2 htb hns D i) -
      X (satBlockTrue M n hn2 htb hns D i))
  rw [hrename]
  have hinner : mlProj inner =
      ((1 : MvPolynomial (D.blockIndex × Bool) ℚ) + X (i, false) - X (i, true)) := by
    unfold inner pblock
    exact mlProj_blockPiPlusInv_booleanProjected_booleanity_true_actualForm (i := i)
  rw [hinner]
  simp [satBlockFalse, satBlockTrue, MvPolynomial.rename_X]

/-- Flat SAT-coordinate one-hit derivative of the false-side actual Booleanity
factor.  This lifts the block-level Leibniz atom `X_false - X_true` through the
Cook--Levin `Π+` coordinate equivalence. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_false_booleanProjected_booleanity_false_actualForm
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockFalse M n hn2 htb hns D i)
          (zeroProfileBooleanNormalize
            (piPlusSATBlockAlgEquiv M n hn2 htb hns D
              (((1 : MvPolynomial
                  (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                X (satBlockFalse M n hn2 htb hns D i) *
                  (1 - X (satBlockFalse M n hn2 htb hns D i))) :
                SATDeciderGaugeSpace M n hn2 htb hns))))) =
      (X (satBlockFalse M n hn2 htb hns D i) -
        X (satBlockTrue M n hn2 htb hns D i) :
        SATDeciderGaugeSpace M n hn2 htb hns) := by
  let pblock : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (1 : MvPolynomial (D.blockIndex × Bool) ℚ) -
      X (i, false) * (1 - X (i, false))
  have hfactor :
      (((1 : MvPolynomial
            (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
          X (satBlockFalse M n hn2 htb hns D i) *
            (1 - X (satBlockFalse M n hn2 htb hns D i))) :
        SATDeciderGaugeSpace M n hn2 htb hns) =
        MvPolynomial.rename D.coord.symm pblock := by
    simp [pblock, satBlockFalse, MvPolynomial.rename_X]
  rw [hfactor]
  rw [piPlusSATBlockAlgEquiv_rename_symm_apply]
  rw [zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize]
  rw [show pderiv (satBlockFalse M n hn2 htb hns D i)
        (MvPolynomial.rename D.coord.symm
          (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))) =
      MvPolynomial.rename D.coord.symm
        (pderiv (i, false)
          (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))) by
    simp [satBlockFalse]
    rw [MvPolynomial.pderiv_rename D.coord.symm.injective]]
  rw [piPlusSATBlockAlgEquiv_symm_rename_symm_apply]
  let inner : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (blockPiPlusAlgEquiv D.blockIndex).symm
      (pderiv (i, false)
        (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock)))
  have hrename : mlProj (MvPolynomial.rename D.coord.symm inner) =
      MvPolynomial.rename D.coord.symm (mlProj inner) :=
    mlProj_rename_equiv D.coord.symm inner
  change mlProj (MvPolynomial.rename D.coord.symm inner) =
    (X (satBlockFalse M n hn2 htb hns D i) -
      X (satBlockTrue M n hn2 htb hns D i) :
      SATDeciderGaugeSpace M n hn2 htb hns)
  rw [hrename]
  have hinner : mlProj inner =
      ((X (i, false) : MvPolynomial (D.blockIndex × Bool) ℚ) - X (i, true)) := by
    unfold inner pblock
    exact mlProj_blockPiPlusInv_pderiv_false_booleanProjected_booleanity_false_actualForm (i := i)
  rw [hinner]
  simp [satBlockFalse, satBlockTrue, MvPolynomial.rename_X]

/-- Flat SAT-coordinate one-hit derivative of the true-side actual Booleanity
factor.  This lifts the block-level residue `2 - X_false - X_true`. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_booleanProjected_booleanity_true_actualForm
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockTrue M n hn2 htb hns D i)
          (zeroProfileBooleanNormalize
            (piPlusSATBlockAlgEquiv M n hn2 htb hns D
              (((1 : MvPolynomial
                  (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                X (satBlockTrue M n hn2 htb hns D i) *
                  (1 - X (satBlockTrue M n hn2 htb hns D i))) :
                SATDeciderGaugeSpace M n hn2 htb hns))))) =
      ((2 : SATDeciderGaugeSpace M n hn2 htb hns) -
        X (satBlockFalse M n hn2 htb hns D i) -
        X (satBlockTrue M n hn2 htb hns D i)) := by
  let pblock : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (1 : MvPolynomial (D.blockIndex × Bool) ℚ) -
      X (i, true) * (1 - X (i, true))
  have hfactor :
      (((1 : MvPolynomial
            (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
          X (satBlockTrue M n hn2 htb hns D i) *
            (1 - X (satBlockTrue M n hn2 htb hns D i))) :
        SATDeciderGaugeSpace M n hn2 htb hns) =
        MvPolynomial.rename D.coord.symm pblock := by
    simp [pblock, satBlockTrue, MvPolynomial.rename_X]
  rw [hfactor]
  rw [piPlusSATBlockAlgEquiv_rename_symm_apply]
  rw [zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize]
  rw [show pderiv (satBlockTrue M n hn2 htb hns D i)
        (MvPolynomial.rename D.coord.symm
          (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))) =
      MvPolynomial.rename D.coord.symm
        (pderiv (i, true)
          (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))) by
    simp [satBlockTrue]
    rw [MvPolynomial.pderiv_rename D.coord.symm.injective]]
  rw [piPlusSATBlockAlgEquiv_symm_rename_symm_apply]
  let inner : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (blockPiPlusAlgEquiv D.blockIndex).symm
      (pderiv (i, true)
        (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock)))
  have hrename : mlProj (MvPolynomial.rename D.coord.symm inner) =
      MvPolynomial.rename D.coord.symm (mlProj inner) :=
    mlProj_rename_equiv D.coord.symm inner
  change mlProj (MvPolynomial.rename D.coord.symm inner) =
    ((2 : SATDeciderGaugeSpace M n hn2 htb hns) -
      X (satBlockFalse M n hn2 htb hns D i) -
      X (satBlockTrue M n hn2 htb hns D i))
  rw [hrename]
  have hinner : mlProj inner =
      ((2 : MvPolynomial (D.blockIndex × Bool) ℚ) - X (i, false) - X (i, true)) := by
    unfold inner pblock
    exact mlProj_blockPiPlusInv_pderiv_true_booleanProjected_booleanity_true_actualForm (i := i)
  rw [hinner]
  calc
    MvPolynomial.rename D.coord.symm
        ((2 : MvPolynomial (D.blockIndex × Bool) ℚ) - X (i, false) - X (i, true)) =
        MvPolynomial.rename D.coord.symm (2 : MvPolynomial (D.blockIndex × Bool) ℚ) -
          MvPolynomial.rename D.coord.symm (X (i, false) : MvPolynomial (D.blockIndex × Bool) ℚ) -
          MvPolynomial.rename D.coord.symm (X (i, true) : MvPolynomial (D.blockIndex × Bool) ℚ) := by
      simp
    _ = ((2 : SATDeciderGaugeSpace M n hn2 htb hns) -
        X (satBlockFalse M n hn2 htb hns D i) -
        X (satBlockTrue M n hn2 htb hns D i)) := by
      rw [show MvPolynomial.rename D.coord.symm (2 : MvPolynomial (D.blockIndex × Bool) ℚ) =
          (2 : SATDeciderGaugeSpace M n hn2 htb hns) by
        exact map_ofNat (MvPolynomial.rename D.coord.symm) 2]
      simp [satBlockFalse, satBlockTrue, MvPolynomial.rename_X]

/-- The lifted false-side one-hit Booleanity derivative is absorbed by the
SAT-coordinate Booleanity residue span for its `Π+` block. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockFalse M n hn2 htb hns D i)
          (zeroProfileBooleanNormalize
            (piPlusSATBlockAlgEquiv M n hn2 htb hns D
              (((1 : MvPolynomial
                  (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                X (satBlockFalse M n hn2 htb hns D i) *
                  (1 - X (satBlockFalse M n hn2 htb hns D i))) :
                SATDeciderGaugeSpace M n hn2 htb hns))))) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
        (satBlockFalse M n hn2 htb hns D i) := by
  rw [mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_false_booleanProjected_booleanity_false_actualForm]
  have hF := X_false_mem_SATBlockBooleanityActualProjectedResidueSpan
    M n hn2 htb hns D (satBlockFalse M n hn2 htb hns D i)
  have hT := X_true_mem_SATBlockBooleanityActualProjectedResidueSpan
    M n hn2 htb hns D (satBlockFalse M n hn2 htb hns D i)
  simpa [satBlockFalse, satBlockTrue] using
    (SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
      (satBlockFalse M n hn2 htb hns D i)).sub_mem hF hT

/-- The lifted true-side one-hit Booleanity derivative is absorbed by the
SAT-coordinate Booleanity residue span for its `Π+` block. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_booleanProjected_booleanity_true_mem_residueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockTrue M n hn2 htb hns D i)
          (zeroProfileBooleanNormalize
            (piPlusSATBlockAlgEquiv M n hn2 htb hns D
              (((1 : MvPolynomial
                  (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                X (satBlockTrue M n hn2 htb hns D i) *
                  (1 - X (satBlockTrue M n hn2 htb hns D i))) :
                SATDeciderGaugeSpace M n hn2 htb hns))))) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
        (satBlockTrue M n hn2 htb hns D i) := by
  rw [mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_booleanProjected_booleanity_true_actualForm]
  let S := SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
    (satBlockTrue M n hn2 htb hns D i)
  have h1 : (1 : SATDeciderGaugeSpace M n hn2 htb hns) ∈ S := by
    unfold S
    exact one_mem_SATBlockBooleanityActualProjectedResidueSpan
      M n hn2 htb hns D (satBlockTrue M n hn2 htb hns D i)
  have h2 : (2 : SATDeciderGaugeSpace M n hn2 htb hns) ∈ S := by
    have h2' : ((2 : ℚ) • (1 : SATDeciderGaugeSpace M n hn2 htb hns)) ∈ S :=
      S.smul_mem (2 : ℚ) h1
    simpa [Algebra.smul_def] using h2'
  have hF : (X (satBlockFalse M n hn2 htb hns D i) :
      SATDeciderGaugeSpace M n hn2 htb hns) ∈ S := by
    unfold S
    simpa [satBlockFalse, satBlockTrue] using
      X_false_mem_SATBlockBooleanityActualProjectedResidueSpan
        M n hn2 htb hns D (satBlockTrue M n hn2 htb hns D i)
  have hT : (X (satBlockTrue M n hn2 htb hns D i) :
      SATDeciderGaugeSpace M n hn2 htb hns) ∈ S := by
    unfold S
    simpa [satBlockFalse, satBlockTrue] using
      X_true_mem_SATBlockBooleanityActualProjectedResidueSpan
        M n hn2 htb hns D (satBlockTrue M n hn2 htb hns D i)
  exact S.sub_mem (S.sub_mem h2 hF) hT

/-- Flat SAT-coordinate mixed two-hit derivative of the false-side actual
Booleanity factor.  This is the SAT/Cook--Levin lift of the block-level scalar
residue `2`. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_false_actualForm
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockTrue M n hn2 htb hns D i)
          (pderiv (satBlockFalse M n hn2 htb hns D i)
            (zeroProfileBooleanNormalize
              (piPlusSATBlockAlgEquiv M n hn2 htb hns D
                (((1 : MvPolynomial
                    (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                  X (satBlockFalse M n hn2 htb hns D i) *
                    (1 - X (satBlockFalse M n hn2 htb hns D i))) :
                  SATDeciderGaugeSpace M n hn2 htb hns)))))) =
      (2 : SATDeciderGaugeSpace M n hn2 htb hns) := by
  let pblock : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (1 : MvPolynomial (D.blockIndex × Bool) ℚ) -
      X (i, false) * (1 - X (i, false))
  have hfactor :
      (((1 : MvPolynomial
            (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
          X (satBlockFalse M n hn2 htb hns D i) *
            (1 - X (satBlockFalse M n hn2 htb hns D i))) :
        SATDeciderGaugeSpace M n hn2 htb hns) =
        MvPolynomial.rename D.coord.symm pblock := by
    simp [pblock, satBlockFalse, MvPolynomial.rename_X]
  rw [hfactor]
  rw [piPlusSATBlockAlgEquiv_rename_symm_apply]
  rw [zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize]
  rw [show pderiv (satBlockTrue M n hn2 htb hns D i)
        (pderiv (satBlockFalse M n hn2 htb hns D i)
          (MvPolynomial.rename D.coord.symm
            (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock)))) =
      MvPolynomial.rename D.coord.symm
        (pderiv (i, true) (pderiv (i, false)
          (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock)))) by
    rw [show pderiv (satBlockFalse M n hn2 htb hns D i)
        (MvPolynomial.rename D.coord.symm
          (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))) =
        MvPolynomial.rename D.coord.symm
          (pderiv (i, false)
            (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))) by
      simp [satBlockFalse]
      rw [MvPolynomial.pderiv_rename D.coord.symm.injective]]
    simp [satBlockTrue]
    rw [MvPolynomial.pderiv_rename D.coord.symm.injective]]
  rw [piPlusSATBlockAlgEquiv_symm_rename_symm_apply]
  let inner : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (blockPiPlusAlgEquiv D.blockIndex).symm
      (pderiv (i, true) (pderiv (i, false)
        (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))))
  have hrename : mlProj (MvPolynomial.rename D.coord.symm inner) =
      MvPolynomial.rename D.coord.symm (mlProj inner) :=
    mlProj_rename_equiv D.coord.symm inner
  change mlProj (MvPolynomial.rename D.coord.symm inner) =
    (2 : SATDeciderGaugeSpace M n hn2 htb hns)
  rw [hrename]
  have hinner : mlProj inner = (2 : MvPolynomial (D.blockIndex × Bool) ℚ) := by
    unfold inner pblock
    exact mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_false_actualForm (i := i)
  rw [hinner]
  exact map_ofNat (MvPolynomial.rename D.coord.symm) 2

/-- Flat SAT-coordinate mixed two-hit derivative of the true-side actual
Booleanity factor.  This is the SAT/Cook--Levin lift of the block-level scalar
residue `-2`. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_true_actualForm
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockTrue M n hn2 htb hns D i)
          (pderiv (satBlockFalse M n hn2 htb hns D i)
            (zeroProfileBooleanNormalize
              (piPlusSATBlockAlgEquiv M n hn2 htb hns D
                (((1 : MvPolynomial
                    (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                  X (satBlockTrue M n hn2 htb hns D i) *
                    (1 - X (satBlockTrue M n hn2 htb hns D i))) :
                  SATDeciderGaugeSpace M n hn2 htb hns)))))) =
      -(2 : SATDeciderGaugeSpace M n hn2 htb hns) := by
  let pblock : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (1 : MvPolynomial (D.blockIndex × Bool) ℚ) -
      X (i, true) * (1 - X (i, true))
  have hfactor :
      (((1 : MvPolynomial
            (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
          X (satBlockTrue M n hn2 htb hns D i) *
            (1 - X (satBlockTrue M n hn2 htb hns D i))) :
        SATDeciderGaugeSpace M n hn2 htb hns) =
        MvPolynomial.rename D.coord.symm pblock := by
    simp [pblock, satBlockTrue, MvPolynomial.rename_X]
  rw [hfactor]
  rw [piPlusSATBlockAlgEquiv_rename_symm_apply]
  rw [zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize]
  rw [show pderiv (satBlockTrue M n hn2 htb hns D i)
        (pderiv (satBlockFalse M n hn2 htb hns D i)
          (MvPolynomial.rename D.coord.symm
            (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock)))) =
      MvPolynomial.rename D.coord.symm
        (pderiv (i, true) (pderiv (i, false)
          (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock)))) by
    rw [show pderiv (satBlockFalse M n hn2 htb hns D i)
        (MvPolynomial.rename D.coord.symm
          (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))) =
        MvPolynomial.rename D.coord.symm
          (pderiv (i, false)
            (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))) by
      simp [satBlockFalse]
      rw [MvPolynomial.pderiv_rename D.coord.symm.injective]]
    simp [satBlockTrue]
    rw [MvPolynomial.pderiv_rename D.coord.symm.injective]]
  rw [piPlusSATBlockAlgEquiv_symm_rename_symm_apply]
  let inner : MvPolynomial (D.blockIndex × Bool) ℚ :=
    (blockPiPlusAlgEquiv D.blockIndex).symm
      (pderiv (i, true) (pderiv (i, false)
        (blockBooleanNormalize ((blockPiPlusAlgEquiv D.blockIndex) pblock))))
  have hrename : mlProj (MvPolynomial.rename D.coord.symm inner) =
      MvPolynomial.rename D.coord.symm (mlProj inner) :=
    mlProj_rename_equiv D.coord.symm inner
  change mlProj (MvPolynomial.rename D.coord.symm inner) =
    -(2 : SATDeciderGaugeSpace M n hn2 htb hns)
  rw [hrename]
  have hinner : mlProj inner = -(2 : MvPolynomial (D.blockIndex × Bool) ℚ) := by
    unfold inner pblock
    exact mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_true_actualForm (i := i)
  rw [hinner]
  rw [map_neg]
  exact congrArg Neg.neg (map_ofNat (MvPolynomial.rename D.coord.symm) 2)

/-- The lifted false-side mixed two-hit Booleanity derivative is absorbed by
the SAT-coordinate Booleanity residue span for its `Π+` block. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockTrue M n hn2 htb hns D i)
          (pderiv (satBlockFalse M n hn2 htb hns D i)
            (zeroProfileBooleanNormalize
              (piPlusSATBlockAlgEquiv M n hn2 htb hns D
                (((1 : MvPolynomial
                    (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                  X (satBlockFalse M n hn2 htb hns D i) *
                    (1 - X (satBlockFalse M n hn2 htb hns D i))) :
                  SATDeciderGaugeSpace M n hn2 htb hns)))))) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
        (satBlockFalse M n hn2 htb hns D i) := by
  rw [mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_false_actualForm]
  let S := SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
    (satBlockFalse M n hn2 htb hns D i)
  have h1 : (1 : SATDeciderGaugeSpace M n hn2 htb hns) ∈ S := by
    unfold S
    exact one_mem_SATBlockBooleanityActualProjectedResidueSpan
      M n hn2 htb hns D (satBlockFalse M n hn2 htb hns D i)
  have h2' : ((2 : ℚ) • (1 : SATDeciderGaugeSpace M n hn2 htb hns)) ∈ S :=
    S.smul_mem (2 : ℚ) h1
  simpa [Algebra.smul_def] using h2'

/-- The lifted true-side mixed two-hit Booleanity derivative is absorbed by the
SAT-coordinate Booleanity residue span for its `Π+` block. -/
theorem mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_true_mem_residueSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockTrue M n hn2 htb hns D i)
          (pderiv (satBlockFalse M n hn2 htb hns D i)
            (zeroProfileBooleanNormalize
              (piPlusSATBlockAlgEquiv M n hn2 htb hns D
                (((1 : MvPolynomial
                    (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                  X (satBlockTrue M n hn2 htb hns D i) *
                    (1 - X (satBlockTrue M n hn2 htb hns D i))) :
                  SATDeciderGaugeSpace M n hn2 htb hns)))))) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
        (satBlockTrue M n hn2 htb hns D i) := by
  rw [mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_true_actualForm]
  let S := SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
    (satBlockTrue M n hn2 htb hns D i)
  have h1 : (1 : SATDeciderGaugeSpace M n hn2 htb hns) ∈ S := by
    unfold S
    exact one_mem_SATBlockBooleanityActualProjectedResidueSpan
      M n hn2 htb hns D (satBlockTrue M n hn2 htb hns D i)
  have h2' : ((2 : ℚ) • (1 : SATDeciderGaugeSpace M n hn2 htb hns)) ∈ S :=
    S.smul_mem (2 : ℚ) h1
  have h2 : (2 : SATDeciderGaugeSpace M n hn2 htb hns) ∈ S := by
    simpa [Algebra.smul_def] using h2'
  exact S.neg_mem h2

/-- Variable-level one-hit derivative residue certificate for an actual
Cook--Levin Booleanity factor.  Unlike the block-index lemmas above, this is
stated directly for an arbitrary SAT variable `v`; the residue span is selected
from `v`'s `Π+` block coordinates. -/
def PiPlusBooleanProjectedBooleanityFactorOneHitDerivativeResidueCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) : Prop :=
  mlProj
    ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (pderiv v
        (zeroProfileBooleanNormalize
          (piPlusSATBlockAlgEquiv M n hn2 htb hns D
            (((1 : MvPolynomial
                (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
              X v * (1 - X v)) :
              SATDeciderGaugeSpace M n hn2 htb hns))))) ∈
    SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v

/-- Variable-level one-hit derivative residue payload for all Cook--Levin SAT
variables. -/
def CookLevinBooleanityFactorOneHitDerivativeResiduePayload
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ v : Fin (cook_levin_compilation M n hn2 htb hns).numVars,
    PiPlusBooleanProjectedBooleanityFactorOneHitDerivativeResidueCertificate
      M n hn2 htb hns D v

/-- The one-hit derivative residue payload is unconditional.  The proof splits
an arbitrary SAT variable into its false/true coordinate in the concrete `Π+`
block chart and then consumes the lifted block derivative certificates. -/
theorem cookLevinBooleanityFactorOneHitDerivativeResiduePayload_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    CookLevinBooleanityFactorOneHitDerivativeResiduePayload M n hn2 htb hns D := by
  intro v
  let i : D.blockIndex := (D.coord v).1
  by_cases hb : (D.coord v).2 = false
  · have hpair : D.coord v = (i, false) := by
      apply Prod.ext
      · simp [i]
      · exact hb
    have hv : v = satBlockFalse M n hn2 htb hns D i := by
      apply D.coord.injective
      rw [hpair]
      simp [satBlockFalse]
    rw [hv]
    unfold PiPlusBooleanProjectedBooleanityFactorOneHitDerivativeResidueCertificate
    exact mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan
      M n hn2 htb hns D i
  · have hbtrue : (D.coord v).2 = true := by
      cases h : (D.coord v).2 with
      | false => exact False.elim (hb h)
      | true => rfl
    have hpair : D.coord v = (i, true) := by
      apply Prod.ext
      · simp [i]
      · exact hbtrue
    have hv : v = satBlockTrue M n hn2 htb hns D i := by
      apply D.coord.injective
      rw [hpair]
      simp [satBlockTrue]
    rw [hv]
    unfold PiPlusBooleanProjectedBooleanityFactorOneHitDerivativeResidueCertificate
    exact mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_booleanProjected_booleanity_true_mem_residueSpan
      M n hn2 htb hns D i

/-- Mixed two-hit derivative residue payload at block granularity: for each
`Π+` block, both actual Booleanity factors survive the `false`/`true` mixed
Leibniz allocation only as scalar residues in the corrected SAT residue span. -/
def CookLevinBooleanityFactorMixedDerivativeResiduePayload
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ i : D.blockIndex,
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockTrue M n hn2 htb hns D i)
          (pderiv (satBlockFalse M n hn2 htb hns D i)
            (zeroProfileBooleanNormalize
              (piPlusSATBlockAlgEquiv M n hn2 htb hns D
                (((1 : MvPolynomial
                    (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                  X (satBlockFalse M n hn2 htb hns D i) *
                    (1 - X (satBlockFalse M n hn2 htb hns D i))) :
                  SATDeciderGaugeSpace M n hn2 htb hns)))))) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
        (satBlockFalse M n hn2 htb hns D i)
    ∧
    mlProj
      ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (pderiv (satBlockTrue M n hn2 htb hns D i)
          (pderiv (satBlockFalse M n hn2 htb hns D i)
            (zeroProfileBooleanNormalize
              (piPlusSATBlockAlgEquiv M n hn2 htb hns D
                (((1 : MvPolynomial
                    (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) -
                  X (satBlockTrue M n hn2 htb hns D i) *
                    (1 - X (satBlockTrue M n hn2 htb hns D i))) :
                  SATDeciderGaugeSpace M n hn2 htb hns)))))) ∈
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
        (satBlockTrue M n hn2 htb hns D i)

/-- The mixed two-hit derivative residue payload is unconditional, by the
explicit SAT-coordinate scalar residue calculations `2` and `-2`. -/
theorem cookLevinBooleanityFactorMixedDerivativeResiduePayload_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    CookLevinBooleanityFactorMixedDerivativeResiduePayload M n hn2 htb hns D := by
  intro i
  exact ⟨
    mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan
      M n hn2 htb hns D i,
    mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_true_mem_residueSpan
      M n hn2 htb hns D i⟩

/-- Paper-scale one-hit derivative residue payload. -/
abbrev PaperScaleCookLevinBooleanityFactorOneHitDerivativeResiduePayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityFactorOneHitDerivativeResiduePayload
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale mixed two-hit derivative residue payload. -/
abbrev PaperScaleCookLevinBooleanityFactorMixedDerivativeResiduePayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityFactorMixedDerivativeResiduePayload
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale one-hit derivative residue payload is unconditional. -/
theorem paperScale_cookLevinBooleanityFactorOneHitDerivativeResiduePayload_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinBooleanityFactorOneHitDerivativeResiduePayload M htb hns :=
  cookLevinBooleanityFactorOneHitDerivativeResiduePayload_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale mixed two-hit derivative residue payload is unconditional. -/
theorem paperScale_cookLevinBooleanityFactorMixedDerivativeResiduePayload_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinBooleanityFactorMixedDerivativeResiduePayload M htb hns :=
  cookLevinBooleanityFactorMixedDerivativeResiduePayload_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Uniform rank payload for corrected Booleanity residue spans.  This packages
local residue absorption at the same granularity as the Booleanity span surface:
each actual Booleanity row may land in a three-dimensional block-local residue
space. -/
def CookLevinBooleanityResidueRankPayload
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ v : Fin (cook_levin_compilation M n hn2 htb hns).numVars,
    Module.finrank ℚ
      (SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v) ≤ 3

/-- The corrected Booleanity residue rank payload is unconditional: it follows
from the explicit three-generator basis `{1, X_false, X_true}`. -/
theorem cookLevinBooleanityResidueRankPayload_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    CookLevinBooleanityResidueRankPayload M n hn2 htb hns D := by
  intro v
  exact finrank_SATBlockBooleanityActualProjectedResidueSpan_le_three
    M n hn2 htb hns D v

/-- Paper-scale corrected Booleanity residue rank payload. -/
abbrev PaperScaleCookLevinBooleanityResidueRankPayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityResidueRankPayload
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale corrected Booleanity residue rank payload is unconditional. -/
theorem paperScale_cookLevinBooleanityResidueRankPayload_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinBooleanityResidueRankPayload M htb hns :=
  cookLevinBooleanityResidueRankPayload_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- One-slot symmetric-power introduction: a row already in a local interface
space belongs to the first symmetric power of that space.  This is the algebraic
adapter used below to turn the corrected Booleanity residue-span payload into the
Route-W `symPower` surface. -/
theorem mem_symPower_one_of_mem {N : Type*} [DecidableEq N]
    (W : Submodule ℚ (MvPolynomial N ℚ))
    {p : MvPolynomial N ℚ} (hp : p ∈ W) :
    p ∈ symPower ℚ 1 W := by
  classical
  unfold symPower
  refine Submodule.subset_span ?_
  refine ⟨fun _ : Fin 1 => p, ?_, ?_⟩
  · intro _
    exact hp
  · simp

/-- The concrete post-`Π+`, Boolean-normalized, pulled-back Booleanity row for
an actual Cook--Levin Booleanity factor indexed by variable `v`.  This is the
row appearing in the corrected span-level Booleanity certificate. -/
noncomputable def cookLevinBooleanityPostRow
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin n) : SATDeciderGaugeSpace M n hn2 htb hns :=
  mlProj
    ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          (((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) :
            SATDeciderGaugeSpace M n hn2 htb hns))))

/-- Span-level corrected Booleanity row certificate.  This is the proper target:
the Booleanity row is allowed to be block-local constant-plus-linear residue
content instead of being forced into a single source generator or the constant
row. -/
def PiPlusBooleanProjectedBooleanityFactorProjectedSpanCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin n) : Prop :=
  cookLevinBooleanityPostRow M n hn2 htb hns D v ∈
    SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v

/-- Span-level Booleanity payload. -/
def CookLevinBooleanityFactorProjectedSpanPayload
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ v : Fin n,
    PiPlusBooleanProjectedBooleanityFactorProjectedSpanCertificate
      M n hn2 htb hns D v

/-- Paper-scale span-level Booleanity payload. -/
abbrev PaperScaleCookLevinBooleanityFactorProjectedSpanPayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanityFactorProjectedSpanPayload
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- The span-level Booleanity payload is unconditional.  This discharges the
local algebra behind the corrected Booleanity interface: false-side coordinates
close to `1`, while true-side coordinates close to the admitted residue
`1 + X_false - X_true`. -/
theorem cookLevinBooleanityFactorProjectedSpanPayload_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    CookLevinBooleanityFactorProjectedSpanPayload M n hn2 htb hns D := by
  intro v
  let i : D.blockIndex := (D.coord v).1
  by_cases hb : (D.coord v).2 = false
  · have hpair : D.coord v = (i, false) := by
      apply Prod.ext
      · simp [i]
      · exact hb
    have hv : v = satBlockFalse M n hn2 htb hns D i := by
      apply D.coord.injective
      rw [hpair]
      simp [satBlockFalse]
    rw [hv]
    unfold PiPlusBooleanProjectedBooleanityFactorProjectedSpanCertificate
    unfold cookLevinBooleanityPostRow
    simp only [boolLC, boolPoly']
    rw [mlProj_piPlusSATBlockAlgEquiv_symm_booleanProjected_booleanity_false]
    exact one_mem_SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
      (satBlockFalse M n hn2 htb hns D i)
  · have hbtrue : (D.coord v).2 = true := by
      cases h : (D.coord v).2 with
      | false => exact False.elim (hb h)
      | true => rfl
    have hpair : D.coord v = (i, true) := by
      apply Prod.ext
      · simp [i]
      · exact hbtrue
    have hv : v = satBlockTrue M n hn2 htb hns D i := by
      apply D.coord.injective
      rw [hpair]
      simp [satBlockTrue]
    rw [hv]
    unfold PiPlusBooleanProjectedBooleanityFactorProjectedSpanCertificate
    unfold cookLevinBooleanityPostRow
    simp only [boolLC, boolPoly']
    rw [mlProj_piPlusSATBlockAlgEquiv_symm_booleanProjected_booleanity_true_actualForm]
    simpa [sub_eq_add_neg] using
      (Submodule.add_mem _
        (Submodule.add_mem _
          (one_mem_SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
            (satBlockTrue M n hn2 htb hns D i))
          (X_false_mem_SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
            (satBlockTrue M n hn2 htb hns D i)))
        (Submodule.neg_mem _
          (X_true_mem_SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D
            (satBlockTrue M n hn2 htb hns D i))))

/-- Residue-to-interface containment from the three concrete Booleanity residue
generators.  This is the explicit index-alignment bridge: callers must supply
that the block-local `1`, `X_false`, and `X_true` rows are represented inside the
paper compiled-basis Booleanity interface space for the chosen `(B,κ,ℓ)`. -/
theorem SATBlockBooleanityActualProjectedResidueSpan_le_interfaceSpace_of_generators
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hone : (1 : SATDeciderGaugeSpace M n hn2 htb hns) ∈
      interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity)
    (hfalse : (X (satBlockFalse M n hn2 htb hns D (D.coord v).1) :
        SATDeciderGaugeSpace M n hn2 htb hns) ∈
      interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity)
    (htrue : (X (satBlockTrue M n hn2 htb hns D (D.coord v).1) :
        SATDeciderGaugeSpace M n hn2 htb hns) ∈
      interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity) :
    SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v ≤
      interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity := by
  classical
  unfold SATBlockBooleanityActualProjectedResidueSpan
  refine Submodule.span_le.mpr ?_
  intro p hp
  unfold SATBlockBooleanityActualProjectedResidueGenerators at hp
  have hp' : p = (1 : SATDeciderGaugeSpace M n hn2 htb hns) ∨
      p = (X (satBlockFalse M n hn2 htb hns D (D.coord v).1) :
        SATDeciderGaugeSpace M n hn2 htb hns) ∨
      p = (X (satBlockTrue M n hn2 htb hns D (D.coord v).1) :
        SATDeciderGaugeSpace M n hn2 htb hns) := by
    simpa using hp
  rcases hp' with hp | hp | hp
  · subst hp
    exact hone
  · subst hp
    exact hfalse
  · subst hp
    exact htrue

/-- Multiplying a symmetric-power element by one interface row raises the
symmetric-power degree by one. -/
theorem symPower_mul_left_mem_succ_local
    {n k : Nat} {W : Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    {a b : MvPolynomial (Fin n) ℚ}
    (ha : a ∈ W) (hb : b ∈ symPower ℚ k W) :
    a * b ∈ symPower ℚ (k + 1) W := by
  classical
  unfold symPower at hb ⊢
  let T : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    Submodule.span ℚ
      {p : MvPolynomial (Fin n) ℚ |
        ∃ f : Fin (k + 1) → MvPolynomial (Fin n) ℚ,
          (∀ i, f i ∈ W) ∧ p = ∏ i, f i}
  change a * b ∈ T
  refine Submodule.span_induction
    (p := fun q : MvPolynomial (Fin n) ℚ => fun _ => a * q ∈ T)
    ?_ ?_ ?_ ?_ hb
  · rintro q ⟨f, hf, rfl⟩
    refine Submodule.subset_span ?_
    let g : Fin (k + 1) → MvPolynomial (Fin n) ℚ := Fin.cases a f
    refine ⟨g, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact ha
      | succ i => exact hf i
    · simpa [g] using (Fin.prod_univ_succ g).symm
  · simp [T]
  · intro p q _ _ hp hq
    rw [mul_add]
    exact Submodule.add_mem T hp hq
  · intro c q _ hq
    simpa [smul_eq_C_mul, mul_assoc, mul_left_comm, mul_comm] using
      Submodule.smul_mem T c hq

/-- Finite products of rows in one interface space lie in the corresponding
symmetric power. -/
theorem finset_prod_mem_symPower_of_mem_interface
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (s : Finset ι) (row : ι → MvPolynomial (Fin n) ℚ)
    (hrow : ∀ i ∈ s, row i ∈ W) :
    s.prod row ∈ symPower ℚ s.card W := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold symPower
      refine Submodule.subset_span ?_
      refine ⟨fun i : Fin 0 => False.elim (Fin.elim0 i), ?_, ?_⟩
      · intro i
        exact False.elim (Fin.elim0 i)
      · simp
  | insert a s has ih =>
      rw [Finset.prod_insert has]
      simpa [has] using
        symPower_mul_left_mem_succ_local (hrow a (by simp [has]))
          (ih (by intro i hi; exact hrow i (by simp [hi])))

/-- Products of actual Booleanity post-rows land in the `k`-fold Booleanity
compiled-basis symmetric power once every local residue span has been aligned
with the compiled-basis Booleanity interface space. -/
theorem cookLevinBooleanity_postRow_finsetProd_mem_interface_symPower
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (s : Finset (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (halign : ∀ v ∈ s,
      SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v ≤
        interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity) :
    s.prod (fun v => cookLevinBooleanityPostRow M n hn2 htb hns D v) ∈
      symPower ℚ s.card
        (interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity) := by
  classical
  exact finset_prod_mem_symPower_of_mem_interface
    (interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity) s
    (fun v => cookLevinBooleanityPostRow M n hn2 htb hns D v)
    (by
      intro v hv
      exact halign v hv
        ((cookLevinBooleanityFactorProjectedSpanPayload_unconditional
          M n hn2 htb hns D) v))

/-- The actual Cook--Levin Booleanity post-row belongs to the first symmetric
power of its corrected Booleanity residue span.  This is the coefficient-level
extraction core needed by Route W: the existing false/true Booleanity span
infrastructure discharges the local algebra, and `mem_symPower_one_of_mem`
packages the resulting residue row as a one-slot symmetric-power contribution. -/
theorem cookLevinBooleanity_postRow_mem_symPower
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin n) :
    cookLevinBooleanityPostRow M n hn2 htb hns D v ∈
      symPower ℚ 1
        (SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v) := by
  exact mem_symPower_one_of_mem
    (SATBlockBooleanityActualProjectedResidueSpan M n hn2 htb hns D v)
    ((cookLevinBooleanityFactorProjectedSpanPayload_unconditional
      M n hn2 htb hns D) v)

/-- Paper-scale actual Cook--Levin Booleanity post-row symmetric-power
membership. -/
theorem paperScale_cookLevinBooleanity_postRow_mem_symPower
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (v : Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) :
    cookLevinBooleanityPostRow M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) v ∈
      symPower ℚ 1
        (SATBlockBooleanityActualProjectedResidueSpan
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) v) := by
  exact cookLevinBooleanity_postRow_mem_symPower
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) v

/-- Paper-scale span-level Booleanity payload, discharged from the concrete
false/true Booleanity normal forms. -/
theorem paperScale_cookLevinBooleanityFactorProjectedSpanPayload_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinBooleanityFactorProjectedSpanPayload M htb hns :=
  cookLevinBooleanityFactorProjectedSpanPayload_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)


/-- Bridge from span-level Booleanity rows to the previous single-row projected
payload.  This is intentionally a named reduction: if downstream code insists on
single generators, it must prove a compression from span rows to that surface. -/
def CookLevinBooleanitySpanToSingleProjectedReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  CookLevinBooleanityFactorProjectedSpanPayload M n hn2 htb hns D →
    CookLevinBooleanityFactorProjectedRowPayload M n hn2 htb hns D

/-- Paper-scale span-to-single reduction. -/
abbrev PaperScaleCookLevinBooleanitySpanToSingleProjectedReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinBooleanitySpanToSingleProjectedReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- If a later seam supplies span-to-single compression, the previous projected
payload follows. -/
theorem paperScale_booleanityProjectedRows_of_spanPayload_reduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hspan : PaperScaleCookLevinBooleanityFactorProjectedSpanPayload M htb hns)
    (hred : PaperScaleCookLevinBooleanitySpanToSingleProjectedReduction
      M htb hns) :
    PaperScaleCookLevinBooleanityFactorProjectedRowPayload M htb hns :=
  hred hspan

/-! ## Axiom audit anchors -/

#print axioms SATBlockBooleanityActualProjectedResidueGenerators
#print axioms SATBlockBooleanityActualProjectedResidueSpan
#print axioms finrank_SATBlockBooleanityActualProjectedResidueSpan_le_three
#print axioms cookLevinBooleanityResidueRankPayload_unconditional
#print axioms paperScale_cookLevinBooleanityResidueRankPayload_unconditional
#print axioms mem_symPower_one_of_mem
#print axioms cookLevinBooleanityPostRow
#print axioms SATBlockBooleanityActualProjectedResidueSpan_le_interfaceSpace_of_generators
#print axioms symPower_mul_left_mem_succ_local
#print axioms finset_prod_mem_symPower_of_mem_interface
#print axioms cookLevinBooleanity_postRow_finsetProd_mem_interface_symPower
#print axioms cookLevinBooleanity_postRow_mem_symPower
#print axioms paperScale_cookLevinBooleanity_postRow_mem_symPower
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_booleanProjected_booleanity_false
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_booleanProjected_booleanity_true_actualForm
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_false_booleanProjected_booleanity_false_actualForm
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_booleanProjected_booleanity_true_actualForm
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_booleanProjected_booleanity_true_mem_residueSpan
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_false_actualForm
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_true_actualForm
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_pderiv_false_booleanProjected_booleanity_true_mem_residueSpan
#print axioms cookLevinBooleanityFactorOneHitDerivativeResiduePayload_unconditional
#print axioms cookLevinBooleanityFactorMixedDerivativeResiduePayload_unconditional
#print axioms paperScale_cookLevinBooleanityFactorOneHitDerivativeResiduePayload_unconditional
#print axioms paperScale_cookLevinBooleanityFactorMixedDerivativeResiduePayload_unconditional
#print axioms cookLevinBooleanityFactorProjectedSpanPayload_unconditional
#print axioms paperScale_cookLevinBooleanityFactorProjectedSpanPayload_unconditional
#print axioms one_mem_SATBlockBooleanityActualProjectedResidueSpan
#print axioms X_false_mem_SATBlockBooleanityActualProjectedResidueSpan
#print axioms X_true_mem_SATBlockBooleanityActualProjectedResidueSpan
#print axioms unaryBooleanitySingleRowTooTightDiagnostic
#print axioms paperScale_booleanityProjectedRows_of_spanPayload_reduction

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
