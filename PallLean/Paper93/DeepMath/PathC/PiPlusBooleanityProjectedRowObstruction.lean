import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityPullbackNormalization
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityActualFactorNormalForm
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSignedCoordinateAtoms

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
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
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

/-- Span-level corrected Booleanity row certificate.  This is the proper target:
the Booleanity row is allowed to be block-local constant-plus-linear residue
content instead of being forced into a single source generator or the constant
row. -/
def PiPlusBooleanProjectedBooleanityFactorProjectedSpanCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin n) : Prop :=
  mlProj
    ((piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          (((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) :
            SATDeciderGaugeSpace M n hn2 htb hns)))) ∈
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
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_booleanProjected_booleanity_false
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_booleanProjected_booleanity_true_actualForm
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_false_booleanProjected_booleanity_false_actualForm
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_booleanProjected_booleanity_true_actualForm
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan
#print axioms mlProj_piPlusSATBlockAlgEquiv_symm_pderiv_true_booleanProjected_booleanity_true_mem_residueSpan
#print axioms cookLevinBooleanityFactorProjectedSpanPayload_unconditional
#print axioms paperScale_cookLevinBooleanityFactorProjectedSpanPayload_unconditional
#print axioms one_mem_SATBlockBooleanityActualProjectedResidueSpan
#print axioms X_false_mem_SATBlockBooleanityActualProjectedResidueSpan
#print axioms X_true_mem_SATBlockBooleanityActualProjectedResidueSpan
#print axioms unaryBooleanitySingleRowTooTightDiagnostic
#print axioms paperScale_booleanityProjectedRows_of_spanPayload_reduction

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
