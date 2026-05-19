import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSignedAtoms

/-!
# Same-block signed atom for Boolean-projected Pi+

The canonical paper-scale pairing sends even-left adjacent pairs into the same
`Pi+` block.  Cross-block signed atom certificates therefore cannot cover the
whole rest list.  This file isolates the same-block algebra.

For a same-block signed factor

`1 - c X(i,false) X(i,true)`,

Boolean-projected `Pi+` pulls it back to `1 - c X(i,true)`.  This is not a
single `(1,0)` source row of that same local factor; it is, however, a concrete
finite combination of source rows if one allows a degree-one multiplier.  This
records the exact local obstruction/route for the even-left parity slice.
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

/-- Signed atom whose two endpoints are the two Boolean sides of the same
`Pi+` block. -/
noncomputable def blockSignedSameBlockAtom {ι : Type*}
    (c : ℚ) (i : ι) : MvPolynomial (ι × Bool) ℚ :=
  (1 : MvPolynomial (ι × Bool) ℚ) -
    c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ)

/-- Same-block signed atoms are multilinear, so `mlProj` fixes them. -/
theorem mlProj_blockSignedSameBlockAtom
    {ι : Type*} [DecidableEq ι] (c : ℚ) (i : ι) :
    mlProj (blockSignedSameBlockAtom c i : MvPolynomial (ι × Bool) ℚ) =
      blockSignedSameBlockAtom c i := by
  unfold blockSignedSameBlockAtom
  have hidx : (i, false) ≠ (i, true) := by intro h; cases h
  have hmul := mlProj_X_mul_X_ne
    (σ := ι × Bool) (a := (i, false)) (b := (i, true)) hidx
  rw [sub_eq_add_neg, mlProj_add]
  have hone : mlProj (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
    rw [show (1 : MvPolynomial (ι × Bool) ℚ) = MvPolynomial.monomial 0 1 by rfl,
      mlProj_monomial]
    have h0 : Finsupp.IsMultilinear (0 : ι × Bool →₀ ℕ) := by intro x; simp
    rw [if_pos h0]
  have hneg :
      mlProj (-(c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ))) =
        -(c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ)) := by
    rw [← neg_one_smul ℚ (c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ)),
      mlProj_smul, mlProj_smul, hmul]
  rw [hone, hneg]

/-- Boolean-projected `Pi+` pullback of a same-block signed atom.  The endpoint
same-block leakage is exactly the linear factor `1 - c X(i,true)`. -/
theorem blockPiPlusInvAlgHom_booleanProjected_signedSameBlockAtom
    {ι : Type*} [DecidableEq ι] (c : ℚ) (i : ι) :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι (blockSignedSameBlockAtom c i))) =
      (1 : MvPolynomial (ι × Bool) ℚ) - c • X (i, true) := by
  unfold blockSignedSameBlockAtom
  rw [map_sub, map_one, map_smul, blockBooleanNormalize_sub]
  have hone : blockBooleanNormalize (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
    rw [show (1 : MvPolynomial (ι × Bool) ℚ) = MvPolynomial.C 1 by rfl]
    rw [MvPolynomial.C_apply, blockBooleanNormalize_monomial]
    rfl
  rw [hone, blockBooleanNormalize_smul, blockBooleanNormalize_blockPiPlusAlgHom_mixed]
  rw [map_sub, map_one, map_smul]
  rw [blockPiPlusInvAlgHom_sub_same_block]

/-- A local span certificate allowing one derivative and a degree-one multiplier.
This is the exact budget needed by the same-block signed atom calculation. -/
def BlockPiPlusBooleanProjectedOneOneRowSpanCertificate
    {ι : Type*} [DecidableEq ι] (p : MvPolynomial (ι × Bool) ℚ) : Prop :=
  blockPiPlusInvAlgHom ι (blockBooleanNormalize (blockPiPlusAlgHom ι p)) ∈
    Submodule.span ℚ
      {q : MvPolynomial (ι × Bool) ℚ |
        ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * blockIterDerivList S p)}

/-- The same-block signed atom is a concrete finite combination of `(1,1)`
source rows: zero-derivative row, one derivative with multiplier `X(i,false)`,
and one derivative with constant multiplier. -/
theorem blockPiPlusBooleanProjectedSameBlockSignedAtom_oneOneSpan
    {ι : Type*} [DecidableEq ι] (c : ℚ) (i : ι) :
    BlockPiPlusBooleanProjectedOneOneRowSpanCertificate
      (blockSignedSameBlockAtom c i) := by
  classical
  let p : MvPolynomial (ι × Bool) ℚ := blockSignedSameBlockAtom c i
  let r0 : MvPolynomial (ι × Bool) ℚ := mlProj ((1 : MvPolynomial (ι × Bool) ℚ) * blockIterDerivList [] p)
  let rX : MvPolynomial (ι × Bool) ℚ := mlProj ((X (i, false) : MvPolynomial (ι × Bool) ℚ) * blockIterDerivList [(i, false)] p)
  let rD : MvPolynomial (ι × Bool) ℚ := mlProj ((1 : MvPolynomial (ι × Bool) ℚ) * blockIterDerivList [(i, false)] p)
  have hr0_mem : r0 ∈ Submodule.span ℚ
      {q : MvPolynomial (ι × Bool) ℚ |
        ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * blockIterDerivList S p)} := by
    exact Submodule.subset_span ⟨[], 1, by simp, by simp, rfl⟩
  have hrX_mem : rX ∈ Submodule.span ℚ
      {q : MvPolynomial (ι × Bool) ℚ |
        ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * blockIterDerivList S p)} := by
    exact Submodule.subset_span ⟨[(i, false)], X (i, false), by simp,
      by simp [MvPolynomial.totalDegree_X], rfl⟩
  have hrD_mem : rD ∈ Submodule.span ℚ
      {q : MvPolynomial (ι × Bool) ℚ |
        ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * blockIterDerivList S p)} := by
    exact Submodule.subset_span ⟨[(i, false)], 1, by simp, by simp, rfl⟩
  have hpull : blockPiPlusInvAlgHom ι
      (blockBooleanNormalize (blockPiPlusAlgHom ι p)) =
      r0 - rX + rD := by
    subst p r0 rX rD
    rw [blockPiPlusInvAlgHom_booleanProjected_signedSameBlockAtom]
    unfold blockSignedSameBlockAtom blockIterDerivList
    simp only [List.foldl_nil, List.foldl_cons]
    have hderiv :
        pderiv (i, false)
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ)) =
          -(c • (X (i, true) : MvPolynomial (ι × Bool) ℚ)) := by
      simp
    rw [hderiv]
    have hrow0 :
        mlProj ((1 : MvPolynomial (ι × Bool) ℚ) *
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ))) =
        (1 : MvPolynomial (ι × Bool) ℚ) -
            c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ) := by
      simpa [blockSignedSameBlockAtom] using mlProj_blockSignedSameBlockAtom c i
    have hrowD :
        mlProj ((1 : MvPolynomial (ι × Bool) ℚ) *
          (-(c • (X (i, true) : MvPolynomial (ι × Bool) ℚ)))) =
        -(c • (X (i, true) : MvPolynomial (ι × Bool) ℚ)) := by
      rw [one_mul]
      rw [← neg_one_smul ℚ (c • (X (i, true) : MvPolynomial (ι × Bool) ℚ)),
        mlProj_smul, mlProj_smul, mlProj_X_block]
    have hrowX :
        mlProj ((X (i, false) : MvPolynomial (ι × Bool) ℚ) *
          (-(c • (X (i, true) : MvPolynomial (ι × Bool) ℚ)))) =
        -(c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ)) := by
      have hxexpr :
          (X (i, false) : MvPolynomial (ι × Bool) ℚ) *
            (-(c • (X (i, true) : MvPolynomial (ι × Bool) ℚ))) =
          -(c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ)) := by
        simp [Algebra.smul_def]
        ring
      rw [hxexpr]
      rw [← neg_one_smul ℚ (c • (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ)),
        mlProj_smul, mlProj_smul]
      have hidx : (i, false) ≠ (i, true) := by intro h; cases h
      rw [mlProj_X_mul_X_ne (σ := ι × Bool) (a := (i, false)) (b := (i, true)) hidx]
    rw [hrow0, hrowX, hrowD]
    ring
  unfold BlockPiPlusBooleanProjectedOneOneRowSpanCertificate
  change blockPiPlusInvAlgHom ι (blockBooleanNormalize (blockPiPlusAlgHom ι p)) ∈
    Submodule.span ℚ
      {q : MvPolynomial (ι × Bool) ℚ |
        ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * blockIterDerivList S p)}
  rw [hpull]
  exact Submodule.add_mem _ (Submodule.sub_mem _ hr0_mem hrX_mem) hrD_mem

/-! ## Axiom audit anchors -/

#print axioms mlProj_blockSignedSameBlockAtom
#print axioms blockPiPlusInvAlgHom_booleanProjected_signedSameBlockAtom
#print axioms blockPiPlusBooleanProjectedSameBlockSignedAtom_oneOneSpan

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
