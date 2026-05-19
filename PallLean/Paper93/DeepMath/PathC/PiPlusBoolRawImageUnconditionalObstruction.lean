import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageCoordinateRenamedCombinationCertificate

/-!
# Raw fixedness obstruction for unconditional discharge

The coordinate-renamed finite fixedness socket is intentionally raw: it asks the
Hadamard block algebra equivalence to fix the listed pieces before Boolean
normalization.  This file records the local obstruction to discharging that
socket unconditionally for the Cook--Levin Booleanity mixed monomials.

In one block, `X(i,false) * X(i,true)` is not raw-fixed by `Pi+`: it maps to
`X(i,false)^2 - X(i,true)^2`.  The Boolean-projected route repairs exactly this
leakage, but the raw fixed-piece certificate cannot be closed for mixed
Booleanity pieces without a further invariant decomposition that avoids this
atom.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

variable {ι : Type*} (i : ι)

/-- Raw `Pi+` sends the mixed block monomial to the difference of two squares. -/
theorem blockPiPlusAlgHom_mixed_raw_square_difference :
    blockPiPlusAlgHom ι
        (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ) =
      (X (i, false) * X (i, false) - X (i, true) * X (i, true) :
        MvPolynomial (ι × Bool) ℚ) := by
  simp [blockPiPlusAlgHom, blockPiPlusLinearForm]
  ring_nf

/-- Consequently, the raw mixed block monomial is not fixed by `Pi+` whenever a
block exists.  This is the local reason an unconditional discharge of the raw
fixed-combination socket is not available from the existing Cook--Levin
Booleanity atom. -/
theorem blockPiPlusAlgHom_mixed_ne_self [DecidableEq ι] :
    blockPiPlusAlgHom ι
        (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ) ≠
      (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ) := by
  intro h
  have hcoeff := congrArg
    (fun p : MvPolynomial (ι × Bool) ℚ =>
      coeff (Finsupp.single (i, false) 1 + Finsupp.single (i, true) 1) p) h
  rw [blockPiPlusAlgHom_mixed_raw_square_difference] at hcoeff
  norm_num at hcoeff

/-- Equivalence form of the same raw fixedness obstruction. -/
theorem blockPiPlusAlgEquiv_mixed_ne_self [DecidableEq ι] :
    blockPiPlusAlgEquiv ι
        (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ) ≠
      (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ) := by
  simpa [blockPiPlusAlgEquiv]
    using blockPiPlusAlgHom_mixed_ne_self (ι := ι) i

/-! ## Axiom audit anchors -/

#print axioms blockPiPlusAlgHom_mixed_raw_square_difference
#print axioms blockPiPlusAlgHom_mixed_ne_self
#print axioms blockPiPlusAlgEquiv_mixed_ne_self

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
