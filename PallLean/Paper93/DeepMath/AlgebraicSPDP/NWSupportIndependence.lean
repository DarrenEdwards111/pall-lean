import PallLean.Paper93.DeepMath.AlgebraicSPDP.ArithmeticCircuitSPDPPivot
import Mathlib.Data.Finset.Image

/-!
# NW Support Independence

This file proves the first NW-specific combinatorial layer behind
`NWSPDPIndependenceCertificate`.

We model a Nisan-Wigderson design monomial by the graph of a codeword

`x ↦ (x, code a x)`.

Low agreement of distinct codewords gives the two facts needed by the
leading-support engine:

1. a derivative window larger than the agreement bound contains a point where
   two distinct codewords differ, so differentiating by the graph of one
   codeword kills the other monomial;
2. an outside window larger than the agreement bound gives injective residual
   graph supports, so the post-derivative leading monomial is private.

The remaining polynomial-calculus step is to identify these graph-support
rows with actual shifted partial derivative rows of the NW polynomial.  Once
that identification supplies `span_rank_le_spdp`, the certificate is
constructed here.
-/

namespace PallLean.Paper93.DeepMath.AlgebraicSPDP

open scoped BigOperators

section GraphDesign

variable {Label Point Value : Type*}
variable [Fintype Point] [DecidableEq Point] [DecidableEq Value]

/-- Points where two NW codewords agree. -/
def nwAgreementSet (code : Label -> Point -> Value) (a b : Label) :
    Finset Point :=
  Finset.univ.filter fun x => code a x = code b x

/-- The graph of a codeword restricted to a finite point window. -/
def nwGraphOn (code : Label -> Point -> Value) (D : Finset Point)
    (a : Label) : Finset (Point × Value) :=
  D.image fun x => (x, code a x)

/-- The residual graph after differentiating/removing the point window `D`. -/
def nwGraphOff (code : Label -> Point -> Value) (D : Finset Point)
    (a : Label) : Finset (Point × Value) :=
  (Finset.univ.filter fun x => x ∉ D).image fun x => (x, code a x)

omit [DecidableEq Point] in
/-- If two codewords agree on all of a window, that window is contained in the
agreement set. -/
theorem nw_window_subset_agreement_of_agrees
    (code : Label -> Point -> Value) (D : Finset Point) (a b : Label)
    (hagrees : ∀ x ∈ D, code a x = code b x) :
    D ⊆ nwAgreementSet code a b := by
  intro x hx
  simp [nwAgreementSet, hagrees x hx]

omit [DecidableEq Point] in
/-- Low agreement forces a disagreement inside every larger derivative
window.  This is the NW reason that differentiating by the graph of one
codeword kills every other codeword monomial. -/
theorem exists_disagreement_in_large_window
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound : Nat)
    (hD : overlapBound < D.card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound)
    {a b : Label} (hne : a ≠ b) :
    ∃ x ∈ D, code a x ≠ code b x := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsubset : D ⊆ nwAgreementSet code a b :=
    nw_window_subset_agreement_of_agrees code D a b hnone
  have hcard : D.card <= (nwAgreementSet code a b).card :=
    Finset.card_le_card hsubset
  have : D.card <= overlapBound := le_trans hcard (hlow a b hne)
  omega

/-- If two residual graph supports are equal, then the two codewords agree at
every point outside the derivative window. -/
theorem agrees_off_window_of_nwGraphOff_eq
    (code : Label -> Point -> Value) (D : Finset Point)
    {a b : Label}
    (hgraph : nwGraphOff code D a = nwGraphOff code D b) :
    ∀ x, x ∉ D -> code a x = code b x := by
  classical
  intro x hxD
  have hxA : (x, code a x) ∈ nwGraphOff code D a := by
    simp [nwGraphOff, hxD]
  have hxB : (x, code a x) ∈ nwGraphOff code D b := by
    simpa [hgraph] using hxA
  have hxB' : x ∉ D ∧ code b x = code a x := by
    simpa [nwGraphOff] using hxB
  exact hxB'.2.symm

/-- Low agreement and a large outside window make the residual graph supports
injective.  These residual supports are the private leading monomials in the
NW shifted-partial argument. -/
theorem nwGraphOff_injective_of_lowAgreement
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound : Nat)
    (hOutside :
      overlapBound < (Finset.univ.filter fun x : Point => x ∉ D).card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound) :
    Function.Injective (nwGraphOff code D) := by
  classical
  intro a b hgraph
  by_contra hne
  have hagreeOutside := agrees_off_window_of_nwGraphOff_eq code D hgraph
  have hsubset :
      (Finset.univ.filter fun x : Point => x ∉ D) ⊆ nwAgreementSet code a b := by
    intro x hx
    have hxD : x ∉ D := (Finset.mem_filter.mp hx).2
    simp [nwAgreementSet, hagreeOutside x hxD]
  have hcard :
      (Finset.univ.filter fun x : Point => x ∉ D).card <=
        (nwAgreementSet code a b).card :=
    Finset.card_le_card hsubset
  have : (Finset.univ.filter fun x : Point => x ∉ D).card <= overlapBound :=
    le_trans hcard (hlow a b hne)
  exact (not_lt_of_ge this) hOutside

/-- Indicator coefficient rows for private residual graph supports.

This is the coefficient-row model after the NW derivative-window argument has
shown that each selected derivative row has exactly one residual graph pivot.
-/
def nwResidualIndicatorRows
    [Fintype Value]
    (code : Label -> Point -> Value) (D : Finset Point) :
    Label -> Finset (Point × Value) -> ℚ :=
  fun a m => if m = nwGraphOff code D a then 1 else 0

/-- The residual row has coefficient `1` at its own pivot. -/
theorem nwResidualIndicatorRows_self
    [Fintype Value]
    (code : Label -> Point -> Value) (D : Finset Point) :
    ∀ a, nwResidualIndicatorRows code D a (nwGraphOff code D a) ≠ 0 := by
  intro a
  simp [nwResidualIndicatorRows]

/-- Injective residual pivots vanish off the diagonal. -/
theorem nwResidualIndicatorRows_offdiag
    [Fintype Value]
    (code : Label -> Point -> Value) (D : Finset Point)
    (hinj : Function.Injective (nwGraphOff code D)) :
    ∀ a b, a ≠ b ->
      nwResidualIndicatorRows code D b (nwGraphOff code D a) = 0 := by
  intro a b hne
  have hpivot_ne : nwGraphOff code D a ≠ nwGraphOff code D b := by
    intro h
    exact hne (hinj h)
  simp [nwResidualIndicatorRows, hpivot_ne]

/-- Low agreement constructs the leading-support hypotheses needed by the
generic algebraic SPDP pivot engine. -/
def NWSPDPIndependenceCertificate.ofLowAgreementResidualPivots
    [Fintype Label] [Fintype Value]
    {numVars degree kappa ell : Nat}
    (support : NWLeadingSupportData)
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound spdpRank : Nat)
    (support_lower_le_labels : support.lower <= Fintype.card Label)
    (hOutside :
      overlapBound < (Finset.univ.filter fun x : Point => x ∉ D).card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound)
    (span_rank_le_spdp :
      (Set.range (nwResidualIndicatorRows code D)).finrank ℚ <= spdpRank) :
    NWSPDPIndependenceCertificate numVars degree kappa ell :=
  let hinj := nwGraphOff_injective_of_lowAgreement code D overlapBound hOutside hlow
  NWSPDPIndependenceCertificate.ofLeadingSupport
    support
    (nwResidualIndicatorRows code D)
    (nwGraphOff code D)
    (nwResidualIndicatorRows_self code D)
    (nwResidualIndicatorRows_offdiag code D hinj)
    spdpRank
    support_lower_le_labels
    span_rank_le_spdp

/-! ## Axiom audit -/

#print axioms exists_disagreement_in_large_window
#print axioms nwGraphOff_injective_of_lowAgreement
#print axioms nwResidualIndicatorRows_offdiag
#print axioms NWSPDPIndependenceCertificate.ofLowAgreementResidualPivots

end GraphDesign

end PallLean.Paper93.DeepMath.AlgebraicSPDP
