import PallLean.Paper93.Paper283.RouteBTransportNPIdentityMinor

/-!
# Route B NP transport for richer finite-span gauges

This file records the NP identity-minor preservation criterion needed by a
richer finite-span Route B projection.  The criterion is deliberately stated
at the selected `CandidateGauge` surface: if the gauge fixes a finite family of
embedded identity-minor rows and the embedded coupled-sheet obstruction lies in
their span, then the gauge fixes the embedded obstruction.  With the usual
compiler extraction and source lower-bound data, this gives the exact
`RouteBSATProjectedNPIdentityMinorLowerBound` field.

No `keepFOB` projection, profile collapse, or P-side source of truth is used.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- If a selected Route B NFrame candidate fixes every row in a set, it fixes
every polynomial in the span of those rows.  This is the row-span bridge used
by finite-span projection candidates. -/
theorem routeBRicherGauge_fixed_of_mem_fixed_row_span
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (rows : Set (SATDeciderGaugeSpace M n hn2 htb hns))
    (hrows :
      ∀ p ∈ rows,
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi p = p)
  {p : SATDeciderGaugeSpace M n hn2 htb hns}
  (hp : p ∈ Submodule.span Rat rows) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi p = p := by
  exact Submodule.span_induction
    (s := rows)
    (p := fun q (_hq : q ∈ Submodule.span Rat rows) =>
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi q = q)
    (fun q hq => hrows q hq)
    (by simp)
    (by
      intro p q _hp _hq hp hq
      simp [map_add, hp, hq])
    (by
      intro a p _hp hp
      simp [map_smul, hp])
    hp

/-- A finite-row version of
`routeBRicherGauge_fixed_of_mem_fixed_row_span`, phrased in the shape expected
from a finite-span projection candidate. -/
theorem routeBRicherGauge_fixed_of_mem_fixed_finite_row_span
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    {r : Nat} (row : Fin r -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hrow :
      ∀ i,
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi (row i) =
          row i)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp : p ∈ Submodule.span Rat (Set.range row)) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi p = p := by
  exact
    routeBRicherGauge_fixed_of_mem_fixed_row_span
      M n hn2 htb hns Pi (Set.range row)
      (by
        intro p hp
        rcases hp with ⟨i, rfl⟩
        exact hrow i)
      hp

/-- Finite-span fixed-embed certificate for the Route B projected NP
identity-minor lower-bound field.

The finite rows are the data a richer projection candidate should expose: the
candidate fixes each row, the embedded coupled-sheet obstruction is in their
span, the compiled Cook-Levin polynomial extracts to that embedded
obstruction, and the source sheet carries the identity-minor lower bound. -/
structure RouteBRicherGaugeNPFixedFiniteRowSpanCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Type where
  Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns)
  rowCount : Nat
  row : Fin rowCount -> SATDeciderGaugeSpace M n hn2 htb hns
  fixes_row :
    ∀ i,
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi (row i) =
        row i
  embedded_mem_rowSpan :
    CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q ∈
      Submodule.span Rat (Set.range row)
  extracts_compiled_to_embed :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q
  source_lower_bound :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q

/-- The finite fixed-row-span certificate gives the fixed embedded obstruction
needed by the paper-faithful Route B NP transport theorem. -/
theorem routeBRicherGauge_fixed_embed_of_fixedFiniteRowSpanCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcert :
      RouteBRicherGaugeNPFixedFiniteRowSpanCertificate M n hn2 htb hns Pi) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) hcert.Q) =
      CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) hcert.Q :=
  routeBRicherGauge_fixed_of_mem_fixed_finite_row_span
    M n hn2 htb hns Pi hcert.row hcert.fixes_row
    hcert.embedded_mem_rowSpan

/-- Direct finite-row-span criterion for the Route B projected NP
identity-minor lower-bound field. -/
theorem routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_finite_row_span
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    {r : Nat} (row : Fin r -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hrow :
      ∀ i,
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi (row i) =
          row i)
    (hembed :
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q ∈
        Submodule.span Rat (Set.range row))
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  have hfix :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q :=
    routeBRicherGauge_fixed_of_mem_fixed_finite_row_span
      M n hn2 htb hns Pi row hrow hembed
  exact
    routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_extraction_source
      M n hn2 htb hns Pi Q hfix (hextract.trans hfix.symm) hsource

/-- Certificate form of
`routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_finite_row_span`. -/
theorem routeBSATProjectedNPIdentityMinorLowerBound_of_richerGaugeNPFixedFiniteRowSpanCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcert :
      RouteBRicherGaugeNPFixedFiniteRowSpanCertificate M n hn2 htb hns Pi) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  rcases hcert with
    ⟨Q, rowCount, row, hrow, hembed, hextract, hsource⟩
  exact
    routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_finite_row_span
      M n hn2 htb hns Pi Q row hrow hembed hextract hsource

/-! ## Axiom audit anchors -/

#print axioms routeBRicherGauge_fixed_of_mem_fixed_row_span
#print axioms routeBRicherGauge_fixed_of_mem_fixed_finite_row_span
#print axioms routeBRicherGauge_fixed_embed_of_fixedFiniteRowSpanCertificate
#print axioms routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_finite_row_span
#print axioms routeBSATProjectedNPIdentityMinorLowerBound_of_richerGaugeNPFixedFiniteRowSpanCertificate

end PallLean.Paper93.Paper283
