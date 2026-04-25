import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeKeepFOB
import PallLean.Paper93.DeepMath.PathB.ProjectedNPIdentityPreservationProgress

/-!
# NP identity-minor preservation for the keep-FOB gauge candidate

This file specializes the reusable projected NP-preservation criterion from
`ProjectedNPIdentityPreservationProgress` to the concrete first-of-block
candidate `PiStarConcrete.keepFOB`.

The positive result is deliberately conditional: if the keep-FOB projection
fixes an embedded source obstruction, the compiled polynomial extracts to that
same fixed image, and the source carries the identity-minor lower bound, then
the keep-FOB candidate satisfies the flat
`SATDeciderGaugeNPIdentityMinorPreservation` field.

No claim is made here that the Cook-Levin source variables are actually FOB,
and no final `Π⋆` witness is constructed.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Keep-FOB fixes an embedded coupled-sheet obstruction if every ambient
variable of the embedded obstruction is kept by `PiStarConcrete.keepFOB`. -/
theorem satDeciderGaugeKeepFOBProjection_fixed_embed_of_embedded_vars_keepFOB
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hvars :
      ∀ i ∈ (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q).vars,
        PiStarConcrete.keepFOB i) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q) =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q := by
  unfold satDeciderGaugeKeepFOBProjection
  apply PiStarConcrete.piZero_eq_self_of_support_kept
  exact PiStarConcrete.support_kept_of_vars_kept
    PiStarConcrete.keepFOB hvars

/-- Source-variable support form of the fixed-embed criterion. Since
`CoupledSheetPoly.embed` is `rename σ.inlU`, it is enough to assume each
source variable used by `Q` maps to a keep-FOB ambient variable. -/
theorem satDeciderGaugeKeepFOBProjection_fixed_embed_of_source_vars_keepFOB
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hvars :
      ∀ i ∈ Q.vars,
        PiStarConcrete.keepFOB
          ((flatCookLevinUVSplit M n hn2 htb hns).inlU i)) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q) =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q := by
  apply satDeciderGaugeKeepFOBProjection_fixed_embed_of_embedded_vars_keepFOB
  intro k hk
  have hk' :
      k ∈ (MvPolynomial.rename
          (flatCookLevinUVSplit M n hn2 htb hns).inlU Q).vars := by
    simpa [CoupledSheetPoly.embed] using hk
  obtain ⟨i, hi, hik⟩ :=
    MvPolynomial.mem_vars_rename
      (flatCookLevinUVSplit M n hn2 htb hns).inlU Q hk'
  rw [← hik]
  exact hvars i hi

/-- Keep-FOB specialization of the projected lower-bound criterion. -/
theorem satDeciderGaugeKeepFOBProjection_projected_compiled_lower_bound_of_fixed_embed_extraction_source
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hfix :
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  exact flatProjectedCompiledLowerBound_of_fixed_embed_extraction_source
    M n hn2 htb hns Q
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)
    hfix hextract hsource

/-- Main keep-FOB NP preservation theorem under the explicit fixed-embed,
extraction, and source identity-minor hypotheses. -/
theorem satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation_of_fixed_embed_extraction_source
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hfix :
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) := by
  exact satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_source
    M n hn2 htb hns Q
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)
    hfix hextract hsource

/-- Same theorem with the fixed-embed hypothesis discharged by the source
variable support criterion for keep-FOB. -/
theorem satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation_of_source_vars_extraction_source
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hvars :
      ∀ i ∈ Q.vars,
        PiStarConcrete.keepFOB
          ((flatCookLevinUVSplit M n hn2 htb hns).inlU i))
    (hextract :
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) := by
  refine
    satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation_of_fixed_embed_extraction_source
      M n hn2 htb hns Q ?_ hextract hsource
  exact satDeciderGaugeKeepFOBProjection_fixed_embed_of_source_vars_keepFOB
    M n hn2 htb hns Q hvars

/-- Exact criterion: with a SAT-decider hypothesis available, keep-FOB NP
preservation is exactly the projected lower bound on the keep-FOB image of the
compiled polynomial. -/
theorem satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation_iff_projected_compiled_lower_bound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) ↔
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  exact satDeciderGaugeNPIdentityMinorPreservation_iff_projected_compiled_lower_bound
    M n hn2 htb hns
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) hdec

/-- Exact obstruction: if the keep-FOB projected lower bound fails for a
SAT-decider, then keep-FOB cannot satisfy NP identity-minor preservation. -/
theorem satDeciderGaugeKeepFOBProjection_not_npIdentityMinorPreservation_of_projected_compiled_lower_bound_fails
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hfail :
      ¬ Nat.choose (n / 3) (Nat.log 2 n) ≤
          mlBlockedSpdpRank
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) :
    ¬ SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) := by
  intro hpres
  exact hfail
    ((satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation_iff_projected_compiled_lower_bound
      M n hn2 htb hns hdec).mp hpres)

end PallLean.Paper93.DeepMath.PathB
