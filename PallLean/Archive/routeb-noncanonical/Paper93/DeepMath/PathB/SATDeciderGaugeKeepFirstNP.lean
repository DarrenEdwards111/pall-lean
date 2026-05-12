import PallLean.Paper93.DeepMath.PathB.ProjectedNPIdentityPreservationProgress
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeCandidate

/-!
# NP identity-minor preservation for the keep-first gauge candidate

This file specializes the reusable projected NP-preservation criterion from
`ProjectedNPIdentityPreservationProgress` to the concrete keep-first candidate
from `SATDeciderGaugeCandidate`.

The main positive result is conditional in exactly the paper-faithful way:
if the keep-first projection fixes an embedded source obstruction, the compiled
polynomial extracts to that same fixed image, and the source carries the
identity-minor lower bound, then the keep-first candidate satisfies the flat
`SATDeciderGaugeNPIdentityMinorPreservation` field.

The file also records the exact obstruction: under a `DecidesSAT M` hypothesis,
NP preservation for keep-first is equivalent to the projected lower bound for
the gauged compiled polynomial.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Keep-first fixes an embedded coupled-sheet obstruction if every ambient
variable of the embedded obstruction is among the kept variables. -/
theorem satDeciderGaugeKeepFirstProjection_fixed_embed_of_embedded_vars_keepFirst
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hvars :
      ∀ i ∈ (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q).vars,
        PiStarConcrete.keepFirstK 1 i) :
    satDeciderGaugeKeepFirstProjection M n hn2 htb hns
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q) =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q := by
  unfold satDeciderGaugeKeepFirstProjection
  apply PiStarConcrete.piZero_eq_self_of_support_kept
  exact PiStarConcrete.support_kept_of_vars_kept
    (PiStarConcrete.keepFirstK 1) hvars

/-- Source-variable support form of the fixed-embed criterion.  Since
`CoupledSheetPoly.embed` is `rename σ.inlU`, it is enough that every source
variable used by `Q` maps to a keep-first ambient variable. -/
theorem satDeciderGaugeKeepFirstProjection_fixed_embed_of_source_vars_keepFirst
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hvars :
      ∀ i ∈ Q.vars,
        PiStarConcrete.keepFirstK 1
          ((flatCookLevinUVSplit M n hn2 htb hns).inlU i)) :
    satDeciderGaugeKeepFirstProjection M n hn2 htb hns
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q) =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q := by
  apply satDeciderGaugeKeepFirstProjection_fixed_embed_of_embedded_vars_keepFirst
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

/-- Keep-first specialization of the projected lower-bound criterion. -/
theorem satDeciderGaugeKeepFirstProjection_projected_compiled_lower_bound_of_fixed_embed_extraction_source
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hfix :
      satDeciderGaugeKeepFirstProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      satDeciderGaugeKeepFirstProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        satDeciderGaugeKeepFirstProjection M n hn2 htb hns
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
        (satDeciderGaugeKeepFirstProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  exact flatProjectedCompiledLowerBound_of_fixed_embed_extraction_source
    M n hn2 htb hns Q
    (satDeciderGaugeKeepFirstProjection M n hn2 htb hns)
    hfix hextract hsource

/-- Main keep-first NP preservation theorem under the explicit fixed-embed,
extraction, and source identity-minor hypotheses. -/
theorem satDeciderGaugeKeepFirstProjection_npIdentityMinorPreservation_of_fixed_embed_extraction_source
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hfix :
      satDeciderGaugeKeepFirstProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      satDeciderGaugeKeepFirstProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        satDeciderGaugeKeepFirstProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) := by
  exact satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_source
    M n hn2 htb hns Q
    (satDeciderGaugeKeepFirstProjection M n hn2 htb hns)
    hfix hextract hsource

/-- Same theorem with the fixed-embed hypothesis discharged by the source
variable support criterion for keep-first. -/
theorem satDeciderGaugeKeepFirstProjection_npIdentityMinorPreservation_of_source_vars_extraction_source
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hvars :
      ∀ i ∈ Q.vars,
        PiStarConcrete.keepFirstK 1
          ((flatCookLevinUVSplit M n hn2 htb hns).inlU i))
    (hextract :
      satDeciderGaugeKeepFirstProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        satDeciderGaugeKeepFirstProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) := by
  refine
    satDeciderGaugeKeepFirstProjection_npIdentityMinorPreservation_of_fixed_embed_extraction_source
      M n hn2 htb hns Q ?_ hextract hsource
  exact satDeciderGaugeKeepFirstProjection_fixed_embed_of_source_vars_keepFirst
    M n hn2 htb hns Q hvars

/-- Exact criterion: with a SAT-decider hypothesis available, keep-first NP
preservation is exactly the projected lower bound on the keep-first image of
the compiled polynomial. -/
theorem satDeciderGaugeKeepFirstProjection_npIdentityMinorPreservation_iff_projected_compiled_lower_bound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
        (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) ↔
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (satDeciderGaugeKeepFirstProjection M n hn2 htb hns
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  exact satDeciderGaugeNPIdentityMinorPreservation_iff_projected_compiled_lower_bound
    M n hn2 htb hns
    (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) hdec

/-- Exact obstruction: if the keep-first projected lower bound fails for a
SAT-decider, then keep-first cannot satisfy NP identity-minor preservation. -/
theorem satDeciderGaugeKeepFirstProjection_not_npIdentityMinorPreservation_of_projected_compiled_lower_bound_fails
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hfail :
      ¬ Nat.choose (n / 3) (Nat.log 2 n) ≤
          mlBlockedSpdpRank
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (satDeciderGaugeKeepFirstProjection M n hn2 htb hns
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) :
    ¬ SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) := by
  intro hpres
  exact hfail
    ((satDeciderGaugeKeepFirstProjection_npIdentityMinorPreservation_iff_projected_compiled_lower_bound
      M n hn2 htb hns hdec).mp hpres)

end PallLean.Paper93.DeepMath.PathB
