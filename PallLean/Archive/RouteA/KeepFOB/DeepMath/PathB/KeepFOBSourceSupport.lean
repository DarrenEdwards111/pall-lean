import PallLean.Paper93.DeepMath.PathB.ProjectedNPIdentityPreservationProgress

/-!
# Source support frontier for keep-FOB fixed embeds

This file isolates the support obligation needed to use the keep-FOB
projection in the projected NP identity-minor route.

It does not prove that the concrete Cook-Levin verifier sheet has only
first-of-block variables.  Instead it records the exact checked frontier:
if every variable in `Q.vars` is first-of-block, equivalently if every embedded
source variable is kept by `PiStarConcrete.keepFOB`, then `piZero keepFOB`
fixes `CoupledSheetPoly.embed σ Q`.  The final theorem plugs that fixedness
into the existing fixed-embed NP-preservation criterion.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

namespace KeepFOBSourceSupport

/-- Source-side first-of-block support: every variable used by `Q` has an
index divisible by `3`. -/
def SourceVarsFOB (σ : UVSplit) (Q : CoupledSheetPoly σ) : Prop :=
  ∀ i ∈ Q.vars, 3 ∣ i.val

/-- The same support obligation after applying the canonical embedding map
`σ.inlU` to source variables. -/
def SourceVarsMapToKeepFOB (σ : UVSplit) (Q : CoupledSheetPoly σ) : Prop :=
  ∀ i ∈ Q.vars, PiStarConcrete.keepFOB (σ.inlU i)

/-- Ambient embedded-variable support obligation. -/
def EmbeddedVarsKeepFOB (σ : UVSplit) (Q : CoupledSheetPoly σ) : Prop :=
  ∀ k ∈ (CoupledSheetPoly.embed σ Q).vars, PiStarConcrete.keepFOB k

/-- Since `σ.inlU i` has the same numeric value as `i`, source-side FOB
support is exactly the mapped-source keep-FOB support obligation. -/
theorem sourceVarsMapToKeepFOB_iff_sourceVarsFOB
    (σ : UVSplit) (Q : CoupledSheetPoly σ) :
    SourceVarsMapToKeepFOB σ Q ↔ SourceVarsFOB σ Q := by
  constructor
  · intro h i hi
    have hi_keep := h i hi
    unfold PiStarConcrete.keepFOB at hi_keep
    exact hi_keep
  · intro h i hi
    unfold PiStarConcrete.keepFOB
    exact h i hi

/-- Embedded variables are kept if every source variable maps to a keep-FOB
ambient variable. -/
theorem embeddedVarsKeepFOB_of_sourceVarsMapToKeepFOB
    (σ : UVSplit) (Q : CoupledSheetPoly σ)
    (hvars : SourceVarsMapToKeepFOB σ Q) :
    EmbeddedVarsKeepFOB σ Q := by
  intro k hk
  have hk' : k ∈ (MvPolynomial.rename σ.inlU Q).vars := by
    simpa [CoupledSheetPoly.embed] using hk
  obtain ⟨i, hi, hik⟩ := MvPolynomial.mem_vars_rename σ.inlU Q hk'
  rw [← hik]
  exact hvars i hi

/-- Source-side FOB support implies embedded-variable keep-FOB support. -/
theorem embeddedVarsKeepFOB_of_sourceVarsFOB
    (σ : UVSplit) (Q : CoupledSheetPoly σ)
    (hvars : SourceVarsFOB σ Q) :
    EmbeddedVarsKeepFOB σ Q :=
  embeddedVarsKeepFOB_of_sourceVarsMapToKeepFOB σ Q
    ((sourceVarsMapToKeepFOB_iff_sourceVarsFOB σ Q).mpr hvars)

/-- If all embedded variables satisfy `keepFOB`, then `piZero keepFOB` fixes
the embedded coupled-sheet polynomial. -/
theorem keepFOB_piZero_fixed_embed_of_embedded_vars
    (σ : UVSplit) (Q : CoupledSheetPoly σ)
    (hvars : EmbeddedVarsKeepFOB σ Q) :
    PiStarConcrete.piZero PiStarConcrete.keepFOB (CoupledSheetPoly.embed σ Q) =
      CoupledSheetPoly.embed σ Q := by
  apply PiStarConcrete.piZero_eq_self_of_support_kept
  exact PiStarConcrete.support_kept_of_vars_kept
    PiStarConcrete.keepFOB hvars

/-- Mapped-source support form of the keep-FOB fixed-embed criterion. -/
theorem keepFOB_piZero_fixed_embed_of_sourceVarsMapToKeepFOB
    (σ : UVSplit) (Q : CoupledSheetPoly σ)
    (hvars : SourceVarsMapToKeepFOB σ Q) :
    PiStarConcrete.piZero PiStarConcrete.keepFOB (CoupledSheetPoly.embed σ Q) =
      CoupledSheetPoly.embed σ Q :=
  keepFOB_piZero_fixed_embed_of_embedded_vars σ Q
    (embeddedVarsKeepFOB_of_sourceVarsMapToKeepFOB σ Q hvars)

/-- Source-side FOB support form of the keep-FOB fixed-embed criterion. -/
theorem keepFOB_piZero_fixed_embed_of_sourceVarsFOB
    (σ : UVSplit) (Q : CoupledSheetPoly σ)
    (hvars : SourceVarsFOB σ Q) :
    PiStarConcrete.piZero PiStarConcrete.keepFOB (CoupledSheetPoly.embed σ Q) =
      CoupledSheetPoly.embed σ Q :=
  keepFOB_piZero_fixed_embed_of_embedded_vars σ Q
    (embeddedVarsKeepFOB_of_sourceVarsFOB σ Q hvars)

/-- Flat Cook-Levin keep-FOB projection used by the source-support frontier. -/
noncomputable def satDeciderGaugeKeepFOBSourceProjection
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  PiStarConcrete.piZero PiStarConcrete.keepFOB

/-- Flat fixed-embed criterion from mapped-source keep-FOB support. -/
theorem satDeciderGaugeKeepFOBSourceProjection_fixed_embed_of_sourceVarsMapToKeepFOB
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hvars :
      SourceVarsMapToKeepFOB (flatCookLevinUVSplit M n hn2 htb hns) Q) :
    satDeciderGaugeKeepFOBSourceProjection M n hn2 htb hns
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q) =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q := by
  unfold satDeciderGaugeKeepFOBSourceProjection
  exact keepFOB_piZero_fixed_embed_of_sourceVarsMapToKeepFOB
    (flatCookLevinUVSplit M n hn2 htb hns) Q hvars

/-- Flat fixed-embed criterion from source-side FOB support on `Q.vars`. -/
theorem satDeciderGaugeKeepFOBSourceProjection_fixed_embed_of_sourceVarsFOB
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hvars : SourceVarsFOB (flatCookLevinUVSplit M n hn2 htb hns) Q) :
    satDeciderGaugeKeepFOBSourceProjection M n hn2 htb hns
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q) =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q := by
  unfold satDeciderGaugeKeepFOBSourceProjection
  exact keepFOB_piZero_fixed_embed_of_sourceVarsFOB
    (flatCookLevinUVSplit M n hn2 htb hns) Q hvars

/-- Keep-FOB NP preservation reduced to the exact `Q.vars` support obligation,
the extraction identity, and the existing source identity-minor lower bound. -/
theorem satDeciderGaugeKeepFOBSourceProjection_npIdentityMinorPreservation_of_sourceVarsFOB_extraction_source
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hvars : SourceVarsFOB (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      satDeciderGaugeKeepFOBSourceProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        satDeciderGaugeKeepFOBSourceProjection M n hn2 htb hns
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeKeepFOBSourceProjection M n hn2 htb hns) := by
  refine satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_source
    M n hn2 htb hns Q
    (satDeciderGaugeKeepFOBSourceProjection M n hn2 htb hns)
    ?_ hextract hsource
  exact satDeciderGaugeKeepFOBSourceProjection_fixed_embed_of_sourceVarsFOB
    M n hn2 htb hns Q hvars

end KeepFOBSourceSupport

end PallLean.Paper93.DeepMath.PathB
