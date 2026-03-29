import PallLean.GodMoveMonotonicityML

/-!
# GodMoveExtractionML

A theorem-level God-Move scaffold for the current multilinear SPDP route.

This packages the exact extraction shape already supported by the proved
infrastructure in `MultilinearSPDP`:

* a restriction/projection from compiled variables to hard-object variables,
* semantic identification of the restricted compiled polynomial with the hard object,
* the resulting rank inequality.

Unlike the earlier generic scaffold, this file contains no monotonicity axioms.
Any remaining non-constructive content is isolated in the semantic equality
that identifies the restricted compiled polynomial with the desired hard object.
-/

namespace GodMoveExtractionML

open SPDP
open MultilinearSPDP
open GodMoveMonotonicityML
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Data for a multilinear God-Move extraction instance. -/
structure GodMoveData (nHard nCompiled : ℕ) where
  compiledPart : BlockPartition nCompiled
  emb : Fin nHard → Fin nCompiled
  emb_injective : Function.Injective emb
  κ : ℕ
  ℓ : ℕ
  compiledPoly : MvPolynomial (Fin nCompiled) F
  hardPoly : MvPolynomial (Fin nHard) F
  semantic : restrictPoly F emb emb_injective compiledPoly = hardPoly

/--
Paper-faithful God-Move inequality on the current multilinear route.

This is the exact statement used informally throughout the extraction layer:
restrict the compiled polynomial to the hard-object coordinates, identify the
result with the hard object, then apply restriction monotonicity.
-/
theorem godMove_extraction_rank_monotone
    {nHard nCompiled : ℕ}
    (D : GodMoveData (F := F) nHard nCompiled) :
    mlBlockedSpdpRank (pullbackPartition D.compiledPart D.emb) D.κ D.ℓ D.hardPoly
      ≤ mlBlockedSpdpRank D.compiledPart D.κ D.ℓ D.compiledPoly := by
  simpa [D.semantic] using
    (mlBlockedSpdpRank_projection_le
      (F := F)
      (f := D.emb)
      (hf := D.emb_injective)
      (B := D.compiledPart)
      (κ := D.κ)
      (ℓ := D.ℓ)
      (p := D.compiledPoly))

/--
Same-space version: if the hard object has already been renamed into the compiled
variable space, then one can compare under the common compiled partition after a
coarsening/transport step.  This theorem stays theorem-level except for the final
semantic identification.
-/
structure EmbeddedGodMoveData (nHard nCompiled : ℕ) where
  compiledPart : BlockPartition nCompiled
  emb : Fin nHard → Fin nCompiled
  emb_injective : Function.Injective emb
  κ : ℕ
  ℓ : ℕ
  compiledPoly : MvPolynomial (Fin nCompiled) F
  hardPoly : MvPolynomial (Fin nHard) F
  embeddedHard : MvPolynomial (Fin nCompiled) F
  semanticRestrict : restrictPoly F emb emb_injective compiledPoly = hardPoly
  semanticEmbed : embeddedHard = MvPolynomial.rename emb hardPoly

/--
Embedded God-Move inequality. This is often the most convenient statement for
separation proofs where the NP-side hard object is compared in the compiled
coordinate system.
-/
theorem godMove_extraction_rank_monotone_embedded
    {nHard nCompiled : ℕ}
    (D : EmbeddedGodMoveData (F := F) nHard nCompiled) :
    mlBlockedSpdpRank D.compiledPart D.κ D.ℓ D.embeddedHard
      ≤ mlBlockedSpdpRank D.compiledPart D.κ D.ℓ D.compiledPoly := by
  have h₁ :
      mlBlockedSpdpRank (pullbackPartition D.compiledPart D.emb) D.κ D.ℓ D.hardPoly
        ≤ mlBlockedSpdpRank D.compiledPart D.κ D.ℓ D.compiledPoly := by
    simpa [D.semanticRestrict] using
      (mlBlockedSpdpRank_projection_le
        (F := F)
        (f := D.emb)
        (hf := D.emb_injective)
        (B := D.compiledPart)
        (κ := D.κ)
        (ℓ := D.ℓ)
        (p := D.compiledPoly))
  have h₂ :
      mlBlockedSpdpRank D.compiledPart D.κ D.ℓ (MvPolynomial.rename D.emb D.hardPoly)
        ≤ mlBlockedSpdpRank (pullbackPartition D.compiledPart D.emb) D.κ D.ℓ D.hardPoly :=
    mlBlockedSpdpRank_rename_le' (F := F) D.emb D.emb_injective D.compiledPart D.κ D.ℓ D.hardPoly
  calc
    mlBlockedSpdpRank D.compiledPart D.κ D.ℓ D.embeddedHard
        = mlBlockedSpdpRank D.compiledPart D.κ D.ℓ (MvPolynomial.rename D.emb D.hardPoly) := by
            rw [D.semanticEmbed]
    _   ≤ mlBlockedSpdpRank (pullbackPartition D.compiledPart D.emb) D.κ D.ℓ D.hardPoly := h₂
    _   ≤ mlBlockedSpdpRank D.compiledPart D.κ D.ℓ D.compiledPoly := h₁

end GodMoveExtractionML
