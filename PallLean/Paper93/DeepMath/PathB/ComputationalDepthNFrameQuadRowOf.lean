import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadAssembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityProbe
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityAssembly

/-!
# N-Frame: the explicit quadratic row family — discharging `hpkg` (28g construction)

Route H drag rung (… → quadratic product assembly → **explicit row family**).  The concrete
`gRowOf`/`gProbe` construction that discharges `gParity_multi_drag`'s per-pair package `hpkg`.
The position-based row (`rowOf`) and probe (`probeOn`) are codebook-agnostic and are reused
verbatim from the affine 28g; only the `GLit` DECODE facts are new.

  `gDecode_kit_mem` — **PROVED**: a kit block (probe-taut or row-taut ON) decodes to contain
        the tautology `GLit.aff 0 0`.
  `gDecode_pin_eq` — **PROVED**: a reserve pin block (selector live, row all-OFF) decodes to
        exactly its singleton pin literal — so both rows of a pair decode identically there.
  `gDecode_kit_row` — **PROVED**: a kit data block on the ROW side (taut row-side ON) decodes
        to contain the tautology, for the `rowOf` family.

## Honest scope — what this closes (Route H)

These are the `GLit` decode reads that a full `gParity_assembled_pair`/`_drag` (mirroring the
affine 28g) composes to discharge `hpkg`: the kit blanket (`gDecode_kit_mem`/`gDecode_kit_row`)
gives the multi-difference absorption, the reserve identity (`gDecode_pin_eq` for both rows)
gives `hres`, and the homogeneous supply gives `hpair`.  The remaining glue — the target-block
`Tsh ∪ Tt` decode and the full per-pair assembly under the placement hypotheses
(`hTautProbe`/`hlive`/`hVS`, the concentration-conditional class) — is the 28g bookkeeping over
these reads.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadRowOf

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityProbe
open PallLean.Paper93.DeepMath.PathB.NFrameParityAssembly
open PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint
open PallLean.Paper93.DeepMath.PathB.NFrameQuadLayout
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

/-- **The kit membership on a probe mix (proved)**: a kit block decodes to contain the
tautology `GLit.aff 0 0`. -/
theorem gDecode_kit_mem (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m)
    (S : Finset (Fin N)) (y : Fin N → Bool) {c : Fin m} (hc : c ∈ KB)
    (hcodeTaut : code tautIdx = GLit.aff 0 0)
    (hyKit : y (xbit hfit c tautIdx) = true) :
    GLit.aff 0 0 ∈ gDecodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c := by
  unfold gDecodeBlock
  rw [← hcodeTaut]
  apply Finset.mem_image_of_mem
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hmem : xbit hfit c tautIdx ∈ Sᶜ
  · rw [mix_read_probe _ _ hmem]
    exact probeOn_read_kit hfit tautIdx pinIdx SC KB PB cstar hc
  · rw [mix_read_row _ _ hmem]
    exact hyKit

/-- **The reserve pin decode (proved)**: a reserve pin block with its selector live and row-
side all-OFF decodes to exactly its singleton pin literal. -/
theorem gDecode_pin_eq (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m)
    (S : Finset (Fin N)) (y : Fin N → Bool) {c : Fin m} (hc : c ∈ PB)
    (hKP : c ∉ KB) (hcs : c ≠ cstar)
    (hlive : xbit hfit c (pinIdx c) ∈ Sᶜ)
    (hyPin : ∀ i : Fin L, y (xbit hfit c i) = false) :
    gDecodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c
      = {code (pinIdx c)} := by
  unfold gDecodeBlock
  ext ℓ
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hmem : xbit hfit c i ∈ Sᶜ
    · rw [mix_read_probe _ _ hmem] at hi
      unfold probeOn at hi
      have hP := of_decide_eq_true hi
      rcases hP with ⟨c', hc', heq⟩ | ⟨c', hc', heq⟩ | ⟨i', hi', heq⟩
      · obtain ⟨hcc, -⟩ := xbit_inj hfit heq
        exact absurd (by rw [hcc]; exact hc') hKP
      · obtain ⟨hcc, hii⟩ := xbit_inj hfit heq
        rw [hii, ← hcc]
      · obtain ⟨hcc, -⟩ := xbit_inj hfit heq
        exact absurd hcc hcs
    · rw [mix_read_row _ _ hmem, hyPin i] at hi
      exact absurd hi Bool.false_ne_true
  · rintro rfl
    refine ⟨pinIdx c, ?_, rfl⟩
    rw [mix_read_probe _ _ hlive]
    exact probeOn_read_pin hfit tautIdx pinIdx SC KB PB cstar hc

/-- **The kit membership on the row family (proved)**: a non-reserve block whose tautology is
row-side ON (the `rowOf` kit blanket) decodes to contain the tautology. -/
theorem gDecode_kit_row (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (RS : Finset (Fin m)) (SCR : Finset (Fin m × Fin L))
    (E : Finset (Fin m × Fin L))
    (S : Finset (Fin N)) (x : Fin N → Bool) {c : Fin m} (hc : c ∉ RS)
    (hcodeTaut : code tautIdx = GLit.aff 0 0)
    (htautRow : xbit hfit c tautIdx ∉ Sᶜ) :
    GLit.aff 0 0 ∈ gDecodeBlock code hfit
      (mixOn Sᶜ x (rowOf hfit tautIdx RS SCR E)) c := by
  unfold gDecodeBlock
  rw [← hcodeTaut]
  apply Finset.mem_image_of_mem
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [mix_read_row _ _ htautRow]
  exact rowOf_read_kit hfit tautIdx RS SCR E hc

end PallLean.Paper93.DeepMath.PathB.NFrameQuadRowOf

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadRowOf.gDecode_kit_mem
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadRowOf.gDecode_pin_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadRowOf.gDecode_kit_row
