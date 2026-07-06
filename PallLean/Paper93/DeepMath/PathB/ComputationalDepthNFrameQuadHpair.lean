import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadRowOf

/-!
# N-Frame: the drag-geometry origin cut — `hpair` for kit + reserve (28g glue)

Route H drag rung (… → GLit decode reads → **drag-geometry hpair**).  `homogeneous_hpair`
(the supply) proved the origin cut `{0, w}` when EVERY non-target block is the homogeneous
pin.  The multi-difference drag geometry is different: the non-target blocks split into a
small RESERVE set of homogeneous pins and a KIT BLANKET of data blocks (always satisfied).
This proves the `hpair` package of `gParity_pair_dist_multi` in that geometry — the last
non-mechanical piece of the `hpkg` discharge.

  `homogeneous_hpair_kit` — **PROVED**: with the reserve blocks the homogeneous pin
        `aff (e_i + e_j) 0` and the other non-target blocks kit (carry `aff 0 0`), the
        non-target predicate plus the off-support scaffold-false condition cut the witness to
        exactly `{0, e_i + e_j}` — the kit blocks contribute nothing, the reserve pins force
        `a_i + a_j = 0`, the scaffold forces `a_k = 0` off `{i,j}`.

## Honest scope — what this closes (Route H)

With the decode reads (`gDecode_kit_mem`/`gDecode_pin_eq`, giving the kit blanket and the
reserve identity) and this `hpair`, the per-pair `hpkg` of `gParity_multi_drag` is dischargeable
in the drag geometry: only the target-block `Tsh ∪ Tt` decode (the single-insert of the
quadratic literal at the target, a `gParity_detect_layout`-style read) and the placement
hypotheses (`hTautProbe`/`hlive`/`hVS`, the concentration-conditional class) remain — pure
bookkeeping over the reads.  The concentration analysis at the raised local rank is the open
gate.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadHpair

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint
open PallLean.Paper93.DeepMath.PathB.NFrameQuadSupply
open PallLean.Paper93.DeepMath.PathB.NFrameQuadAssembly

variable {v m : ℕ}

set_option maxHeartbeats 1600000 in
/-- **THE DRAG-GEOMETRY ORIGIN CUT (proved)**: reserve blocks the homogeneous pin, other
non-target blocks kit; the non-target predicate + the off-support scaffold cut the witness to
`{0, e_i + e_j}`. -/
theorem homogeneous_hpair_kit (i j : Fin v) (hij : i ≠ j)
    (cstar : Fin m) (RS : Finset (Fin m)) (c₀ : Fin m)
    (hc₀RS : c₀ ∈ RS) (hc₀cs : c₀ ≠ cstar)
    (Bk : Fin m → Finset (GLit v))
    (hpinBlk : ∀ c, c ∈ RS → Bk c = {GLit.aff (single v i + single v j) 0})
    (hkitBlk : ∀ c, c ≠ cstar → c ∉ RS → GLit.aff 0 0 ∈ Bk c)
    (a : Fin v → ZMod 2) :
    ((∀ c, c ≠ cstar → gBlockSat a (Bk c))
      ∧ ∀ ℓ ∈ ((Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1)),
          ¬ gLitHolds a ℓ)
    ↔ (a = 0 ∨ a = single v i + single v j) := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  -- the pins force a_i + a_j = 0
  have hpin : (∀ c, c ≠ cstar → gBlockSat a (Bk c)) ↔ (a i + a j = 0) := by
    constructor
    · intro h
      have h0 := h c₀ hc₀cs
      rw [hpinBlk c₀ hc₀RS] at h0
      obtain ⟨ℓ, hℓ, hlit⟩ := h0
      rw [Finset.mem_singleton] at hℓ
      subst hℓ
      change dotp (single v i + single v j) a = 0 at hlit
      rw [dotp_add_left', dotp_single, dotp_single] at hlit
      exact hlit
    · intro h c hc
      by_cases hcRS : c ∈ RS
      · rw [hpinBlk c hcRS]
        refine ⟨GLit.aff (single v i + single v j) 0, Finset.mem_singleton_self _, ?_⟩
        change dotp (single v i + single v j) a = 0
        rw [dotp_add_left', dotp_single, dotp_single]
        exact h
      · exact gBlockSat_of_taut a _ (hkitBlk c hc hcRS)
  -- the scaffold forces a_k = 0 off {i,j}
  have hscaf : (∀ ℓ ∈ ((Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1)),
      ¬ gLitHolds a ℓ) ↔ (∀ k, k ≠ i → k ≠ j → a k = 0) := by
    constructor
    · intro h k hki hkj
      have hmem : GLit.aff (single v k) 1
          ∈ (Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1) := by
        apply Finset.mem_image_of_mem
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hki, hkj⟩
      have hlit := h _ hmem
      change ¬ (dotp (single v k) a = 1) at hlit
      rw [dotp_single] at hlit
      rcases hz (a k) with h0 | h1
      · exact h0
      · exact absurd h1 hlit
    · intro h ℓ hℓ hlit
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hℓ
      rw [Finset.mem_sdiff] at hk
      have hki : k ≠ i := fun hc => hk.2 (by rw [hc]; exact Finset.mem_insert_self i {j})
      have hkj : k ≠ j := fun hc =>
        hk.2 (by rw [hc]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
      change dotp (single v k) a = 1 at hlit
      rw [dotp_single, h k hki hkj] at hlit
      exact absurd hlit (by decide)
  rw [hpin, hscaf]
  exact homogeneous_pair_solution i j hij a

end PallLean.Paper93.DeepMath.PathB.NFrameQuadHpair

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadHpair.homogeneous_hpair_kit
