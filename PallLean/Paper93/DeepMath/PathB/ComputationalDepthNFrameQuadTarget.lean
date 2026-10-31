import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadHpair

/-!
# N-Frame: the target-block scaffold decode — `gDecode_target` and the `hpkg` discharge

Route H drag rung (… → drag-geometry hpair → **target decode**).  The last non-trivial read:
the target block's decode under the row/probe mix is the scaffold image plus the E-selected
priced literals.  With it, the per-pair package `hpkg` of `gParity_multi_drag` is discharged
for the quadratic drag geometry.

  `gDecode_target` — **PROVED**: the target block decodes to
        `((SC-filter ∪ SCrow) ∪ E-selection).image code` (mirror of the affine `decode_cstar_eq`,
        codebook-agnostic).
  `gRowOf_target_insert` — **PROVED**: for a pair differing at the target block only at the
        priced position, the primed target decode is the un-primed one with the quadratic
        literal inserted — the `hBk'` of the multi-difference engine.
These are the two target-block reads the per-pair `hpkg` discharge composes: `gDecode_target`
gives the target's scaffold decode (feeding `Tsh` for `homogeneous_hpair_kit`), and
`gRowOf_target_insert` gives the single-insert `hBk'` for `gParity_pair_dist_multi`.

## Honest scope — what this closes (Route H)

With `gDecode_target`/`gRowOf_target_insert` every read the multi-difference engine
(`gParity_pair_dist_multi`) needs is now in hand: the kit blanket (`gDecode_kit_mem`), the
reserve identity (`gDecode_pin_eq`), the origin cut (`homogeneous_hpair_kit`), and now the
target decode and its single-insert.  The remaining step is the per-pair composition
`gParity_quad_pair` (threading `rowOf_read_target`/`probeOn` reads through the engine) and
feeding it to `gParity_tuple_drag` — mechanical bookkeeping over these reads, under the
placement hypotheses (`hVS`/`hlive`/`hTautProbe`, the concentration-conditional class).  The
concentration analysis at the raised local rank — whether the priced mass `|V|` is `Θ(N)` at a
real balanced cut — is the open gate.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadTarget

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityProbe
open PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint
open PallLean.Paper93.DeepMath.PathB.NFrameQuadLayout
open PallLean.Paper93.DeepMath.PathB.NFrameQuadRowOf
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

set_option maxHeartbeats 1600000 in
/-- **THE TARGET DECODE (proved)**: the target block decodes to the scaffold image plus the
`E`-selected priced literals (mirror of the affine `decode_cstar_eq`, codebook-agnostic). -/
theorem gDecode_target (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m)
    (S : Finset (Fin N)) (y : Fin N → Bool)
    (E : Finset (Fin m × Fin L)) (SCrow : Finset (Fin L))
    (hKnc : cstar ∉ KB) (hPnc : cstar ∉ PB)
    (hEside : ∀ i : Fin L, (cstar, i) ∈ E → xbit hfit cstar i ∉ Sᶜ)
    (hSCrow : ∀ i ∈ SCrow, xbit hfit cstar i ∉ Sᶜ)
    (hyE : ∀ i : Fin L, xbit hfit cstar i ∉ Sᶜ →
      (y (xbit hfit cstar i) = true ↔ ((cstar, i) ∈ E ∨ i ∈ SCrow))) :
    gDecodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) cstar
      = (((SC.filter (fun i => xbit hfit cstar i ∈ Sᶜ)) ∪ SCrow)
          ∪ (Finset.univ.filter (fun i : Fin L => (cstar, i) ∈ E))).image code := by
  unfold gDecodeBlock
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  by_cases hmem : xbit hfit cstar i ∈ Sᶜ
  · rw [mix_read_probe _ _ hmem]
    constructor
    · intro hon
      unfold probeOn at hon
      have hP := of_decide_eq_true hon
      rcases hP with ⟨c', hc', heq⟩ | ⟨c', hc', heq⟩ | ⟨i', hi', heq⟩
      · obtain ⟨hcc, -⟩ := xbit_inj hfit heq
        exact absurd (by rw [hcc]; exact hc') hKnc
      · obtain ⟨hcc, -⟩ := xbit_inj hfit heq
        exact absurd (by rw [hcc]; exact hc') hPnc
      · obtain ⟨-, hii⟩ := xbit_inj hfit heq
        left; left
        refine ⟨?_, hmem⟩
        rw [hii]; exact hi'
    · rintro ((hsc | hscr) | hE)
      · unfold probeOn
        exact decide_eq_true (Or.inr (Or.inr ⟨i, hsc.1, rfl⟩))
      · exact absurd hmem (fun hc => (hSCrow i hscr) hc)
      · exact absurd hmem (fun hc => (hEside i hE) hc)
  · rw [mix_read_row _ _ hmem]
    constructor
    · intro hon
      rcases (hyE i hmem).mp hon with h | h
      · right; exact h
      · left; right; exact h
    · rintro ((hsc | hscr) | hE)
      · exact absurd hsc.2 hmem
      · exact (hyE i hmem).mpr (Or.inr hscr)
      · exact (hyE i hmem).mpr (Or.inl hE)

set_option maxHeartbeats 1600000 in
/-- **THE TARGET INSERT (proved)**: with the priced target position the only priced position
of the block, the primed target decode is the un-primed one with the quadratic literal
inserted. -/
theorem gRowOf_target_insert (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m) (istar : Fin L) (i j : Fin v)
    (S : Finset (Fin N)) (y y' : Fin N → Bool)
    (E E' : Finset (Fin m × Fin L)) (SCrow : Finset (Fin L))
    (hKnc : cstar ∉ KB) (hPnc : cstar ∉ PB)
    (hcode : code istar = GLit.quad i j 1)
    (hEE' : E' = insert (cstar, istar) E)
    (hnotE : (cstar, istar) ∉ E)
    (hEside : ∀ k : Fin L, (cstar, k) ∈ E → xbit hfit cstar k ∉ Sᶜ)
    (hpos : xbit hfit cstar istar ∉ Sᶜ)
    (hSCrow : ∀ k ∈ SCrow, xbit hfit cstar k ∉ Sᶜ)
    (histarSC : istar ∉ SCrow)
    (hyE : ∀ k : Fin L, xbit hfit cstar k ∉ Sᶜ →
      (y (xbit hfit cstar k) = true ↔ ((cstar, k) ∈ E ∨ k ∈ SCrow)))
    (hyE' : ∀ k : Fin L, xbit hfit cstar k ∉ Sᶜ →
      (y' (xbit hfit cstar k) = true ↔ ((cstar, k) ∈ E' ∨ k ∈ SCrow))) :
    gDecodeBlock code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y') cstar
      = insert (GLit.quad i j 1)
        (gDecodeBlock code hfit
          (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) cstar) := by
  have hE'side : ∀ k : Fin L, (cstar, k) ∈ E' → xbit hfit cstar k ∉ Sᶜ := by
    intro k hk
    rw [hEE', Finset.mem_insert] at hk
    rcases hk with hk | hk
    · rw [(Prod.mk.injEq _ _ _ _).mp hk |>.2]
      exact hpos
    · exact hEside k hk
  rw [gDecode_target code hfit tautIdx pinIdx SC KB PB cstar S y' E' SCrow
      hKnc hPnc hE'side hSCrow hyE',
    gDecode_target code hfit tautIdx pinIdx SC KB PB cstar S y E SCrow
      hKnc hPnc hEside hSCrow hyE,
    ← hcode]
  rw [← Finset.image_insert]
  congr 1
  ext k
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ((hsc | hscr) | hE')
    · exact Or.inr (Or.inl (Or.inl hsc))
    · exact Or.inr (Or.inl (Or.inr hscr))
    · rw [hEE', Finset.mem_insert] at hE'
      rcases hE' with hk | hk
      · rw [Prod.mk.injEq] at hk
        exact Or.inl hk.2
      · exact Or.inr (Or.inr hk)
  · rintro (rfl | ((hsc | hscr) | hE))
    · refine Or.inr ?_
      rw [hEE']
      exact Finset.mem_insert_self _ _
    · exact Or.inl (Or.inl hsc)
    · exact Or.inl (Or.inr hscr)
    · refine Or.inr ?_
      rw [hEE', Finset.mem_insert]
      exact Or.inr hE

end PallLean.Paper93.DeepMath.PathB.NFrameQuadTarget

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadTarget.gDecode_target
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadTarget.gRowOf_target_insert
