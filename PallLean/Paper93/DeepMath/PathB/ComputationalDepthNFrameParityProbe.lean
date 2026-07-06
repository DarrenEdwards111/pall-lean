import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityLayout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityPins

/-!
# N-Frame: the parity probe — supplying the detection under a cut

Rung 27 of the arc (… → parity pins → **parity probe**).  The explicit probe construction:
given a cut `S`, the probe `probeOn` turns ON exactly the kit tautologies (at kit blocks),
the per-pair pin selectors (at pin blocks), and the scaffold selectors (at the target block),
and the decoded mix is proved to have exactly the rung-26 kit/pin structure.

  `probeOn` — the explicit probe, with the four read lemmas (`_read_kit`, `_read_pin`,
        `_read_pinblock_off`, `_read_target_off`) via `xbit_inj` geometry.
  `decode_kit_mem` — **PROVED, the kit no-lose**: a kit block's tautology lands in the decode
        whether its position is probe-side (the probe sets it) or row-side (the row constant
        sets it).  Kit blocks may carry ARBITRARY other content — `blockSat_of_taut` absorbs
        it — so data blocks carrying tuple content are kit blocks, free of charge.
  `decode_pin_eq` — **PROVED, the pin supply**: a pin block with its selector LIVE
        (probe-side — the one genuinely liveness-constrained bit class, since row content is
        constant across the family while pins vary per pair) and row-side all-OFF decodes to
        exactly its singleton pin literal.
  `parity_probe_supply` — **PROVED, THE SUPPLY THEOREM**: liveness of the pin selectors + the
        row-design constants + the linear package on the decoded target content ⇒ the family
        values of the two mixes DIFFER.  The full composition of rungs 24–27.

## Honest scope

What remains is the SUPPLY COUNTING (rung 28): choosing `KB`/`PB`/`pinIdx`/`SC` per pair
under an adversarial balanced cut — pin-selector liveness from the kill-cost scout lemmas
with the expander-affine codebook, `hspan` from pins + scaffold spanning the hyperplane
`w^⊥`, the base point from transversal independence — and the tuple-family/Markov assembly
feeding `cut_row_capacity` for `j = Θ(N)`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityProbe

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityPins
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

/-! ### The probe -/

/-- The explicit probe: ON at kit tautologies, pin selectors, and target scaffold. -/
def probeOn (hfit : m * L ≤ N) (tautIdx : Fin L) (pinIdx : Fin m → Fin L)
    (SC : Finset (Fin L)) (KB PB : Finset (Fin m)) (cstar : Fin m)
    (p : Fin N) : Bool :=
  decide ((∃ c ∈ KB, p = xbit hfit c tautIdx)
    ∨ (∃ c ∈ PB, p = xbit hfit c (pinIdx c))
    ∨ (∃ i ∈ SC, p = xbit hfit cstar i))

theorem probeOn_read_kit (hfit : m * L ≤ N) (tautIdx : Fin L)
    (pinIdx : Fin m → Fin L) (SC : Finset (Fin L)) (KB PB : Finset (Fin m))
    (cstar : Fin m) {c : Fin m} (hc : c ∈ KB) :
    probeOn hfit tautIdx pinIdx SC KB PB cstar (xbit hfit c tautIdx) = true := by
  unfold probeOn
  exact decide_eq_true (Or.inl ⟨c, hc, rfl⟩)

theorem probeOn_read_pin (hfit : m * L ≤ N) (tautIdx : Fin L)
    (pinIdx : Fin m → Fin L) (SC : Finset (Fin L)) (KB PB : Finset (Fin m))
    (cstar : Fin m) {c : Fin m} (hc : c ∈ PB) :
    probeOn hfit tautIdx pinIdx SC KB PB cstar (xbit hfit c (pinIdx c)) = true := by
  unfold probeOn
  exact decide_eq_true (Or.inr (Or.inl ⟨c, hc, rfl⟩))

theorem probeOn_read_pinblock_off (hfit : m * L ≤ N) (tautIdx : Fin L)
    (pinIdx : Fin m → Fin L) (SC : Finset (Fin L)) (KB PB : Finset (Fin m))
    (cstar : Fin m) {c : Fin m} {i : Fin L}
    (hKP : c ∉ KB) (hne : i ≠ pinIdx c) (hcs : c ≠ cstar) :
    probeOn hfit tautIdx pinIdx SC KB PB cstar (xbit hfit c i) = false := by
  unfold probeOn
  apply decide_eq_false
  rintro (⟨c', hc', heq⟩ | ⟨c', hc', heq⟩ | ⟨i', hi', heq⟩)
  · obtain ⟨hcc, -⟩ := xbit_inj hfit heq
    apply hKP
    rw [hcc]
    exact hc'
  · obtain ⟨hcc, hii⟩ := xbit_inj hfit heq
    apply hne
    rw [hcc]
    exact hii
  · obtain ⟨hcc, -⟩ := xbit_inj hfit heq
    exact hcs hcc

theorem probeOn_read_target_off (hfit : m * L ≤ N) (tautIdx : Fin L)
    (pinIdx : Fin m → Fin L) (SC : Finset (Fin L)) (KB PB : Finset (Fin m))
    (cstar : Fin m) {i : Fin L}
    (hi : i ∉ SC) (hKnc : cstar ∉ KB) (hPnc : cstar ∉ PB) :
    probeOn hfit tautIdx pinIdx SC KB PB cstar (xbit hfit cstar i) = false := by
  unfold probeOn
  apply decide_eq_false
  rintro (⟨c', hc', heq⟩ | ⟨c', hc', heq⟩ | ⟨i', hi', heq⟩)
  · obtain ⟨hcc, -⟩ := xbit_inj hfit heq
    apply hKnc
    rw [hcc]
    exact hc'
  · obtain ⟨hcc, -⟩ := xbit_inj hfit heq
    apply hPnc
    rw [hcc]
    exact hc'
  · obtain ⟨-, hii⟩ := xbit_inj hfit heq
    apply hi
    rw [hii]
    exact hi'

/-! ### The decode discharges -/

/-- **The kit no-lose (proved)**: the kit block's tautology lands in the decode from either
side of the cut. -/
theorem decode_kit_mem (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m)
    (S : Finset (Fin N)) (y : Fin N → Bool) {c : Fin m} (hc : c ∈ KB)
    (hcodeTaut : code tautIdx = tautLit v)
    (hyKit : y (xbit hfit c tautIdx) = true) :
    tautLit v ∈ decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c := by
  unfold NFrameParityLayout.decodeBlock
  rw [← hcodeTaut]
  apply Finset.mem_image_of_mem
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hmem : xbit hfit c tautIdx ∈ Sᶜ
  · rw [mix_read_probe _ _ hmem]
    exact probeOn_read_kit hfit tautIdx pinIdx SC KB PB cstar hc
  · rw [mix_read_row _ _ hmem]
    exact hyKit

/-- **The pin supply (proved)**: a pin block with its selector live and row-side all-OFF
decodes to exactly its singleton pin literal. -/
theorem decode_pin_eq (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m)
    (S : Finset (Fin N)) (y : Fin N → Bool) {c : Fin m} (hc : c ∈ PB)
    (hKP : c ∉ KB) (hcs : c ≠ cstar)
    (hlive : xbit hfit c (pinIdx c) ∈ Sᶜ)
    (hyPin : ∀ i : Fin L, y (xbit hfit c i) = false) :
    decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c
      = {code (pinIdx c)} := by
  unfold NFrameParityLayout.decodeBlock
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

/-! ### The supply theorem -/

set_option maxHeartbeats 1600000 in
/-- **THE SUPPLY THEOREM (proved)**: pin-selector liveness + row-design constants + the
linear package on the decoded target content ⇒ the two mixes get DIFFERENT family values.
The full composition of rungs 24–27; the remaining work is choosing the block sets and
discharging the linear package under an adversarial cut (kill-cost + transversal). -/
theorem parity_probe_supply (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m) (istar : Fin L)
    (S : Finset (Fin N)) (y y' : Fin N → Bool)
    (w a₀ l : Fin v → ZMod 2) (b : ZMod 2)
    -- codebook data
    (hcode : code istar = (l, b))
    (hcodeTaut : code tautIdx = tautLit v)
    (hlw : dotp l w = 1)
    -- block-set structure
    (hcover : ∀ c, c ≠ cstar → c ∈ KB ∨ c ∈ PB)
    (hKP : ∀ c ∈ PB, c ∉ KB)
    (hKnc : cstar ∉ KB)
    (hPnc : cstar ∉ PB)
    -- LIVENESS: the per-pair pin selectors are probe-side
    (hlive : ∀ c ∈ PB, xbit hfit c (pinIdx c) ∈ Sᶜ)
    -- row design: kit constants ON, pin blocks all-OFF
    (hyKit : ∀ c ∈ KB, y (xbit hfit c tautIdx) = true)
    (hyPin : ∀ c ∈ PB, ∀ i : Fin L, y (xbit hfit c i) = false)
    -- pair geometry (as rung 25)
    (hpos : xbit hfit cstar istar ∉ Sᶜ)
    (hy : y (xbit hfit cstar istar) = false)
    (hy' : y' (xbit hfit cstar istar) = true)
    (hagree : ∀ p : Fin N, p ≠ xbit hfit cstar istar → y p = y' p)
    -- the linear package on the decoded target content
    (hsolP : ∀ c ∈ PB, litHolds a₀ (code (pinIdx c)))
    (hsolT : ∀ ℓ ∈ decodeBlock code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) cstar,
      ¬ litHolds a₀ ℓ)
    (hkerP : ∀ c ∈ PB, dotp (code (pinIdx c)).1 w = 0)
    (hkerT : ∀ ℓ ∈ decodeBlock code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) cstar,
      dotp ℓ.1 w = 0)
    (hspan : ∀ u : Fin v → ZMod 2,
      (∀ c ∈ PB, dotp (code (pinIdx c)).1 u = 0) →
      (∀ ℓ ∈ decodeBlock code hfit
          (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) cstar,
        dotp ℓ.1 u = 0) →
      u = 0 ∨ u = w) :
    parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y)
    ≠ parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y') := by
  classical
  -- the decoded mix has the rung-26 kit/pin structure
  have hkit' : ∀ c ∈ KB, tautLit v ∈ decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c := by
    intro c hc
    exact decode_kit_mem code hfit tautIdx pinIdx SC KB PB cstar S y hc
      hcodeTaut (hyKit c hc)
  have hpin' : ∀ c ∈ PB, decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c
      = {code (pinIdx c)} := by
    intro c hc
    have hcs : c ≠ cstar := fun hcon => hPnc (hcon ▸ hc)
    exact decode_pin_eq code hfit tautIdx pinIdx SC KB PB cstar S y hc
      (hKP c hc) hcs (hlive c hc) (hyPin c hc)
  -- discharge hsol and heven (rung 26)
  obtain ⟨hsol, heven⟩ := package_discharge
    (fun c => decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c)
    cstar (fun c => code (pinIdx c)) KB PB w a₀ l
    hcover hkit' hpin' hPnc hsolP hsolT hkerP hkerT hspan hlw
  -- the detection transfer (rung 25)
  exact parity_detect_layout_ne code hfit S
    (probeOn hfit tautIdx pinIdx SC KB PB cstar) y y' cstar istar
    w a₀ l b hcode hlw hpos hy hy' hagree hsol heven

end PallLean.Paper93.DeepMath.PathB.NFrameParityProbe

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityProbe.probeOn_read_kit
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityProbe.decode_kit_mem
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityProbe.decode_pin_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityProbe.parity_probe_supply
