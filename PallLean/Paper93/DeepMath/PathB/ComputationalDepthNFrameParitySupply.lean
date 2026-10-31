import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityTwoPoint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityProbe
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityDrag

/-!
# N-Frame: the parity supply — the per-pair discharge

Rung 28c of the arc (… → parity drag → **parity supply**).  The `hdist` interface of the drag
is discharged: for any two tuple rows, the constructed probe (rung 27's `probeOn`) plus a
PER-TARGET-POSITION supply package makes the two mixes' family values differ, via the
two-point comparison.  Key structural facts from the pressure-test:

- the two-point comparison is MULTI-DIFFERENCE NATIVE, so no pair geometry is needed — only
  the decoded contents matter;
- the supply package is per-TARGET-POSITION, not per-pair: `a₀` falsifies ALL of the target
  block's priced literals at once, and `w` kills all their functionals except the target's —
  the same `(w, a₀, pins, scaffold)` serves every pair whose chosen difference is that
  position.

  `decode_cstar_eq` — **PROVED, the target decode**: the decoded target content of a tuple
        row's mix is exactly `(effective scaffold) ∪ (the row's selected positions)` — the
        effective scaffold being probe-side `SC`-selectors plus row-side `SCrow`-selectors.
  `parity_pair_dist` — **PROVED, THE PAIR DISCHARGE**: structure + liveness + row design +
        the per-target linear supply ⇒ the two mixes' family values DIFFER.

## Honest scope

Remaining for the full `(2+c)N` chain: (i) the SUPPLY COUNTING — pins spanning `w^⊥` with the
shared scaffold from kill-cost liveness on the expander-affine codebook (paper-proved, scout
lemmas frozen; Lean instantiation of an explicit expander is the one large deferred
formalization), the per-block transversal placement, and the block-NEUTRALIZATION menus
(every non-pin block must be kit-able or harmlessly pinnable under adversarial position
control — named here as a concrete combinatorial sub-problem of the counting round);
(ii) `|V| = Θ(T)` via Markov selection (rung 23's `markov_select`, reusable); (iii) the
band/`cbudget` conversion — the parity family's root-shape and essential-variable lemmas
mirroring the sat3 ones, then `2·live + Θ(N)`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParitySupply

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityPins
open PallLean.Paper93.DeepMath.PathB.NFrameParityProbe
open PallLean.Paper93.DeepMath.PathB.NFrameParityTwoPoint
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

set_option maxHeartbeats 1600000 in
/-- **The target decode (proved)**: the decoded target content of a tuple row's mix is the
effective scaffold plus the row's selected positions. -/
theorem decode_cstar_eq (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m)
    (S : Finset (Fin N)) (y : Fin N → Bool)
    (E : Finset (Fin m × Fin L)) (SCrow : Finset (Fin L))
    (hKnc : cstar ∉ KB) (hPnc : cstar ∉ PB)
    (hEside : ∀ i : Fin L, (cstar, i) ∈ E → xbit hfit cstar i ∉ Sᶜ)
    (hSCrow : ∀ i ∈ SCrow, xbit hfit cstar i ∉ Sᶜ)
    (hyE : ∀ i : Fin L, xbit hfit cstar i ∉ Sᶜ →
      (y (xbit hfit cstar i) = true ↔ ((cstar, i) ∈ E ∨ i ∈ SCrow))) :
    decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) cstar
      = (((SC.filter (fun i => xbit hfit cstar i ∈ Sᶜ)) ∪ SCrow)
          ∪ (Finset.univ.filter (fun i : Fin L => (cstar, i) ∈ E))).image code := by
  unfold NFrameParityLayout.decodeBlock
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
        left
        left
        refine ⟨?_, hmem⟩
        rw [hii]
        exact hi'
    · rintro ((hsc | hscr) | hE)
      · unfold probeOn
        exact decide_eq_true (Or.inr (Or.inr ⟨i, hsc.1, rfl⟩))
      · exact absurd hmem (by
          intro hc
          exact (hSCrow i hscr) hc)
      · exact absurd hmem (by
          intro hc
          exact (hEside i hE) hc)
  · rw [mix_read_row _ _ hmem]
    constructor
    · intro hon
      rcases (hyE i hmem).mp hon with h | h
      · right
        exact h
      · left
        right
        exact h
    · rintro ((hsc | hscr) | hE)
      · exact absurd hsc.2 hmem
      · exact (hyE i hmem).mpr (Or.inr hscr)
      · exact (hyE i hmem).mpr (Or.inl hE)

set_option maxHeartbeats 3200000 in
/-- **THE PAIR DISCHARGE (proved)**: structure + liveness + row design + the per-target
linear supply ⇒ the two tuple rows' mixes get DIFFERENT family values.  No pair geometry is
needed — the two-point comparison is multi-difference native. -/
theorem parity_pair_dist (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m) (istar : Fin L)
    (S : Finset (Fin N)) (y y' : Fin N → Bool)
    (E E' : Finset (Fin m × Fin L)) (SCrow : Finset (Fin L))
    (w a₀ : Fin v → ZMod 2)
    -- codebook and structure
    (hcodeTaut : code tautIdx = tautLit v)
    (hcover : ∀ c, c ≠ cstar → c ∈ KB ∨ c ∈ PB)
    (hKP : ∀ c ∈ PB, c ∉ KB)
    (hKnc : cstar ∉ KB)
    (hPnc : cstar ∉ PB)
    (hlive : ∀ c ∈ PB, xbit hfit c (pinIdx c) ∈ Sᶜ)
    -- row design at non-target blocks (both rows)
    (hyKit : ∀ c ∈ KB, y (xbit hfit c tautIdx) = true)
    (hyKit' : ∀ c ∈ KB, y' (xbit hfit c tautIdx) = true)
    (hyPin : ∀ c ∈ PB, ∀ i : Fin L, y (xbit hfit c i) = false)
    (hyPin' : ∀ c ∈ PB, ∀ i : Fin L, y' (xbit hfit c i) = false)
    -- row design at the target block
    (hEside : ∀ i : Fin L, (cstar, i) ∈ E → xbit hfit cstar i ∉ Sᶜ)
    (hE'side : ∀ i : Fin L, (cstar, i) ∈ E' → xbit hfit cstar i ∉ Sᶜ)
    (hSCrow : ∀ i ∈ SCrow, xbit hfit cstar i ∉ Sᶜ)
    (hyE : ∀ i : Fin L, xbit hfit cstar i ∉ Sᶜ →
      (y (xbit hfit cstar i) = true ↔ ((cstar, i) ∈ E ∨ i ∈ SCrow)))
    (hyE' : ∀ i : Fin L, xbit hfit cstar i ∉ Sᶜ →
      (y' (xbit hfit cstar i) = true ↔ ((cstar, i) ∈ E' ∨ i ∈ SCrow)))
    -- the target
    (htarE' : (cstar, istar) ∈ E')
    (hlw : dotp (code istar).1 w = 1)
    -- the per-target linear supply
    (ha₀E : ∀ i : Fin L, (cstar, i) ∈ E → ¬ litHolds a₀ (code i))
    (ha₀E' : ∀ i : Fin L, (cstar, i) ∈ E' → ¬ litHolds a₀ (code i))
    (hwE : ∀ i : Fin L, (cstar, i) ∈ E → dotp (code i).1 w = 0)
    (hpairPin : ∀ a : Fin v → ZMod 2,
      ((∀ c ∈ PB, litHolds a (code (pinIdx c)))
        ∧ ∀ ℓ ∈ (((SC.filter (fun i => xbit hfit cstar i ∈ Sᶜ)) ∪ SCrow)).image code,
          ¬ litHolds a ℓ)
      ↔ (a = a₀ ∨ a = a₀ + w)) :
    parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y)
    ≠ parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y') := by
  classical
  -- the decode structure at non-target blocks, both rows
  have hkitY : ∀ c ∈ KB, tautLit v ∈ decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c := by
    intro c hc
    exact decode_kit_mem code hfit tautIdx pinIdx SC KB PB cstar S y hc
      hcodeTaut (hyKit c hc)
  have hkitY' : ∀ c ∈ KB, tautLit v ∈ decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y') c := by
    intro c hc
    exact decode_kit_mem code hfit tautIdx pinIdx SC KB PB cstar S y' hc
      hcodeTaut (hyKit' c hc)
  have hpinY : ∀ c ∈ PB, decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c
      = {code (pinIdx c)} := by
    intro c hc
    have hcs : c ≠ cstar := fun hcon => hPnc (hcon ▸ hc)
    exact decode_pin_eq code hfit tautIdx pinIdx SC KB PB cstar S y hc
      (hKP c hc) hcs (hlive c hc) (hyPin c hc)
  have hpinY' : ∀ c ∈ PB, decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y') c
      = {code (pinIdx c)} := by
    intro c hc
    have hcs : c ≠ cstar := fun hcon => hPnc (hcon ▸ hc)
    exact decode_pin_eq code hfit tautIdx pinIdx SC KB PB cstar S y' hc
      (hKP c hc) hcs (hlive c hc) (hyPin' c hc)
  -- the non-target collapse, both rows
  have hAY := nonTarget_iff_pins
    (fun c => decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c)
    cstar (fun c => code (pinIdx c)) KB PB hcover hkitY hpinY hPnc
  have hAY' := nonTarget_iff_pins
    (fun c => decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y') c)
    cstar (fun c => code (pinIdx c)) KB PB hcover hkitY' hpinY' hPnc
  -- the target decodes
  have hDT := decode_cstar_eq code hfit tautIdx pinIdx SC KB PB cstar S y E SCrow
    hKnc hPnc hEside hSCrow hyE
  have hDT' := decode_cstar_eq code hfit tautIdx pinIdx SC KB PB cstar S y' E' SCrow
    hKnc hPnc hE'side hSCrow hyE'
  rw [Finset.image_union] at hDT hDT'
  -- assemble the two-point comparison
  have hmain := parity_two_point
    (fun c => decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y) c)
    (fun c => decodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y') c)
    cstar
    ((((SC.filter (fun i => xbit hfit cstar i ∈ Sᶜ)) ∪ SCrow)).image code)
    ((Finset.univ.filter (fun i : Fin L => (cstar, i) ∈ E)).image code)
    ((Finset.univ.filter (fun i : Fin L => (cstar, i) ∈ E')).image code)
    w a₀ (code istar).1 (code istar).2 hlw hDT hDT'
    (by
      -- the target literal is in the primed tuple image
      have heta : ((code istar).1, (code istar).2) = code istar := rfl
      rw [heta]
      apply Finset.mem_image_of_mem
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, htarE'⟩)
    (by
      rintro ℓ hℓ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
      rw [Finset.mem_filter] at hi
      exact ha₀E i hi.2)
    (by
      rintro ℓ hℓ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
      rw [Finset.mem_filter] at hi
      exact ha₀E' i hi.2)
    (by
      rintro ℓ hℓ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
      rw [Finset.mem_filter] at hi
      exact hwE i hi.2)
    (by
      intro a
      constructor
      · intro h
        exact (hAY' a).mpr ((hAY a).mp h)
      · intro h
        exact (hAY a).mpr ((hAY' a).mp h))
    (by
      intro a
      constructor
      · rintro ⟨hnt, hsh⟩
        exact (hpairPin a).mp ⟨(hAY a).mp hnt, hsh⟩
      · intro h
        obtain ⟨hp, hsh⟩ := (hpairPin a).mpr h
        exact ⟨(hAY a).mpr hp, hsh⟩)
  exact hmain

end PallLean.Paper93.DeepMath.PathB.NFrameParitySupply

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParitySupply.decode_cstar_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParitySupply.parity_pair_dist
