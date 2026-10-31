import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3TandemCanon

/-!
# Entry 480 — generic scan loop: the iterated tandem comparison `tandemLoop` (proved)

Closing the comparison loop with a back-edge (`lcrFound := s`): one tandem iteration (`tandemStepCanon_run`, entry 479)
returns to the loop head `s` with both cursors advanced one, so iterating `d` times walks both cursors from step `0` to step
`d` on the canonical comparison tape (`cursTape`, entry 478).  Correctness is by induction on the step count `d`, the machine
fixed — the distance-agnostic two-cursor walk that compares two unary fields.

`tandemLoop … := tandemStep3 … (lcrFound := s) …`.

## What is proved (clean axioms, no `sorry`)

* **`tandemLoop …`** — the back-edged tandem comparison loop.
* **`tandemLoop_run`** (PROVED) — for `d` iterations, with the base tape's two fields all `I` over `cp … cp+d` and `cp+g …
  cp+g+d`, the inter-field region marker-free, and in bounds: `∃ N, reachIn N (s, cp, cursTape tp cp g 0) (s, cp+d, cursTape
  tp cp g d)` — both cursors walk `d` steps, by induction on `d`.

## Honest scope

This is the **iterated tandem walk** (both fields continuing for `d` steps).  It does **not** yet build the four-way
end-branch (match vs mismatch at the field ends), the symbol compare, the match-or-advance branch, the generic apply, nor a
fixed `U` / `EmitsEncodedStepEx3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemLoop

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemStep (tandemStep3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CursTape (cursTape)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemCanon (tandemStepCanon_run)

/-- **The back-edged tandem comparison loop.**  One iteration returns to the loop head `s`. -/
def tandemLoop (s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid lcrCont : ℕ) : TMachine3 :=
  tandemStep3 s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid s lcrCont

/-- **The iterated tandem walk advances both cursors `d` steps (PROVED).** -/
theorem tandemLoop_run (s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid lcrCont : ℕ)
    (tp : List Sym3) (cp g : ℕ) (hg : 2 ≤ g) :
    ∀ (d : ℕ), (∀ k, k ≤ d → tp.getD (cp + k) Sym3.O = Sym3.I) →
      (∀ k, k ≤ d → tp.getD (cp + g + k) Sym3.O = Sym3.I) →
      (∀ j, cp < j → j < cp + g + d → tp.getD j Sym3.O ≠ Sym3.M) → cp + g + d < tp.length →
      ∃ N, reachIn (toNTM3 (tandemLoop s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid lcrCont)) N
        (s, cp, cursTape tp cp g 0) (s, cp + d, cursTape tp cp g d) := by
  intro d
  induction d with
  | zero => intro _ _ _ _; exact ⟨0, rfl⟩
  | succ d ih =>
      intro hCF hRF hGap hbnd
      obtain ⟨N0, h0⟩ := ih (fun k hk => hCF k (by omega)) (fun k hk => hRF k (by omega))
        (fun j hj1 hj2 => hGap j hj1 (by omega)) (by omega)
      obtain ⟨Ns, hs⟩ := tandemStepCanon_run s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid s lcrCont
        tp cp g d hg (hCF d (by omega)) (hCF (d + 1) (by omega)) (hRF d (by omega)) (hRF (d + 1) (by omega))
        (fun j hj1 hj2 => hGap j (by omega) (by omega)) (by omega)
      exact ⟨N0 + Ns, (reachIn_add (toNTM3 (tandemLoop s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid
        lcrCont)) N0 Ns _ _).mpr ⟨(s, cp + d, cursTape tp cp g d), h0, hs⟩⟩

/-!
**The iterated tandem walk, proved.**  `tandemLoop` walks both cursors `d` steps, by induction on `d` — the distance-agnostic
unary comparison loop.  Next: the four-way end-branch (when a field ends, `markAdvance3`'s end-case distinguishes match from
mismatch), then the symbol compare — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemLoop

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemLoop.tandemLoop_run
