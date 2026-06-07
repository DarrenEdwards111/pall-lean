import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeq

/-!
# The full-path sequence (full-path encoder re-architecture, step 1) — branch only

The no-go `Dseq_first_clause_mem` showed the satisfy-position label is *incomplete*: it drops the
falsify steps, so the confound (a clause falsified at the leaf that also got satisfy steps) cannot be
reconstructed.  The fix is to record the **full canonical path** — a token per *queried variable*, both
satisfy and falsify steps — so the active-clause progression (and hence every block boundary) is
unambiguous on replay.  This is the actual Håstad/Razborov label.

This file is step 1: the full-path sequence itself.

* `deepestFullSeq cs F σ : List (ℕ × Bool)` — for **every** step along the deepest branch, the pivot
  position and a bit (`true` = satisfy step, `false` = falsify step).  Same control flow as
  `deepestSatSeq`, but it records *both* branches (where `deepestSatSeq` records only satisfy steps).
* `deepestFullSeq_satSeq` — **subsumption**: filtering the full path to its satisfy steps recovers
  exactly the positions of `deepestSatSeq`.  So the full path is a strict refinement carrying the
  satisfy data plus the dropped falsify structure.

Later steps (separate files): length = path length (the new `s`), the full-path decoder replaying the
active-clause progression from `σ_end`, and its correctness on the confound — the real switching lemma.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The full canonical path.**  Records, for every step along the deepest branch, the pivot position
and a bit (`true` = satisfy, `false` = falsify).  Identical control flow to `deepestSatSeq`, but it
conses on *both* branches rather than only the satisfy branch. -/
def deepestFullSeq (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → List (ℕ × Bool)
  | 0, _ => []
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then []
    else match SwitchingCounting.activeTerm cs σ with
      | none => []
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => []
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then (SwitchingCounting.pivotPosOf cs σ,
                  !SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ)
                 :: deepestFullSeq cs fuel (fixVar σ (litVar ℓ) false)
          else (SwitchingCounting.pivotPosOf cs σ,
                  !SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ)
                 :: deepestFullSeq cs fuel (fixVar σ (litVar ℓ) true)

/-- **Subsumption.**  The satisfy steps of the full path are exactly the positions recorded by
`deepestSatSeq`. -/
theorem deepestFullSeq_satSeq (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      (deepestFullSeq cs F σ).filterMap (fun pb => if pb.2 then some pb.1 else none)
        = (deepestSatSeq cs F σ).map Prod.snd := by
  intro F
  induction F with
  | zero => intro σ; rfl
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestFullSeq, deepestSatSeq]; simp [hany]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => rw [deepestFullSeq, deepestSatSeq]; simp [hany, hact]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => rw [deepestFullSeq, deepestSatSeq]; simp [hany, hact, hh]
        | some ℓ =>
          -- one deepest step, for either branch bit
          have step : ∀ (σ' : Fin n → Option Bool),
              (deepestFullSeq cs F σ').filterMap (fun pb => if pb.2 then some pb.1 else none)
                = (deepestSatSeq cs F σ').map Prod.snd →
              ((SwitchingCounting.pivotPosOf cs σ, !SwitchingCounting.litFalse σ' ℓ)
                  :: deepestFullSeq cs F σ').filterMap (fun pb => if pb.2 then some pb.1 else none)
                = ((if SwitchingCounting.litFalse σ' ℓ then id
                      else List.cons (T, SwitchingCounting.pivotPosOf cs σ))
                    (deepestSatSeq cs F σ')).map Prod.snd := by
            intro σ' hih
            by_cases hf : SwitchingCounting.litFalse σ' ℓ
            · rw [if_pos hf, id_eq, List.filterMap_cons]
              simp only [hf, Bool.not_true, Bool.false_eq_true, if_false]
              exact hih
            · rw [if_neg hf, List.filterMap_cons]
              simp only [hf, Bool.not_false, if_true, List.map_cons]
              rw [hih]
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                        (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · rw [deepestFullSeq, deepestSatSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_pos hd]
            exact step (fixVar σ (litVar ℓ) false) (ih (fixVar σ (litVar ℓ) false))
          · rw [deepestFullSeq, deepestSatSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_neg hd]
            exact step (fixVar σ (litVar ℓ) true) (ih (fixVar σ (litVar ℓ) true))

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestFullSeq_satSeq
