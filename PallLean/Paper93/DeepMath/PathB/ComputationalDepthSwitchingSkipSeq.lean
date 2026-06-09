import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestFullSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSkipLabel

/-!
# Tight switching, skip-encoded decoder step 2: the skip-aware encoder (branch `razborov-recoverRho-wip`)

The encoder half of the `m`-free skip-augmented decoder (label space: skip-decoder step 1).  The full-path
encoder `deepestFullSeq cs F σ : List (ℕ × Bool)` records, per canonical step, the pivot position and a
satisfy/falsify bit.  The witnessed encoder `deepestWitSeq` records `(pos, active-clause-index)`, paying the
`Fin m` index that poisons the rate.  Here we record `(pos, satisfy/falsify-bit, advance-bit)` — the **advance
bit** replacing the clause index:

```
  deepestSkipSeq cs F σ : List (ℕ × Bool × Bool),
```

where the third component is `true` exactly when the just-processed active clause `T` is no longer *active* under the new
state — i.e. `T` is now falsified, or out of free literals (the negation of `activeTerm`'s predicate
`!termFalsified ∧ hasFree`).  That is the `O(1)` signal the decoder uses to know
*when* to scan to the next live clause (located by canonical order), in place of the recorded `Fin m` index.

This brick is the encoder itself plus its **subsumption** of the full path: erasing the advance bit recovers
`deepestFullSeq` exactly.  So `deepestSkipSeq` is a strict refinement of `deepestFullSeq` — it carries every
position and satisfy/falsify bit (hence everything the `(2w)^s` `PathLabel` carries) *plus* the advance bit,
and has the same length (the canonical depth `s`).  The decoder that replays the active-clause progression
from this label — dropping `hnf`/`hleaf`/`hpos` — is the next brick.

* `deepestSkipSeq` — the skip-aware full-path encoder (pivot, satisfy/falsify bit, advance bit).
* `deepestSkipSeq_map_full` — **subsumption**: erasing the advance bit gives `deepestFullSeq`.
* `deepestSkipSeq_length` — its length equals the full-path length (the canonical depth `s`).

## Honest scope

This is the encoder and its refinement of the full path — *not* the recovery.  Whether the advance bit
suffices to recover the active-clause progression without `hnf`/`hleaf`/`hpos` (the empty-skip wall) is the
content of the following decoder bricks; this file only fixes what the encoder writes down.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The skip-aware full-path encoder.**  Identical control flow to `deepestFullSeq`, but each step records a
third component, the **advance bit**: `true` when the just-processed active clause `T` is no longer active under the
taken-branch state — falsified, or with no free literals left (the negation of `activeTerm`'s
predicate `!termFalsified ∧ hasFree`) — the `O(1)` signal that replaces the
`Fin m` active-clause index of `deepestWitSeq`. -/
def deepestSkipSeq (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → List (ℕ × Bool × Bool)
  | 0, _ => []
  | fuel + 1, σ =>
    if anyTermSat cs σ then []
    else match activeTerm cs σ with
      | none => []
      | some T => match (freeLits σ T).head? with
        | none => []
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then (pivotPosOf cs σ,
                  !litFalse (fixVar σ (litVar ℓ) false) ℓ,
                  termFalsified (fixVar σ (litVar ℓ) false) T ||
                    decide ((freeLits (fixVar σ (litVar ℓ) false) T).length = 0))
                 :: deepestSkipSeq cs fuel (fixVar σ (litVar ℓ) false)
          else (pivotPosOf cs σ,
                  !litFalse (fixVar σ (litVar ℓ) true) ℓ,
                  termFalsified (fixVar σ (litVar ℓ) true) T ||
                    decide ((freeLits (fixVar σ (litVar ℓ) true) T).length = 0))
                 :: deepestSkipSeq cs fuel (fixVar σ (litVar ℓ) true)

/-- **Subsumption of the full path.**  Erasing the advance bit from the skip-aware encoder recovers the
full-path encoder `deepestFullSeq` exactly — so `deepestSkipSeq` carries every pivot position and
satisfy/falsify bit (hence all the `(2w)^s` path data) plus the advance bit. -/
theorem deepestSkipSeq_map_full (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool),
      (deepestSkipSeq cs fuel σ).map (fun t => (t.1, t.2.1)) = deepestFullSeq cs fuel σ := by
  intro fuel
  induction fuel with
  | zero => intro σ; rfl
  | succ fuel ih =>
    intro σ
    cases hany : anyTermSat cs σ with
    | true => rw [deepestSkipSeq, deepestFullSeq]; simp [hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => rw [deepestSkipSeq, deepestFullSeq]; simp [hany, hact]
      | some T =>
        cases hh : (freeLits σ T).head? with
        | none => rw [deepestSkipSeq, deepestFullSeq]; simp [hany, hact, hh]
        | some ℓ =>
          by_cases hd : (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
                        (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          · rw [deepestSkipSeq, deepestFullSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_pos hd, List.map_cons]
            rw [ih]
          · rw [deepestSkipSeq, deepestFullSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_neg hd, List.map_cons]
            rw [ih]

/-- The skip-aware encoder has the same length as the full path (the canonical depth `s`). -/
theorem deepestSkipSeq_length (cs : List (Clause n)) (fuel : ℕ) (σ : Fin n → Option Bool) :
    (deepestSkipSeq cs fuel σ).length = (deepestFullSeq cs fuel σ).length := by
  rw [← deepestSkipSeq_map_full cs fuel σ, List.length_map]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSkipSeq_map_full
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSkipSeq_length
