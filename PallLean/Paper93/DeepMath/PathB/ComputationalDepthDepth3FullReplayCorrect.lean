import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullReplay

/-!
# Full-path re-architecture, step 4a: correctness **given the active-clause stream** — branch only

The full path resolves the confound *provided* the decoder knows which clause is active at each step.
This file proves exactly that, cleanly isolating the remaining hard part (step 4b).

* `activeStreamPar cs F σ : List (Clause n)` — the active clause at *each* step of the deepest descent
  (per-step, with repetition across a clause's satisfy run).  Same control flow as `deepestFullSeq`.
* `fullReplaySatPar` — the per-step parallel decoder: consume one clause and one `(position, bit)`
  together; a satisfy bit records `(clause, position)`, a falsify bit records nothing.
* `fullReplaySatPar_correct` — **the result**: `fullReplaySatPar (activeStreamPar cs F σ)
  (deepestFullSeq cs F σ) = deepestSatSeq cs F σ`.  So the full path + the active-clause stream
  reconstruct the satisfy sequence *exactly*, confound included — which the old satisfy-position label
  could not do.

**Step 4b (the remaining open core).**  Recovering `activeStreamPar` from `σ_end` alone — replaying the
active-clause computation backward from the leaf — is the genuine Håstad/Razborov reconstruction.  This
file does *not* do that; it proves the architecture is sound once the stream is in hand, reducing the
whole switching lemma to that single backward-replay step.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The per-step parallel decoder: consume a clause and a `(position, bit)` together; a satisfy bit
records `(clause, position)`, a falsify bit records nothing. -/
def fullReplaySatPar : List (Clause n) → List (ℕ × Bool) → List (Clause n × ℕ)
  | C :: cs', (p, b) :: rest => (if b then [(C, p)] else []) ++ fullReplaySatPar cs' rest
  | _, _ => []

/-- The active clause at every step of the deepest descent (per-step, with repetition). -/
def activeStreamPar (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → List (Clause n)
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
          then T :: activeStreamPar cs fuel (fixVar σ (litVar ℓ) false)
          else T :: activeStreamPar cs fuel (fixVar σ (litVar ℓ) true)

/-- **Correctness given the active stream.**  The full path together with the per-step active-clause
stream reconstructs the satisfy sequence exactly. -/
theorem fullReplaySatPar_correct (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      fullReplaySatPar (activeStreamPar cs F σ) (deepestFullSeq cs F σ) = deepestSatSeq cs F σ := by
  intro F
  induction F with
  | zero => intro σ; rfl
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => simp [activeStreamPar, deepestFullSeq, deepestSatSeq, fullReplaySatPar, hany]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => simp [activeStreamPar, deepestFullSeq, deepestSatSeq, fullReplaySatPar, hany, hact]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          simp [activeStreamPar, deepestFullSeq, deepestSatSeq, fullReplaySatPar, hany, hact, hh]
        | some ℓ =>
          have step : ∀ (σ' : Fin n → Option Bool),
              fullReplaySatPar (activeStreamPar cs F σ') (deepestFullSeq cs F σ')
                = deepestSatSeq cs F σ' →
              fullReplaySatPar (T :: activeStreamPar cs F σ')
                  ((SwitchingCounting.pivotPosOf cs σ, !SwitchingCounting.litFalse σ' ℓ)
                    :: deepestFullSeq cs F σ')
                = ((if SwitchingCounting.litFalse σ' ℓ then id
                      else List.cons (T, SwitchingCounting.pivotPosOf cs σ))
                    (deepestSatSeq cs F σ')) := by
            intro σ' hih
            rw [fullReplaySatPar, hih]
            by_cases hf : SwitchingCounting.litFalse σ' ℓ = true
            · simp [hf]
            · simp only [Bool.not_eq_true] at hf; simp [hf]
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
                        (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · rw [activeStreamPar, deepestFullSeq, deepestSatSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_pos hd]
            exact step (fixVar σ (litVar ℓ) false) (ih (fixVar σ (litVar ℓ) false))
          · rw [activeStreamPar, deepestFullSeq, deepestSatSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_neg hd]
            exact step (fixVar σ (litVar ℓ) true) (ih (fixVar σ (litVar ℓ) true))

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.fullReplaySatPar_correct
