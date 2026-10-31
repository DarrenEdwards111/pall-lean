import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FreeLitPos
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction

/-!
# Tight switching, step 28: the witnessed reconstruction correctness — `hnf`-free (branch `razborov-recoverRho-wip`)

The mathematical heart of dropping `hnf`.  The deepest branch selects, at each step, the variable
`litVar ℓ` of the active term's first free literal.  We record per step the witness `(freeLitPos σ T,
activeTermIdx cs σ)` — the literal's position in the term and the term's index in `cs` — and decode it by
`litVar (cs[clauseIdx].lits[position])` (Option-form, no proofs).  Bricks 66/67 give the recovery
`cs[activeTermIdx] = T` and `T.lits[freeLitPos] = ℓ`, so the decode returns exactly `litVar ℓ` — **with no
clause scanning and no `hnf`**.

Inducting on the fuel along `deepestSel`'s own recursion (the witness encode mirrors it step for step,
sharing the `anyTermSat` / `activeTerm` / `head?` / depth-comparison branches) gives

```
  witDecode cs (deepestWitSeq cs F ρ) = deepestSel cs F ρ,
```

*unconditionally* — the empty-skip wall is gone because the witness names the live active term directly
instead of disambiguating dead clauses from the leaf.

* `witDecode`, `deepestWitSeq` — the witness decode and the deepest-branch encode.
* `witDecode_deepestWitSeq` — the `hnf`-free reconstruction correctness.

## Honest scope

This is the `hnf`-free correctness in `ℕ`-indexed form (positions/clause-indices as `ℕ`).  Packaging it into
the `Fintype` `WitLabel w s m` (bounding positions by `w`, clause indices by `m`, length by `s`) and feeding
`deepest_count_of_witness` (step 25) is the remaining mechanical conversion — the math content (this decode
recovers `deepestSel` without `hnf`) is done here.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The witness decoder: read off the selected variable from each `(position, clause-index)` pair via
`litVar (cs[clauseIdx].lits[position])` — no scan, no `hnf`. -/
def witDecode (cs : List (Clause n)) : List (ℕ × ℕ) → Finset (Fin n)
  | [] => ∅
  | pc :: rest =>
    match (cs[pc.2]?).bind (fun T => T.lits[pc.1]?) with
    | none => witDecode cs rest
    | some ℓ => insert (litVar ℓ) (witDecode cs rest)

/-- The deepest-branch witness encode: per step, the active term's first-free-literal position and the
term's index in `cs`.  Mirrors `deepestSel`'s recursion exactly. -/
def deepestWitSeq (cs : List (Clause n)) : ℕ → Restriction n → List (ℕ × ℕ)
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
          then (freeLitPos σ T, activeTermIdx cs σ)
                 :: deepestWitSeq cs fuel (fixVar σ (litVar ℓ) false)
          else (freeLitPos σ T, activeTermIdx cs σ)
                 :: deepestWitSeq cs fuel (fixVar σ (litVar ℓ) true)

/-- **The witnessed reconstruction is correct — `hnf`-free.**  The witness decode of the deepest-branch
encode recovers the deepest selected set, with dead clauses present and no `hnf` assumption. -/
theorem witDecode_deepestWitSeq (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Restriction n),
      witDecode cs (deepestWitSeq cs fuel σ) = deepestSel cs fuel σ := by
  intro fuel
  induction fuel with
  | zero => intro σ; rfl
  | succ fuel ih =>
    intro σ
    by_cases hsat : anyTermSat cs σ = true
    · simp only [deepestWitSeq, deepestSel, if_pos hsat, witDecode]
    · cases hT : activeTerm cs σ with
      | none => simp only [deepestWitSeq, deepestSel, if_neg hsat, hT, witDecode]
      | some T =>
        cases hh : (freeLits σ T).head? with
        | none => simp only [deepestWitSeq, deepestSel, if_neg hsat, hT, hh, witDecode]
        | some ℓ =>
          have hc : cs[activeTermIdx cs σ]? = some T := by
            rw [List.getElem?_eq_getElem (activeTermIdx_lt hT), getElem_activeTermIdx hT]
          have hp : T.lits[freeLitPos σ T]? = some ℓ := by
            rw [List.getElem?_eq_getElem (freeLitPos_lt hh), getElem_freeLitPos hh]
          by_cases hcmp : (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          · simp only [deepestWitSeq, deepestSel, if_neg hsat, hT, hh, if_pos hcmp, witDecode,
              hc, Option.bind_some, hp]
            rw [ih (fixVar σ (litVar ℓ) false)]
          · simp only [deepestWitSeq, deepestSel, if_neg hsat, hT, hh, if_neg hcmp, witDecode,
              hc, Option.bind_some, hp]
            rw [ih (fixVar σ (litVar ℓ) true)]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.witDecode_deepestWitSeq
