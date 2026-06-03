import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDecoder

/-!
# Position → literal conversion (within the active clause)

The decoder loop (`decodeLoop_recover`) needs, per step, the active *literal* `ℓ_k`; the `(2w)^s`
label can only afford to record a *position* `p_k ∈ Fin w` (an index into the active clause) plus a
bit.  Recovering `ℓ_k` from `p_k` factors into two independent pieces:

1. **position → literal, given the clause** — index `p_k` into the active clause's literal list.
   This is plain list indexing and is proved here:
   * `clauseLitAt T p := T.lits[p]?`;
   * `clauseLitAt_pivot` — at a step with active clause `T` and pivot `ℓ`, the pivot sits at position
     `T.lits.indexOf ℓ`, so `clauseLitAt T (T.lits.indexOf ℓ) = some ℓ`;
   * `clauseLitAt_pivotPosOf` — packaged with the canonical position `pivotPosOf`:
     `clauseLitAt T (pivotPosOf cs σ) = activeTermLit cs σ`.  The recorded position recovers the
     pivot **from the active clause**.

2. **identify the active clause `T_k` from the end-state** — this is the genuine Håstad
   active-clause identification, and it is **not** discharged here.  `pivotPosOf` (the position) is
   exactly the `Fin w` component of the `(2w)^s` label; what remains open is producing `T_k` (the
   clause) from `replayPath cs ρ s` alone, which `clauseLitAt`/`clauseLitAt_pivotPosOf` then turn
   into `ℓ_k`.  No monotonicity/identification lemma is assumed or faked.

So this file closes the *within-clause* half of the position→literal conversion and pins the
remaining open core down to the single function "active clause at step `k` from the end-state".
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Position → literal within a clause.**  The literal at position `p` of clause `T`. -/
def clauseLitAt (T : Clause n) (p : ℕ) : Option (Rung4Literal n) := T.lits[p]?

/-- **The pivot sits at its `indexOf` position.**  At a step with active clause `T` and pivot `ℓ`,
indexing `T`'s literal list at `T.lits.indexOf ℓ` returns the pivot. -/
theorem clauseLitAt_pivot {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    {ℓ : Rung4Literal n} (hT : activeTerm cs σ = some T) (hℓ : activeTermLit cs σ = some ℓ) :
    clauseLitAt T (T.lits.idxOf ℓ) = some ℓ := by
  have hmem : ℓ ∈ T.lits := by
    unfold activeTermLit at hℓ
    rw [hT] at hℓ
    exact (List.mem_filter.mp (List.mem_of_mem_head? hℓ)).1
  unfold clauseLitAt
  exact List.getElem?_idxOf hmem

/-- The canonical position of the pivot in its active clause (the `Fin w` component of the label). -/
def pivotPosOf (cs : List (Clause n)) (σ : Restriction n) : ℕ :=
  match activeTerm cs σ, activeTermLit cs σ with
  | some T, some ℓ => T.lits.idxOf ℓ
  | _, _ => 0

/-- **The recorded position recovers the pivot from the active clause.**  Given the active clause
`T`, indexing at the canonical position `pivotPosOf` returns the active literal.  This is the
within-clause position→literal conversion: the label's position plus the clause yields the pivot. -/
theorem clauseLitAt_pivotPosOf {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (hT : activeTerm cs σ = some T) (hsome : (activeTermLit cs σ).isSome) :
    clauseLitAt T (pivotPosOf cs σ) = activeTermLit cs σ := by
  obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp hsome
  rw [hℓ]
  have hpos : pivotPosOf cs σ = T.lits.idxOf ℓ := by
    unfold pivotPosOf; rw [hT, hℓ]
  rw [hpos]
  exact clauseLitAt_pivot hT hℓ

/-- **Per-step reduction.**  At each replay step that has an active literal, that literal is
recovered by `clauseLitAt` from the step's active clause and recorded position `pivotPosOf`.  So the
decoder loop's advice (`decodeLoop_recover`) is computable from the per-step *active clauses* and the
position label; the only missing ingredient is the active clause `T_k` itself — the Håstad
active-clause identification from the end-state, which is **not** discharged here. -/
theorem step_pivot_eq_clauseLitAt {cs : List (Clause n)} {ρ : Restriction n} {k : ℕ}
    (hsome : (activeTermLit cs (replayPath cs ρ k)).isSome) :
    ∃ T, activeTerm cs (replayPath cs ρ k) = some T ∧
      clauseLitAt T (pivotPosOf cs (replayPath cs ρ k)) = activeTermLit cs (replayPath cs ρ k) := by
  set σ := replayPath cs ρ k with hσ
  cases hT : activeTerm cs σ with
  | none =>
    exfalso
    unfold activeTermLit at hsome
    rw [hT] at hsome
    simp at hsome
  | some T =>
    exact ⟨T, rfl, clauseLitAt_pivotPosOf hT hsome⟩

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clauseLitAt_pivot
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clauseLitAt_pivotPosOf
