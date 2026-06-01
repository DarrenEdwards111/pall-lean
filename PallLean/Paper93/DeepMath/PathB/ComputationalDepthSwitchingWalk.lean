import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingConfirm

/-!
# The σ*-guided clause walk (scaffolding + selector correctness)

**STATUS: REAL.  THE WALK FOLD — DEFINITIONS AND PER-STEP SELECTOR.**

The `(2w)^s` decoder walks `cs` consuming the label as consecutive index-blocks (one per
processed clause, delimited by the control bits).  For each block it finds the first
clause in the remaining `cs`-suffix that *confirms* (flips under `σ*` when its block
variables are freed), collects that clause's block variables, and advances.

* `blockVars C block`: the variables named by a block of clause-relative indices in `C`;
* `walkVars`: the fold — find the first confirming clause per block, collect, advance;
* `found_confirms`: the clause the walk lands on genuinely confirms (it is the head of a
  `dropWhile`, so it fails the "not-confirm" predicate).

Correctness — `walkVars σ* cs (encoder blocks) = path-variable set` — is the next layer
(matching each `find?` to the encoder's processed-clause sequence).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The variables named by a block of clause-relative indices in `C`. -/
def blockVars (C : Clause n) (block : List ℕ) : Finset (Fin n) :=
  (block.filterMap (fun i => (C.lits[i]?).map litVar)).toFinset

theorem mem_blockVars {C : Clause n} {block : List ℕ} {v : Fin n} :
    v ∈ blockVars C block ↔ ∃ i ∈ block, (C.lits[i]?).map litVar = some v := by
  unfold blockVars
  rw [List.mem_toFinset, List.mem_filterMap]

/-- The walk: for each index-block, find the first confirming clause in the `cs`-suffix,
collect its block variables, advance past it. -/
def walkVars (σstar : Restriction n) : List (Clause n) → List (List ℕ) → Finset (Fin n)
  | _, [] => ∅
  | suffix, block :: rest =>
    match suffix.dropWhile (fun C => !confirm σstar (blockVars C block) C) with
    | [] => ∅
    | C :: tail => blockVars C block ∪ walkVars σstar tail rest

theorem walkVars_nil (σstar : Restriction n) (suffix : List (Clause n)) :
    walkVars σstar suffix [] = ∅ := rfl

theorem walkVars_cons (σstar : Restriction n) (suffix : List (Clause n))
    (block : List ℕ) (rest : List (List ℕ)) :
    walkVars σstar suffix (block :: rest) =
      match suffix.dropWhile (fun C => !confirm σstar (blockVars C block) C) with
      | [] => ∅
      | C :: tail => blockVars C block ∪ walkVars σstar tail rest := rfl

/-- The head of a `dropWhile` fails the dropped predicate. -/
theorem dropWhile_head_not {α : Type*} {p : α → Bool} {l : List α} {a : α} {t : List α}
    (h : l.dropWhile p = a :: t) : p a = false := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    have hunfold : (b :: l).dropWhile p
        = match p b with | true => l.dropWhile p | false => b :: l := rfl
    rw [hunfold] at h
    cases hb : p b with
    | true => simp only [hb] at h; exact ih h
    | false =>
      simp only [hb] at h
      rw [List.cons.injEq] at h
      rw [← h.1]; exact hb

/-- **Selector correctness.**  The clause the walk lands on for a block genuinely confirms
(flips under `σ*` when its block variables are freed). -/
theorem found_confirms {σstar : Restriction n} {suffix : List (Clause n)} {block : List ℕ}
    {C : Clause n} {tail : List (Clause n)}
    (h : suffix.dropWhile (fun C => !confirm σstar (blockVars C block) C) = C :: tail) :
    confirm σstar (blockVars C block) C = true := by
  have hb := dropWhile_head_not h
  simpa using hb

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.found_confirms
