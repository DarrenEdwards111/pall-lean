import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestFullSeq

/-!
# Full-path re-architecture, steps 2–3: length + the forward decoder — branch only

Building on `deepestFullSeq` (the full canonical path, recording both satisfy and falsify steps):

* **Step 2 — length.**  `deepestSatSeq_length_le_full`: the satisfy sequence is no longer than the full
  path (it is the satisfy-filtered sub-sequence).  The full path's length is the new `(2w)^s` exponent.
* **Step 3 — the forward decoder.**  `fullReplaySat`: walk a clause stream and the full path together;
  on a **satisfy** bit record `(clause, position)` and stay on the clause, on a **falsify** bit advance
  to the next clause (recording nothing).  Because the falsify steps are now explicit, block boundaries
  are unambiguous — the confound (a falsified-at-leaf clause that also got satisfy steps) is handled by
  construction: its satisfy run is recorded, then its falsify bit advances.  `fullReplaySat_clause_mem`
  is the structural sanity lemma.

**Step 4 (the open core).**  Correctness — `fullReplaySat (activeStream …) (deepestFullSeq cs F ρ)
= deepestSatSeq cs F ρ` — needs the *active-clause stream* (the clause active at each step).  The
falsify bits tell the decoder *when* to advance, but *which* clause is next (the descent can skip
clauses falsified/satisfied/with-no-free-literal at the running state) must be recovered from `σ_end` by
replaying the active-clause computation backward from the leaf.  That backward state-replay is the
genuine Håstad/Razborov reconstruction (a later file); it is not faked here.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-! ## Step 2 — length -/

/-- The satisfy sequence is no longer than the full path. -/
theorem deepestSatSeq_length_le_full (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool) :
    (deepestSatSeq cs F σ).length ≤ (deepestFullSeq cs F σ).length := by
  have h := deepestFullSeq_satSeq cs F σ
  have hlen := congrArg List.length h
  rw [List.length_map] at hlen
  rw [← hlen]
  exact List.length_filterMap_le _ _

/-! ## Step 3 — the forward decoder -/

/-- **The full-path forward decoder.**  Walk a clause stream and the full path; a satisfy bit records
`(clause, position)` and stays, a falsify bit advances to the next clause.  Falsify steps being explicit
makes block boundaries unambiguous (the confound is handled by construction). -/
def fullReplaySat : List (Clause n) → List (ℕ × Bool) → List (Clause n × ℕ)
  | _, [] => []
  | [], _ => []
  | C :: cs', (p, b) :: rest =>
      if b then (C, p) :: fullReplaySat (C :: cs') rest
      else fullReplaySat cs' rest

/-- Every clause emitted by `fullReplaySat` belongs to the input clause stream. -/
theorem fullReplaySat_clause_mem :
    ∀ (clauses : List (Clause n)) (path : List (ℕ × Bool)) {C : Clause n} {p : ℕ},
      (C, p) ∈ fullReplaySat clauses path → C ∈ clauses := by
  intro clauses path
  induction path generalizing clauses with
  | nil => intro C p h; cases clauses <;> simp [fullReplaySat] at h
  | cons pb rest ih =>
    intro C p h
    cases clauses with
    | nil => simp [fullReplaySat] at h
    | cons D cs' =>
      obtain ⟨q, b⟩ := pb
      rw [fullReplaySat] at h
      by_cases hb : b
      · rw [if_pos hb, List.mem_cons] at h
        rcases h with heq | htl
        · have hCD : C = D := congrArg Prod.fst heq
          rw [hCD]; exact List.mem_cons_self
        · exact ih (D :: cs') htl
      · rw [if_neg hb] at h
        exact List.mem_cons_of_mem _ (ih cs' h)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSeq_length_le_full
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.fullReplaySat_clause_mem
