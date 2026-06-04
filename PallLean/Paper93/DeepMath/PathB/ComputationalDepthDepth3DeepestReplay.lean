import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockWellFormed

/-!
# Deepest-branch replay decoder (stage 1: definition + well-formedness)

The full general decoder, built as a staged push toward the narrow target

    replayBlocks cs (deepestEnd cs F ρ) (lab ρ) = clauseGrouping (deepestSatSeq cs F ρ)

which feeds `reconstruction_of_canonGroupDecoder` to close the general interleaved
`ReconstructionCorrect`.

**Stage plan.**
1. *Definition* (this file): the replay decoder `replayBlocks` — walk the end-state-readable clauses
   `leafClauses cs π` in `cs`-order, zipped with the label's per-clause position blocks, emitting a
   nonempty `(clause, position)` block for each clause that has satisfy positions and skipping the
   (immediately-falsified) clauses whose block is empty.
2. *One replay step* — relate `replayBlocks` on a `cons` to its tail (next).
3. *Soundness* (`replayBlocks_correct`) — the replay reproduces `clauseGrouping (deepestSatSeq …)`.
4. *Feed* `reconstruction_of_canonGroupDecoder`.

This file does stage 1: `replayBlocks` and its **well-formedness** — its output has the same shape as
the target `clauseGrouping (deepestSatSeq …)` (`clauseGrouping_ne_nil`,
`clauseGrouping_block_entry_mem_leafClauses`): nonempty blocks whose clauses are end-state-readable.

* `replayBlocks` — the decoder.
* `replayBlocks_ne_nil` — every emitted block is nonempty.
* `replayBlocks_block_entry_mem_leafClauses` — every block entry's clause is in `leafClauses`.

Stages 2–4 (soundness against `deepestSatSeq` and the `(2w)^s` packaging) are the remaining push, not
faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The replay decoder.**  Walk the end-state-readable clauses `leafClauses cs π` (in `cs`-order)
zipped with the label's per-clause position blocks; emit a nonempty `(clause, position)` block for each
clause with positions, skipping clauses whose block is empty (immediately falsified). -/
def replayBlocks (cs : List (Clause n)) (π : Fin n → Option Bool) (label : List (List ℕ)) :
    List (List (Clause n × ℕ)) :=
  (List.zip (leafClauses cs π) label).filterMap
    (fun cp => if cp.2 = [] then none else some (cp.2.map (fun p => (cp.1, p))))

/-- **Every emitted block is nonempty** — matching `clauseGrouping_ne_nil`. -/
theorem replayBlocks_ne_nil (cs : List (Clause n)) (π : Fin n → Option Bool) (label : List (List ℕ))
    {blk : List (Clause n × ℕ)} (h : blk ∈ replayBlocks cs π label) : blk ≠ [] := by
  rw [replayBlocks, List.mem_filterMap] at h
  obtain ⟨⟨C, ps⟩, _, hf⟩ := h
  by_cases hps : ps = []
  · simp only [hps, if_pos] at hf; exact absurd hf (by simp)
  · simp only [hps, if_neg, if_false] at hf
    simp only [Option.some.injEq] at hf
    rw [← hf]
    intro hcon
    exact hps (List.map_eq_nil_iff.mp hcon)

/-- **Every block entry's clause is end-state-readable** — matching
`clauseGrouping_block_entry_mem_leafClauses`. -/
theorem replayBlocks_block_entry_mem_leafClauses (cs : List (Clause n)) (π : Fin n → Option Bool)
    (label : List (List ℕ)) {blk : List (Clause n × ℕ)} {C : Clause n} {p : ℕ}
    (hblk : blk ∈ replayBlocks cs π label) (hentry : (C, p) ∈ blk) :
    C ∈ leafClauses cs π := by
  rw [replayBlocks, List.mem_filterMap] at hblk
  obtain ⟨⟨C', ps⟩, hcp, hf⟩ := hblk
  by_cases hps : ps = []
  · simp only [hps, if_pos] at hf; exact absurd hf (by simp)
  · simp only [hps, if_neg, if_false] at hf
    simp only [Option.some.injEq] at hf
    rw [← hf, List.mem_map] at hentry
    obtain ⟨q, _, hq⟩ := hentry
    have hCC' : C = C' := (congrArg Prod.fst hq).symm
    rw [hCC']
    exact (List.of_mem_zip hcp).1

/-! ## Stage 2: one replay step

`replayAux` is `replayBlocks` on an explicit clause list (so it can be recursed on).  Its `cons`
lemmas are the one-step behavior the soundness induction (stage 3) walks on: an empty position-block
skips its clause; a nonempty one emits the clause's `(clause, position)` block and recurses. -/

/-- `replayBlocks` on an explicit clause list (the recursion target). -/
def replayAux (clauses : List (Clause n)) (label : List (List ℕ)) :
    List (List (Clause n × ℕ)) :=
  (List.zip clauses label).filterMap
    (fun cp => if cp.2 = [] then none else some (cp.2.map (fun p => (cp.1, p))))

/-- `replayBlocks` is `replayAux` on the end-state clause enumeration. -/
theorem replayBlocks_eq_replayAux (cs : List (Clause n)) (π : Fin n → Option Bool)
    (label : List (List ℕ)) : replayBlocks cs π label = replayAux (leafClauses cs π) label := rfl

@[simp] theorem replayAux_nil_left (label : List (List ℕ)) :
    replayAux ([] : List (Clause n)) label = [] := rfl

@[simp] theorem replayAux_nil_right (clauses : List (Clause n)) :
    replayAux clauses [] = [] := by
  rw [replayAux, List.zip_nil_right]; rfl

/-- **Skip step.**  An empty position-block drops its clause. -/
theorem replayAux_cons_empty (C : Clause n) (cs' : List (Clause n)) (label' : List (List ℕ)) :
    replayAux (C :: cs') ([] :: label') = replayAux cs' label' := by
  rw [replayAux, List.zip_cons_cons, List.filterMap_cons_none (by simp), ← replayAux]

/-- **Emit step.**  A nonempty position-block emits the clause's `(clause, position)` block and
recurses. -/
theorem replayAux_cons_nonempty (C : Clause n) {b : List ℕ} (hb : b ≠ [])
    (cs' : List (Clause n)) (label' : List (List ℕ)) :
    replayAux (C :: cs') (b :: label') = b.map (fun p => (C, p)) :: replayAux cs' label' := by
  rw [replayAux, List.zip_cons_cons,
    List.filterMap_cons_some (b := b.map (fun p => (C, p))) (by simp [hb]), ← replayAux]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.replayBlocks_ne_nil
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.replayBlocks_block_entry_mem_leafClauses
