import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqDecoder

/-!
# Why the rigid `Dseq` is not general — the confound, as a structural no-go (branch only)

The concrete decoder `Dseq` walks `leafClauses` and, via `takeBlock`, assigns each clause a block of the
token stream.  This file proves the **structural limitation**: `takeBlock` returns a *nonempty* block
whenever tokens remain (`takeBlock_fst_ne_nil`), so `Dseq` always gives the first walked leaf clause a
nonempty block (`Dseq_first_clause_mem`).  Hence `Dseq` **cannot skip a leaf clause** — it cannot
produce an interior (or leading) *empty* block.

Consequence (the honest boundary): for a bad set containing a **confound** — a clause falsified at the
leaf that *also* received satisfy steps — `deepestSatSeq` has clauses interleaved with empty-block
(falsified, no-satisfy) leaf clauses.  No choice of label `lab` can make the rigid `Dseq` reproduce
that, because `Dseq` never emits an empty interior block.  So `Dseq_correct_general` (with this `Dseq`)
is **not achievable**; the regimes it *does* settle are exactly no-skip (`Dseq`) and clean-skip
(`DseqSkip`), and `confound_uncovered` shows no single `σ_end`-decoder separates confound from
clean-skip with the satisfy-position label.

The genuine general decoder is the **full-path Razborov decoder**: a label with a token per *queried
variable* (satisfy *and* falsify steps, `s` = total path length, the `×2` bit recording the
satisfy/falsify branch), from which the full path — and hence the block boundaries, confound included —
is replayed unambiguously.  That is the actual Håstad switching lemma and a re-architecture of the
label/count, not a refinement of this `Dseq`.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `takeBlock` returns a nonempty block whenever there are tokens to consume. -/
theorem takeBlock_fst_ne_nil {w : ℕ} (toks : List (Fin w × Bool)) (h : toks ≠ []) :
    (takeBlock toks).1 ≠ [] := by
  cases toks with
  | nil => exact absurd rfl h
  | cons t ts =>
    rw [takeBlock]
    by_cases hb : t.2
    · simp [hb]
    · simp only [hb, Bool.false_eq_true, if_false]
      cases takeBlock ts with
      | mk b r => simp

/-- **`Dseq` cannot skip the first walked clause.**  Whenever the label is nonempty, the head leaf
clause `C` appears in the decoder's output — so `Dseq` can never give it an empty block. -/
theorem replayBlocksFlat_first_clause_mem {w : ℕ} (C : Clause n) (cs' : List (Clause n))
    (toks : List (Fin w × Bool)) (h : toks ≠ []) :
    ∃ p, (C, p) ∈ replayBlocksFlat (C :: cs') toks := by
  have hne : (takeBlock toks).1 ≠ [] := takeBlock_fst_ne_nil toks h
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
  refine ⟨(t.1 : ℕ), ?_⟩
  have hsplit : replayBlocksFlat (C :: cs') toks
      = (takeBlock toks).1.map (fun t => (C, (t.1 : ℕ)))
          ++ replayBlocksFlat cs' (takeBlock toks).2 := by rw [replayBlocksFlat]
  rw [hsplit, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- **The structural no-go for `Dseq`.**  Whenever the label is nonempty, the head leaf clause of the
walk is present in `Dseq`'s output — `Dseq` cannot skip it.  Therefore a `deepestSatSeq` whose head
leaf clause carries an *empty* block (a leading skip — present in the confound / clean-skip structure)
is unreachable by `Dseq` for any label, witnessing that the rigid `Dseq` is not a general decoder. -/
theorem Dseq_first_clause_mem {w s : ℕ} (cs : List (Clause n)) (σ_end : Fin n → Option Bool)
    (lbl : SwitchingCounting.PathLabel w s) (C : Clause n) (cs' : List (Clause n))
    (hlc : leafClauses cs σ_end = C :: cs') (h : List.ofFn lbl ≠ []) :
    ∃ p, (C, p) ∈ Dseq cs σ_end lbl := by
  rw [Dseq, hlc]
  exact replayBlocksFlat_first_clause_mem C cs' (List.ofFn lbl) h

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Dseq_first_clause_mem
