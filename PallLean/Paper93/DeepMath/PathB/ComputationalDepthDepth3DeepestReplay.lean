import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockWellFormed
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFlatten
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFlatLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEncLabel

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

/-! ## Stage 3a: the decoder reconstruction round-trip

Given a `(clause, positions)` list, the decoder run on its clause-projection and position-projection
reconstructs exactly the nonempty position-blocks (empty entries — immediately-falsified clauses — are
skipped).  This is the decoder's core correctness; it reduces soundness (stage 3) to the *alignment*
of `leafClauses` with the blocks of `clauseGrouping (deepestSatSeq …)`. -/

/-- **The decoder reconstruction round-trip.**  `replayAux` on the clause/position projections of an
entry list yields the nonempty entries in block form, skipping the empty ones. -/
theorem replayAux_map_eq (entries : List (Clause n × List ℕ)) :
    replayAux (entries.map Prod.fst) (entries.map Prod.snd) =
      (entries.filter (fun cp => decide (cp.2 ≠ []))).map (fun cp => cp.2.map (fun p => (cp.1, p))) := by
  induction entries with
  | nil => simp [replayAux]
  | cons cp rest ih =>
    obtain ⟨C, ps⟩ := cp
    simp only [List.map_cons, List.filter_cons]
    by_cases hps : ps = []
    · rw [hps, replayAux_cons_empty, ih]
      simp
    · rw [replayAux_cons_nonempty C hps, ih]
      simp [hps]

/-! ## Stage 3b-i: concrete encoder, reduce to the alignment equation

The encoder labels each leaf-readable clause with its positions in `deepestSatSeq`.  Feeding it to the
decoder and applying the reconstruction round-trip reduces `replayBlocks_correct` to one equation: the
nonempty leaf-clause blocks (in `leafClauses`-order) equal `clauseGrouping (deepestSatSeq …)` — the
*alignment* (stage 3b-ii). -/

/-- The positions of clause `C` recorded in `deepestSatSeq`. -/
def deepestSatPositions (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool) (C : Clause n) :
    List ℕ :=
  (deepestSatSeq cs F ρ).filterMap (fun e => if e.1 = C then some e.2 else none)

/-- The replay label: each leaf-readable clause paired with its `deepestSatSeq` position block. -/
def replayLabel (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool) : List (List ℕ) :=
  (leafClauses cs (deepestEnd cs F ρ)).map (deepestSatPositions cs F ρ)

/-- **The decoder output, concretely.**  With the encoder `replayLabel`, the decoder produces exactly
the nonempty leaf-clause blocks in block form — reducing `replayBlocks_correct` to the alignment. -/
theorem replayBlocks_eq_filter (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool) :
    replayBlocks cs (deepestEnd cs F ρ) (replayLabel cs F ρ) =
      (((leafClauses cs (deepestEnd cs F ρ)).map
        (fun C => (C, deepestSatPositions cs F ρ C))).filter
          (fun cp => decide (cp.2 ≠ []))).map (fun cp => cp.2.map (fun p => (cp.1, p))) := by
  have hfst : ((leafClauses cs (deepestEnd cs F ρ)).map
      (fun C => (C, deepestSatPositions cs F ρ C))).map Prod.fst
      = leafClauses cs (deepestEnd cs F ρ) := by
    rw [List.map_map,
      show (Prod.fst ∘ fun C : Clause n => (C, deepestSatPositions cs F ρ C)) = id from by
        funext x; rfl, List.map_id]
  have hsnd : ((leafClauses cs (deepestEnd cs F ρ)).map
      (fun C => (C, deepestSatPositions cs F ρ C))).map Prod.snd = replayLabel cs F ρ := by
    rw [List.map_map, replayLabel,
      show (Prod.snd ∘ fun C : Clause n => (C, deepestSatPositions cs F ρ C))
        = deepestSatPositions cs F ρ from by funext C; rfl]
  rw [replayBlocks_eq_replayAux]
  have key := replayAux_map_eq
    ((leafClauses cs (deepestEnd cs F ρ)).map (fun C => (C, deepestSatPositions cs F ρ C)))
  rwa [hfst, hsnd] at key

/-! ## Stage 3b-ii: soundness via order-insensitivity

`decodeSatSeq` is a `toFinset`, so it depends only on the *set* of `(clause, position)` pairs — the
order-matching (the apparent alignment wall) is irrelevant.  It therefore suffices that the decoder's
flattened output has the same membership as `deepestSatSeq`, which holds because every
`deepestSatSeq` pair's clause is end-state-readable (`deepestSatSeq_clause_mem_leafClauses`). -/

/-- `deepestSatPositions C` lists exactly the positions paired with `C` in `deepestSatSeq`. -/
theorem mem_deepestSatPositions (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (C : Clause n) (p : ℕ) :
    p ∈ deepestSatPositions cs F ρ C ↔ (C, p) ∈ deepestSatSeq cs F ρ := by
  unfold deepestSatPositions
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨ec, ep⟩, he, heq⟩
    by_cases h : ec = C
    · rw [if_pos h] at heq; simp only [Option.some.injEq] at heq; subst h; subst heq; exact he
    · rw [if_neg h] at heq; exact absurd heq (by simp)
  · intro h; exact ⟨(C, p), h, by simp⟩

/-- `decodeSatSeq` depends only on membership (it is a `toFinset`). -/
theorem decodeSatSeq_eq_of_mem {l l' : List (Clause n × ℕ)} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    decodeSatSeq l = decodeSatSeq l' := by
  unfold decodeSatSeq
  ext y
  simp only [List.mem_toFinset, List.mem_filterMap]
  exact ⟨fun ⟨b, hb, hg⟩ => ⟨b, (h b).mp hb, hg⟩, fun ⟨b, hb, hg⟩ => ⟨b, (h b).mpr hb, hg⟩⟩

/-- **The decoder's flattened output has the same pairs as `deepestSatSeq`.**  No ordering needed:
every `deepestSatSeq` pair's clause is end-state-readable, so it is produced by the decoder, and
conversely. -/
theorem replayBlocks_flatten_mem (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (hsat : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false) (cp : Clause n × ℕ) :
    cp ∈ (replayBlocks cs (deepestEnd cs F ρ) (replayLabel cs F ρ)).flatten ↔
      cp ∈ deepestSatSeq cs F ρ := by
  obtain ⟨C, p⟩ := cp
  rw [replayBlocks_eq_filter, List.mem_flatten]
  constructor
  · rintro ⟨blk, hblk, hin⟩
    rw [List.mem_map] at hblk
    obtain ⟨⟨C', ps⟩, hcp', rfl⟩ := hblk
    rw [List.mem_map] at hin
    obtain ⟨q, hq, hqeq⟩ := hin
    rw [List.mem_filter, List.mem_map] at hcp'
    obtain ⟨⟨C'', hC'', hC''eq⟩, _⟩ := hcp'
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hC''eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hqeq
    exact (mem_deepestSatPositions cs F ρ C'' q).mp hq
  · intro hmem
    have hC : C ∈ leafClauses cs (deepestEnd cs F ρ) :=
      deepestSatSeq_clause_mem_leafClauses cs F ρ hmem hsat
    have hp : p ∈ deepestSatPositions cs F ρ C := (mem_deepestSatPositions cs F ρ C p).mpr hmem
    refine ⟨(deepestSatPositions cs F ρ C).map (fun q => (C, q)), ?_, ?_⟩
    · rw [List.mem_map]
      refine ⟨(C, deepestSatPositions cs F ρ C), ?_, rfl⟩
      rw [List.mem_filter, List.mem_map]
      refine ⟨⟨C, hC, rfl⟩, ?_⟩
      simp only [decide_eq_true_eq]
      exact fun he => by rw [he] at hp; exact absurd hp (by simp)
    · rw [List.mem_map]; exact ⟨p, hp, rfl⟩

/-- **Replay soundness (order-insensitive).**  The decoder recovers the deepest selected set:
`decodeSatSeq (replayBlocks …).flatten = deepestSatSel`.  This is `replayBlocks_correct` at the
`decodeSatSeq` level — the alignment dissolved by order-insensitivity. -/
theorem replayBlocks_decodeSatSeq (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (hsat : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false) :
    decodeSatSeq (replayBlocks cs (deepestEnd cs F ρ) (replayLabel cs F ρ)).flatten
      = deepestSatSel cs F ρ := by
  rw [decodeSatSeq_eq_of_mem (replayBlocks_flatten_mem cs F ρ hsat),
    ← deepestSatSel_eq_decodeSatSeq]

/-! ## Stage 4: determinism — the end-state and label determine `ρ`

The count's core: the deepest end-state together with the replay label determine `ρ`.  From the
replay soundness the satisfy set is determined; threading adds the label-free falsify set
(`decodedSel`), giving the whole selected set, and `deepestEnd_inj` recovers `ρ`.  This is the
injectivity any switching count consumes.  (The remaining step — packing `replayLabel` into the fixed
`(2w)^s` type `PathLabel w s` — re-meets the empty-block skip obstruction and is the loose/tight
label-encoding question, separate from this determinism.) -/

/-- **Determinism.**  For restrictions that falsify nothing and whose deepest leaves are unsatisfied,
equal deepest end-states and equal replay labels force `ρ = σ`. -/
theorem replay_inj (cs : List (Clause n)) (F : ℕ) {ρ σ : Fin n → Option Bool}
    (hρ : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hσ : SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false)
    (hnfρ : ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hnfσ : ∀ T ∈ cs, SwitchingCounting.termFalsified σ T = false)
    (hend : deepestEnd cs F ρ = deepestEnd cs F σ)
    (hlab : replayLabel cs F ρ = replayLabel cs F σ) :
    ρ = σ := by
  have h1 : deepestSatSel cs F ρ = deepestSatSel cs F σ := by
    rw [← replayBlocks_decodeSatSeq cs F ρ hρ, ← replayBlocks_decodeSatSeq cs F σ hσ, hend, hlab]
  have h2 : deepestSel cs F ρ = deepestSel cs F σ := by
    rw [← decodedSel_union_satSel_eq_deepestSel hnfρ, ← decodedSel_union_satSel_eq_deepestSel hnfσ,
      hend, h1]
  exact deepestEnd_inj cs F hend h2

/-! ## Loose general count

A real end-to-end general switching count, validating the decoder architecture: the recovered
selected set `deepestSatSel ρ` (which the replay decoder produces — `replayBlocks_decodeSatSeq`) is a
finite label (`Finset (Fin n)`, card `2^n`), and together with the deepest end-state determines `ρ`
(the threading + `deepestEnd_inj` core of `replay_inj`).  So the deepest-branch bad set is counted by
`(end-state, recovered-set)` with no read-once or no-skip restriction — only "ρ falsifies nothing".
The bound is loose (`2^n`); the tight `(2w)^s` is the no-skip / packing refinement. -/

/-- **Loose general deepest-branch count.**  For a bad set of restrictions that each falsify no term,
with deepest end-states in `Short`, `|Bad| ≤ |Short| · 2^n` — the recovered selected set as label. -/
theorem deepest_loose_count (cs : List (Clause n)) (F : ℕ)
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false) :
    Bad.card ≤ Short.card * 2 ^ n := by
  refine SwitchingCounting.card_bad_le_label_card (deepestEnd cs F)
    (fun ρ => deepestSatSel cs F ρ) (le_of_eq (by rw [Fintype.card_finset, Fintype.card_fin]))
    hmem ?_
  intro ρ hρ σ hσ hend hsat
  have hsat' : deepestSatSel cs F ρ = deepestSatSel cs F σ := hsat
  have h2 : deepestSel cs F ρ = deepestSel cs F σ := by
    rw [← decodedSel_union_satSel_eq_deepestSel (hnf ρ hρ),
      ← decodedSel_union_satSel_eq_deepestSel (hnf σ hσ), hend, hsat']
  exact deepestEnd_inj cs F hend h2

/-! ## No-skip tight `(2w)^s` count

When no leaf-readable clause is immediately falsified (every replay block is nonempty), the empty-block
obstruction vanishes and the sharp Håstad label applies: pack `replayLabel` into `PathLabel w s` via
`ungroupBlocks → toFinW → flatToLabel` — an injective chain on nonempty, in-range, length-`s` blocks —
and the injectivity composes with `replay_inj` to feed `card_bad_le_encoding`, yielding the tight
`(2w)^s`. -/

/-- **No-skip tight `(2w)^s` count.**  For a bad set where each restriction falsifies nothing, has an
unsatisfied deepest leaf, all replay blocks nonempty (no immediate falsify), positions `< w`, and the
flattened label has length `s`, with deepest end-states in `Short`: `|Bad| ≤ |Short| · (2w)^s`. -/
theorem deepest_noskip_tight_count {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hns : ∀ ρ ∈ Bad, ∀ b ∈ replayLabel cs F ρ, b ≠ [])
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad,
      (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  refine SwitchingCounting.card_bad_le_encoding (deepestEnd cs F)
    (fun ρ => SwitchingCounting.flatToLabel
      (SwitchingCounting.toFinW w (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ))))
    hmem ?_
  intro ρ hρ σ hσ hend hlab
  have hlab' : (SwitchingCounting.flatToLabel
      (SwitchingCounting.toFinW w (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)))
        : SwitchingCounting.PathLabel w s)
      = SwitchingCounting.flatToLabel
        (SwitchingCounting.toFinW w (SwitchingCounting.ungroupBlocks (replayLabel cs F σ))) := hlab
  have h1 : SwitchingCounting.toFinW w (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ))
      = SwitchingCounting.toFinW w (SwitchingCounting.ungroupBlocks (replayLabel cs F σ)) :=
    SwitchingCounting.flatToLabel_inj
      (by rw [SwitchingCounting.toFinW, List.length_map]; exact hlen ρ hρ)
      (by rw [SwitchingCounting.toFinW, List.length_map]; exact hlen σ hσ) hlab'
  have h2 : SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)
      = SwitchingCounting.ungroupBlocks (replayLabel cs F σ) :=
    SwitchingCounting.toFinW_inj w (hpos ρ hρ) (hpos σ hσ) h1
  have h3 : replayLabel cs F ρ = replayLabel cs F σ :=
    SwitchingCounting.ungroupBlocks_inj (hns ρ hρ) (hns σ hσ) h2
  exact replay_inj cs F (hleaf ρ hρ) (hleaf σ hσ) (hnf ρ hρ) (hnf σ hσ) hend h3

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.replayBlocks_ne_nil
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.replayBlocks_block_entry_mem_leafClauses
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.replayBlocks_decodeSatSeq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.replay_inj
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_loose_count
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_noskip_tight_count
