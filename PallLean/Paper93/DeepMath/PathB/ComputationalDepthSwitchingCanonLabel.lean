import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEncLabel

/-!
# The canonical single-assignment label (general tight star count)

**STATUS: REAL.  THE TIGHT STAR COUNT FOR GENERAL (SHARED-VARIABLE) CLAUSE FAMILIES.**

The flat label `encFlatLabel` over-counts a path variable once per confirmed clause containing
it (`encLits_length_le_flatLabel`: the label is `≥` the star count, with equality only for
variable-disjoint clauses).  The fix that works for *general* clause families is the
**canonical single-assignment** label: assign each path variable to the *first* confirmed
clause that names it.  Then the per-clause blocks are **disjoint by construction**, so

> `Σ_{confirmed} |canonBlock| = |⋃_{confirmed} termBlock| = star count`,

with **no clause-disjointness hypothesis** — this is the general resolution of the label
over-count, not the read-once special case.

This file builds `canonBlocks` (the fold assigning each variable to its first clause) and
proves the tight count `canonBlocks_sum_card`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- `|A ∪ B| = |A| + |B \ A|`. -/
theorem card_union_eq_add_sdiff (A B : Finset (Fin n)) :
    (A ∪ B).card = A.card + (B \ A).card := by
  rw [← Finset.union_sdiff_self_eq_union, Finset.card_union_of_disjoint]
  exact Finset.sdiff_disjoint.symm

/-- The canonical per-clause blocks: each clause claims its path variables *not already
claimed* by an earlier clause (so the blocks are pairwise disjoint by construction). -/
def canonBlocks (litList : List (Rung4Literal n)) (claimed : Finset (Fin n)) :
    List (Clause n) → List (Finset (Fin n))
  | [] => []
  | C :: rest =>
      (termBlock litList C \ claimed)
        :: canonBlocks litList (claimed ∪ (termBlock litList C \ claimed)) rest

/-- **Tight count: canonical blocks sum to the union, minus what was already claimed.**
By construction the canonical blocks partition the new variables, so their sizes sum to the
size of the union of `termBlock`s (relative to `claimed`) — *with no disjointness hypothesis on
the clauses*. -/
theorem canonBlocks_sum_card (litList : List (Rung4Literal n)) :
    ∀ (L : List (Clause n)) (claimed : Finset (Fin n)),
      ((canonBlocks litList claimed L).map Finset.card).sum
        = ((L.foldr (fun C acc => termBlock litList C ∪ acc) ∅) \ claimed).card := by
  intro L
  induction L with
  | nil => intro claimed; simp [canonBlocks]
  | cons C rest ih =>
    intro claimed
    simp only [canonBlocks, List.map_cons, List.sum_cons, List.foldr_cons]
    rw [ih (claimed ∪ (termBlock litList C \ claimed))]
    set R := rest.foldr (fun C acc => termBlock litList C ∪ acc) ∅
    have hrhs : (termBlock litList C ∪ R) \ claimed
        = (termBlock litList C \ claimed) ∪ (R \ claimed) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
    have hstep : R \ (claimed ∪ (termBlock litList C \ claimed))
        = (R \ claimed) \ (termBlock litList C \ claimed) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
    rw [hrhs, hstep]
    exact (card_union_eq_add_sdiff _ _).symm

/-- **The canonical label is tight — generally.**  The total size of the canonical
single-assignment blocks over the confirmed terms equals `(encLits ρ cs).length`, i.e. the
star count (`stars ρ - stars (complete ρ (encLits ρ cs))` by `stars_complete_encLits`), with
**no clause variable-disjointness hypothesis**.  This is the general resolution of the
`encFlatLabel` over-count: replacing "all positions" by "first-claim positions" makes the label
length equal the star count for arbitrary (shared-variable) clause families. -/
theorem canonBlocks_sum_card_eq_length (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    ((canonBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs))))).map Finset.card).sum
      = (encLits ρ cs).length := by
  rw [canonBlocks_sum_card, Finset.sdiff_empty,
    ← termWalk_eq_filter_full (complete ρ (encLits ρ cs)) (termBlock (encLits ρ cs)) cs
      cs.length (List.length_filter_le _ _),
    card_termWalkVars_encLits ρ cs hcs]

/-- Every canonical block is disjoint from the variables already claimed when it was produced. -/
theorem canonBlocks_disjoint_claimed (litList : List (Rung4Literal n)) :
    ∀ (L : List (Clause n)) (claimed : Finset (Fin n)) (B : Finset (Fin n)),
      B ∈ canonBlocks litList claimed L → Disjoint B claimed := by
  intro L
  induction L with
  | nil => intro claimed B hB; simp [canonBlocks] at hB
  | cons C rest ih =>
    intro claimed B hB
    rw [canonBlocks, List.mem_cons] at hB
    rcases hB with rfl | hB
    · exact Finset.sdiff_disjoint
    · exact (ih _ B hB).mono_right Finset.subset_union_left

/-- **The canonical blocks are pairwise disjoint.**  Each path variable is claimed by exactly
one (its first) confirmed clause, so the canonical blocks form a genuine *partition* of the
path-variable set — the structural backbone for a canonical encoding (and why the tight count
`canonBlocks_sum_card_eq_length` holds with no clause-disjointness hypothesis). -/
theorem canonBlocks_pairwise_disjoint (litList : List (Rung4Literal n)) :
    ∀ (L : List (Clause n)) (claimed : Finset (Fin n)),
      (canonBlocks litList claimed L).Pairwise (fun A B => Disjoint A B) := by
  intro L
  induction L with
  | nil => intro claimed; simp [canonBlocks]
  | cons C rest ih =>
    intro claimed
    rw [canonBlocks, List.pairwise_cons]
    refine ⟨fun B hB => ?_, ih _⟩
    exact ((canonBlocks_disjoint_claimed litList rest _ B hB).mono_right
      Finset.subset_union_right).symm

/-- **The canonical blocks cover the same variables as the full blocks** (minus what was
already claimed).  The union of the canonical first-claim blocks equals the union of the
`termBlock`s minus `claimed` — first-claim assignment drops *duplicate* coverage but never
loses a variable. -/
theorem canonBlocks_union (litList : List (Rung4Literal n)) :
    ∀ (L : List (Clause n)) (claimed : Finset (Fin n)),
      ((canonBlocks litList claimed L).foldr (· ∪ ·) ∅)
        = ((L.foldr (fun C acc => termBlock litList C ∪ acc) ∅) \ claimed) := by
  intro L
  induction L with
  | nil => intro claimed; simp [canonBlocks]
  | cons C rest ih =>
    intro claimed
    simp only [canonBlocks, List.foldr_cons]
    rw [ih (claimed ∪ (termBlock litList C \ claimed))]
    set R := rest.foldr (fun C acc => termBlock litList C ∪ acc) ∅
    have h1 : (termBlock litList C ∪ R) \ claimed
        = (termBlock litList C \ claimed) ∪ (R \ claimed) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
    have h2 : R \ (claimed ∪ (termBlock litList C \ claimed))
        = (R \ claimed) \ (termBlock litList C \ claimed) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
    rw [h1, h2, Finset.union_sdiff_self_eq_union]

/-- **Canonical blocks recover exactly the path-variable set** (at the union level, no
disjointness needed).  Combined with `tokFlatten_inj`, this is the route to `canonLabel_det`:
the canonical first-claim label determines the path-variable set via `σ*` (confirmed terms) +
the partition. -/
theorem canonBlocks_union_eq_pathvars (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    ((canonBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs))))).foldr (· ∪ ·) ∅)
      = ((encLits ρ cs).map litVar).toFinset := by
  rw [canonBlocks_union, Finset.sdiff_empty,
    ← termWalk_eq_filter_full (complete ρ (encLits ρ cs)) (termBlock (encLits ρ cs)) cs
      cs.length (List.length_filter_le _ _),
    termWalkVars_encLits_eq_pathvars ρ cs hcs]

/-- **Determinism core (`canonLabel_det`, block level).**  If the canonical first-claim block
lists agree, the path-variable sets agree — *immediately* from `canonBlocks_union_eq_pathvars`
(each side's blocks union to its path-variable set).  This is the logical heart of
`canonLabel_det`; what remains to make the *label* `(2w)^s`-sized is to present the blocks as
tokenized `Fin w` positions (`tokFlatten`/`tokFlatten_inj`, below) recovered via the confirmed
terms (which equal `σ*` determines), so that equal flat labels force equal blocks here. -/
theorem canonBlocks_det_pathvars (ρ σ : Restriction n) (cs : List (Clause n))
    (hcsρ : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hcsσ : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hblocks : canonBlocks (encLits ρ cs) ∅ (cs.filter (termSat (complete ρ (encLits ρ cs))))
        = canonBlocks (encLits σ cs) ∅ (cs.filter (termSat (complete σ (encLits σ cs))))) :
    ((encLits ρ cs).map litVar).toFinset = ((encLits σ cs).map litVar).toFinset := by
  rw [← canonBlocks_union_eq_pathvars ρ cs hcsρ, ← canonBlocks_union_eq_pathvars σ cs hcsσ,
    hblocks]

/-! ## Position layer: canonical blocks as clause-relative indices -/

/-- The canonical block of a single term as **clause-relative positions**: the path-literal
positions whose variable is not yet claimed (first-claim positions). -/
def canonPosBlock (litList : List (Rung4Literal n)) (claimed : Finset (Fin n)) (C : Clause n) :
    List ℕ :=
  (blockOf litList C).filter (fun i => (C.lits[i]?).any (fun ℓ => decide (litVar ℓ ∉ claimed)))

/-- **Position↔variable correspondence (per clause).**  Reading the canonical positions of a
term recovers exactly its canonical variable block `termBlock litList C \ claimed`.  The analog
of `blockVars_blockOf`, now respecting the first-claim filter. -/
theorem canonPosBlock_blockVars (litList : List (Rung4Literal n)) (claimed : Finset (Fin n))
    (C : Clause n) :
    blockVars C (canonPosBlock litList claimed C) = termBlock litList C \ claimed := by
  ext v
  rw [Finset.mem_sdiff, mem_blockVars, ← blockVars_blockOf, mem_blockVars]
  constructor
  · rintro ⟨i, hi, hv⟩
    rw [canonPosBlock, List.mem_filter] at hi
    obtain ⟨hib, hP⟩ := hi
    cases hg : C.lits[i]? with
    | none => rw [hg] at hv; simp at hv
    | some ℓ =>
      rw [hg] at hv hP
      simp only [Option.map_some, Option.some.injEq] at hv
      simp only [Option.any_some, decide_eq_true_eq] at hP
      exact ⟨⟨i, hib, by rw [hg]; simp [hv]⟩, hv ▸ hP⟩
  · rintro ⟨⟨i, hib, hv⟩, hvc⟩
    refine ⟨i, ?_, hv⟩
    rw [canonPosBlock, List.mem_filter]
    refine ⟨hib, ?_⟩
    cases hg : C.lits[i]? with
    | none => rw [hg] at hv; simp at hv
    | some ℓ =>
      rw [hg] at hv
      simp only [Option.map_some, Option.some.injEq] at hv
      simp only [hg, Option.any_some, decide_eq_true_eq]
      exact hv ▸ hvc

/-- The canonical position-blocks over a clause list (same first-claim fold as `canonBlocks`,
but recording clause-relative positions instead of variables). -/
def canonPosBlocks (litList : List (Rung4Literal n)) (claimed : Finset (Fin n)) :
    List (Clause n) → List (List ℕ)
  | [] => []
  | C :: rest =>
      canonPosBlock litList claimed C
        :: canonPosBlocks litList (claimed ∪ (termBlock litList C \ claimed)) rest

/-- **The variable blocks are the position blocks read through the clauses.**
`canonBlocks = zipWith blockVars cs (canonPosBlocks)` — so the position-layer label
`canonPosBlocks` together with the clause list recovers the variable-level canonical blocks. -/
theorem canonBlocks_eq_zipWith (litList : List (Rung4Literal n)) :
    ∀ (L : List (Clause n)) (claimed : Finset (Fin n)),
      canonBlocks litList claimed L = List.zipWith blockVars L (canonPosBlocks litList claimed L) := by
  intro L
  induction L with
  | nil => intro claimed; rfl
  | cons C rest ih =>
    intro claimed
    rw [canonBlocks, canonPosBlocks, List.zipWith_cons_cons, canonPosBlock_blockVars,
      ih (claimed ∪ (termBlock litList C \ claimed))]

/-- **`canonLabel_det` at the position-block level.**  Equal completions (`σ*`) and equal
canonical *position*-blocks force equal path-variable sets.  The completion fixes the confirmed
clause list (same `cs`, same `termSat σ*`), and the position-blocks read through those clauses
give the canonical variable blocks (`canonBlocks_eq_zipWith`), whose union is the path-variable
set (`canonBlocks_union_eq_pathvars`).  This is the target determinism; only the `Fin w`
tokenization (`tokFlatten`/`toFinW`) remains to present `canonPosBlocks` as a `(2w)^s` label. -/
theorem canonPosBlocks_det (ρ σ : Restriction n) (cs : List (Clause n))
    (hcsρ : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hcsσ : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hσ : complete ρ (encLits ρ cs) = complete σ (encLits σ cs))
    (hpos : canonPosBlocks (encLits ρ cs) ∅ (cs.filter (termSat (complete ρ (encLits ρ cs))))
        = canonPosBlocks (encLits σ cs) ∅ (cs.filter (termSat (complete σ (encLits σ cs))))) :
    ((encLits ρ cs).map litVar).toFinset = ((encLits σ cs).map litVar).toFinset := by
  refine canonBlocks_det_pathvars ρ σ cs hcsρ hcsσ ?_
  rw [canonBlocks_eq_zipWith, canonBlocks_eq_zipWith, hpos, hσ]

/-! ## Delimiter-tokenized flattening (handles empty blocks) -/

/-- A token of the canonical flat label: either a within-block index (`Fin w`) or an
end-of-block delimiter.  The explicit `endBlock` makes boundary recovery exact **including for
empty blocks** (an empty block flattens to the single token `[endBlock]`), unlike `markLast`
which loses empty blocks. -/
inductive CanonTok (w : ℕ) where
  | lit : Fin w → CanonTok w
  | endBlock : CanonTok w
  deriving DecidableEq

variable {w : ℕ}

/-- Flatten index-blocks with an explicit `endBlock` delimiter after each block. -/
def tokFlatten : List (List (Fin w)) → List (CanonTok w)
  | [] => []
  | b :: bs => b.map CanonTok.lit ++ CanonTok.endBlock :: tokFlatten bs

/-- Group a token stream back into blocks by splitting at `endBlock`. -/
def tokGroup : List (CanonTok w) → List (List (Fin w))
  | [] => []
  | CanonTok.endBlock :: rest => [] :: tokGroup rest
  | CanonTok.lit x :: rest =>
      match tokGroup rest with
      | [] => [[x]]
      | b :: bs => (x :: b) :: bs

/-- Grouping a tokenized block (prepended to a tail) recovers the block — **for any block,
empty or not** (no nonempty hypothesis). -/
theorem tokGroup_append_endBlock (b : List (Fin w)) (rest : List (CanonTok w)) :
    tokGroup (b.map CanonTok.lit ++ CanonTok.endBlock :: rest) = b :: tokGroup rest := by
  induction b with
  | nil => rfl
  | cons x b ih =>
    show tokGroup (CanonTok.lit x :: (b.map CanonTok.lit ++ CanonTok.endBlock :: rest)) = _
    show (match tokGroup (b.map CanonTok.lit ++ CanonTok.endBlock :: rest) with
      | [] => [[x]] | b :: bs => (x :: b) :: bs) = _
    rw [ih]

/-- **Token count of the tokenized flatten.**  Each block contributes its size plus one
`endBlock` delimiter, so the total is `Σ block sizes + #blocks`.  This makes the delimiter cost
explicit: the tokenized label has length `s + #blocks`, not `s`. -/
theorem tokFlatten_length : ∀ bs : List (List (Fin w)),
    (tokFlatten bs).length = (bs.map List.length).sum + bs.length := by
  intro bs
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [tokFlatten, List.length_append, List.length_map, List.length_cons, ih, List.map_cons,
      List.sum_cons, List.length_cons]
    omega

/-- **Round-trip — unconditional.**  Grouping the tokenized blocks recovers them exactly, with
no nonempty-block hypothesis (the `endBlock` delimiter marks every boundary, including empty
blocks).  This is the empty-block fix the canonical label needs. -/
theorem tokGroup_tokFlatten (bs : List (List (Fin w))) : tokGroup (tokFlatten bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [tokFlatten, tokGroup_append_endBlock, ih]

/-- The tokenized flatten is injective — *unconditionally* (no nonempty-block hypothesis). -/
theorem tokFlatten_inj {bs cs : List (List (Fin w))} (h : tokFlatten bs = tokFlatten cs) :
    bs = cs := by
  have := tokGroup_tokFlatten bs
  rw [h, tokGroup_tokFlatten cs] at this
  exact this.symm

/-! ## The canonical flat label and `canonLabel_det` -/

/-- Recover an `ℕ` index list from its `Fin w` coercion (in-range entries). -/
theorem map_natToFin_val [NeZero w] : ∀ {b : List ℕ}, (∀ i ∈ b, i < w) →
    (b.map (natToFin w)).map Fin.val = b := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons x t ih =>
    intro hb
    simp only [List.map_cons, natToFin_val (hb x (List.mem_cons.mpr (Or.inl rfl)))]
    rw [ih (fun i hi => hb i (List.mem_cons.mpr (Or.inr hi)))]

/-- Recover a list of `ℕ` index-blocks from its `Fin w` coercion (in-range entries). -/
theorem map_map_natToFin_val [NeZero w] : ∀ {L : List (List ℕ)}, (∀ b ∈ L, ∀ i ∈ b, i < w) →
    (L.map (fun b => b.map (natToFin w))).map (fun b => b.map (Fin.val)) = L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons b L ih =>
    intro hL
    simp only [List.map_cons]
    rw [map_natToFin_val (hL b (List.mem_cons.mpr (Or.inl rfl))),
      ih (fun b' hb' => hL b' (List.mem_cons.mpr (Or.inr hb')))]

/-- Canonical positions are below the clause width. -/
theorem canonPosBlocks_lt (litList : List (Rung4Literal n)) :
    ∀ (L : List (Clause n)) (claimed : Finset (Fin n)), (∀ T ∈ L, T.lits.length ≤ w) →
      ∀ b ∈ canonPosBlocks litList claimed L, ∀ i ∈ b, i < w := by
  intro L
  induction L with
  | nil => intro claimed _ b hb; simp [canonPosBlocks] at hb
  | cons C rest ih =>
    intro claimed hL b hb i hi
    rw [canonPosBlocks, List.mem_cons] at hb
    rcases hb with rfl | hb
    · rw [canonPosBlock, List.mem_filter] at hi
      exact lt_of_lt_of_le (blockOf_lt hi.1) (hL C (List.mem_cons.mpr (Or.inl rfl)))
    · exact ih _ (fun T hT => hL T (List.mem_cons.mpr (Or.inr hT))) b hb i hi

/-- **The canonical flat label.**  The canonical first-claim position-blocks over the confirmed
terms, coerced to `Fin w` (clause-relative indices, `< w`) and flattened with the `endBlock`
delimiter.  A `(2w)^s`-class label that tolerates empty blocks. -/
def canonFlatLabel (w : ℕ) [NeZero w] (ρ : Restriction n) (cs : List (Clause n)) :
    List (CanonTok w) :=
  tokFlatten ((canonPosBlocks (encLits ρ cs) ∅
    (cs.filter (termSat (complete ρ (encLits ρ cs))))).map (fun b => b.map (natToFin w)))

/-- **`canonLabel_det` — the target.**  For width-`w` clause families: equal completions
(`σ*`) and equal canonical flat labels force equal path-variable sets.  This is the working
Route B decoder (`encLits`) combined with the canonical first-claim label — solving the general
shared-variable over-count (tight `s`, `canonBlocks_sum_card_eq_length`) and the empty-block
boundary problem (`tokFlatten`), with the per-step recomputation supplied by `σ*` (confirmed
terms) rather than stored ambiguously (no `replayPath` end-state ambiguity). -/
theorem canonLabel_det [NeZero w] (ρ σ : Restriction n) (cs : List (Clause n))
    (hcsρ : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hcsσ : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hσ : complete ρ (encLits ρ cs) = complete σ (encLits σ cs))
    (hlabel : canonFlatLabel w ρ cs = canonFlatLabel w σ cs) :
    ((encLits ρ cs).map litVar).toFinset = ((encLits σ cs).map litVar).toFinset := by
  refine canonPosBlocks_det ρ σ cs hcsρ hcsσ hσ ?_
  have h1 := tokFlatten_inj hlabel
  have hwρ := canonPosBlocks_lt (encLits ρ cs)
    (cs.filter (termSat (complete ρ (encLits ρ cs)))) ∅
    (fun T hT => hwidth T (List.mem_of_mem_filter hT))
  have hwσ := canonPosBlocks_lt (encLits σ cs)
    (cs.filter (termSat (complete σ (encLits σ cs)))) ∅
    (fun T hT => hwidth T (List.mem_of_mem_filter hT))
  have h2 := congrArg (fun L => L.map (fun b => b.map (Fin.val : Fin w → ℕ))) h1
  dsimp only at h2
  rwa [map_map_natToFin_val hwρ, map_map_natToFin_val hwσ] at h2

/-! ## The genuine `(2w)^s` canonical label (delimiter-free, via `PathLabel w s`) -/

/-- **The canonical `(2w)^s` label.**  The delimiter-free `(index, isLast)`-per-position
encoding of the canonical first-claim blocks, packed into `PathLabel w s` (cardinality
`(2w)^s`, `card_pathLabels`).  No `endBlock` delimiter cost: the boundary is the `isLast` bit on
each position (`markLast`/`ungroupBlocks`), so the label lives in exactly `(2w)^s` — provided
the canonical blocks are nonempty (which `markLast` requires). -/
def canonMarkLabel (w s : ℕ) [NeZero w] (ρ : Restriction n) (cs : List (Clause n)) :
    PathLabel w s :=
  flatToLabel (toFinW w (ungroupBlocks (canonPosBlocks (encLits ρ cs) ∅
    (cs.filter (termSat (complete ρ (encLits ρ cs)))))))

/-- **`canonLabel_det` with the `(2w)^s` label.**  The canonical `PathLabel w s` label (an
element of a `(2w)^s`-element type) together with the completion `σ*` determines the
path-variable set — for width-`w` clause families with nonempty canonical blocks and flat
length `s`.  This is the genuine `(2w)^s` cardinality realization: the determining label lives
in `PathLabel w s`, no delimiter overhead. -/
theorem canonMarkLabel_det (w s : ℕ) [NeZero w] (ρ σ : Restriction n) (cs : List (Clause n))
    (hcsρ : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hcsσ : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hneρ : ∀ b ∈ canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))), b ≠ [])
    (hneσ : ∀ b ∈ canonPosBlocks (encLits σ cs) ∅
        (cs.filter (termSat (complete σ (encLits σ cs)))), b ≠ [])
    (hlenρ : (ungroupBlocks (canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))))).length = s)
    (hlenσ : (ungroupBlocks (canonPosBlocks (encLits σ cs) ∅
        (cs.filter (termSat (complete σ (encLits σ cs)))))).length = s)
    (hσ : complete ρ (encLits ρ cs) = complete σ (encLits σ cs))
    (hlabel : canonMarkLabel w s ρ cs = canonMarkLabel w s σ cs) :
    ((encLits ρ cs).map litVar).toFinset = ((encLits σ cs).map litVar).toFinset := by
  refine canonPosBlocks_det ρ σ cs hcsρ hcsσ hσ ?_
  have hidxρ : ∀ p ∈ ungroupBlocks (canonPosBlocks (encLits ρ cs) ∅
      (cs.filter (termSat (complete ρ (encLits ρ cs))))), p.1 < w := by
    intro p hp
    obtain ⟨b, hb, hpb⟩ := ungroupBlocks_fst_mem hp
    exact canonPosBlocks_lt (encLits ρ cs) _ ∅
      (fun T hT => hwidth T (List.mem_of_mem_filter hT)) b hb p.1 hpb
  have hidxσ : ∀ p ∈ ungroupBlocks (canonPosBlocks (encLits σ cs) ∅
      (cs.filter (termSat (complete σ (encLits σ cs))))), p.1 < w := by
    intro p hp
    obtain ⟨b, hb, hpb⟩ := ungroupBlocks_fst_mem hp
    exact canonPosBlocks_lt (encLits σ cs) _ ∅
      (fun T hT => hwidth T (List.mem_of_mem_filter hT)) b hb p.1 hpb
  have hfl := flatToLabel_inj (s := s) (by simpa only [toFinW, List.length_map] using hlenρ)
    (by simpa only [toFinW, List.length_map] using hlenσ) hlabel
  exact ungroupBlocks_inj hneρ hneσ (toFinW_inj w hidxρ hidxσ hfl)

/-- The canonical label space has cardinality `(2w)^s`. -/
theorem card_canonMarkLabel_space (w s : ℕ) :
    (Finset.univ : Finset (PathLabel w s)).card = (2 * w) ^ s := by
  rw [Finset.card_univ]; exact card_pathLabels w s

/-- **The `(2w)^s` switching count with the tight canonical label.**  For width-`w` clause
families: if every bad `ρ` has nonempty canonical blocks and canonical flat length `s`, and its
completion lands in `Short`, then `|Bad| ≤ |Short| · (2w)^s`.  Here `s` is the *canonical* flat
length — the **star count** (`canonBlocks_sum_card_eq_length`), tight for *arbitrary*
(shared-variable) clause families and with **no delimiter overhead** (`PathLabel w s` is exactly
`(2w)^s`).  The decoder side is `encLits_decode`; injectivity is `canonMarkLabel_det` +
`termWalk_inj'`. -/
theorem canonMarkLabel_switching_count {w s : ℕ} [NeZero w] {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hne : ∀ ρ ∈ Bad, ∀ b ∈ canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))), b ≠ [])
    (hlen : ∀ ρ ∈ Bad, (ungroupBlocks (canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))))).length = s)
    (hmem : ∀ ρ ∈ Bad, complete ρ (encLits ρ cs) ∈ Short) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  refine card_bad_le_encoding (fun ρ => complete ρ (encLits ρ cs))
    (fun ρ => canonMarkLabel w s ρ cs) hmem ?_
  intro ρ hρ σ hσ hE hlab
  have hE' : complete ρ (encLits ρ cs) = complete σ (encLits σ cs) := hE
  have hvar := canonMarkLabel_det w s ρ σ cs hcs hcs hwidth (hne ρ hρ) (hne σ hσ)
    (hlen ρ hρ) (hlen σ hσ) hE' hlab
  exact termWalk_inj' (encLits_decode ρ cs hcs) (encLits_decode σ cs hcs) hE' hvar

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonLabel_det
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonMarkLabel_det
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonMarkLabel_switching_count
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.tokFlatten_length
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonBlocks_sum_card
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonBlocks_sum_card_eq_length
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonBlocks_pairwise_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonBlocks_union_eq_pathvars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonBlocks_det_pathvars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonPosBlock_blockVars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonBlocks_eq_zipWith
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonPosBlocks_det
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.tokGroup_tokFlatten
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.tokFlatten_inj
