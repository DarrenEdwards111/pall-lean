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

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonBlocks_sum_card
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonBlocks_sum_card_eq_length
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonBlocks_pairwise_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.tokGroup_tokFlatten
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.tokFlatten_inj
