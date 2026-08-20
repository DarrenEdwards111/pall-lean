import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonLabel

/-!
# The tokenized switching count — `hne`-free

The delimiter-free `(2w)^s` count (`canonMarkLabel_switching_count`) needs `hne` (every canonical
block nonempty), which fails for clauses satisfied by `ρ` alone (empty blocks).  The **tokenized**
canonical label `canonFlatLabel` (`tokFlatten`, with an `endBlock` delimiter per block) tolerates
empty blocks, and its determinacy `canonLabel_det` is already proved **without any `hne`
hypothesis**.

This file turns that into a count.  The token label `canonFlatLabel w ρ cs : List (CanonTok w)` is
embedded — injectively — into the finite type `Fin L → Option (Fin w)` (`tokEncode`: `lit i ↦ some i`,
`endBlock ↦ none`), for bad sets of a fixed canonical-label *length* `L`.  `card_bad_le_label_card`
(the generic finite-label scaffold) then gives:

`canonFlatLabel_switching_count` : `Bad.card ≤ Short.card · (w+1)^L`,

with injectivity from `canonLabel_det` (no `hne`) + `termWalk_inj'`, and `hmem` discharged exactly as
in the delimiter-free route (`completion_mem_stars`).

**Trade-off (honest).**  The label length is `L = s + (number of confirmed clauses)` — the `+#blocks`
is the delimiter cost — so the bound is `(w+1)^L`, weaker than the delimiter-free `(2w)^s` but
**unconditional** (no `hne`).  The two routes are complementary: `(2w)^s` when blocks are nonempty,
`(w+1)^L` otherwise.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- Encode a token as an `Option (Fin w)` (`endBlock ↦ none`) — into a clean finite type. -/
def tokEncode {w : ℕ} : CanonTok w → Option (Fin w)
  | .lit i => some i
  | .endBlock => none

theorem tokEncode_inj {w : ℕ} : Function.Injective (tokEncode (w := w)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [tokEncode]

/-- **The tokenized switching count (no `hne`).**  For width-`w` clause families, on a bad set whose
canonical token label has fixed length `L`, the count `Bad.card ≤ Short.card · (w+1)^L` holds — with
no nonempty-block hypothesis.  Injectivity is the empty-block-tolerant `canonLabel_det`. -/
theorem canonFlatLabel_switching_count {w L : ℕ} [NeZero w] {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hlen : ∀ ρ ∈ Bad, (canonFlatLabel w ρ cs).length = L)
    (hmem : ∀ ρ ∈ Bad, complete ρ (encLits ρ cs) ∈ Short) :
    Bad.card ≤ Short.card * (w + 1) ^ L := by
  refine card_bad_le_label_card (β := Fin L → Option (Fin w))
    (fun ρ => complete ρ (encLits ρ cs))
    (fun ρ i => tokEncode ((canonFlatLabel w ρ cs).getD i .endBlock))
    ?_ hmem ?_
  · rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_fin]
  · intro ρ hρ σ hσ hE hlab
    have hcf : canonFlatLabel w ρ cs = canonFlatLabel w σ cs := by
      apply List.ext_getElem
      · rw [hlen ρ hρ, hlen σ hσ]
      · intro i h1 h2
        have hi : i < L := by rw [hlen ρ hρ] at h1; exact h1
        have hc := congrFun hlab ⟨i, hi⟩
        simp only at hc
        have hg := tokEncode_inj hc
        rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hg
    have hvar := canonLabel_det ρ σ cs hcs hcs hwidth hE hcf
    exact termWalk_inj' (encLits_decode ρ cs hcs) (encLits_decode σ cs hcs) hE hvar

/-- The empty-block-safe token label pays only one delimiter for each confirmed term.
In particular its overhead is additive in the number of DNF terms, rather than a term-index
choice at every queried variable.  This is the quantitative shape needed by a term-index-aware
multi-switching encoding. -/
theorem canonFlatLabel_length_le_path_add_terms {w : ℕ} [NeZero w]
    (rho : Restriction n) (cs : List (Clause n)) :
    (canonFlatLabel w rho cs).length ≤
      (ungroupBlocks (canonPosBlocks (encLits rho cs) ∅
        (cs.filter (termSat (complete rho (encLits rho cs)))))).length + cs.length := by
  let bs := canonPosBlocks (encLits rho cs) ∅
    (cs.filter (termSat (complete rho (encLits rho cs))))
  have hblocks : bs.length ≤ cs.length := by
    have hlen : ∀ (L : List (Clause n)) (claimed : Finset (Fin n)),
        (canonPosBlocks (encLits rho cs) claimed L).length = L.length := by
      intro L
      induction L with
      | nil => intro claimed; rfl
      | cons C rest ih =>
          intro claimed
          simp only [canonPosBlocks, List.length_cons, ih]
    dsimp [bs]
    rw [hlen]
    exact List.length_filter_le _ _
  rw [canonFlatLabel, tokFlatten_length]
  simp only [List.length_map, List.map_map]
  have hsum :
      (bs.map (List.length ∘ fun b => b.map (natToFin w))).sum =
        (bs.map List.length).sum := by
    simp [Function.comp_def]
  rw [show canonPosBlocks (encLits rho cs) ∅
      (cs.filter (termSat (complete rho (encLits rho cs)))) = bs from rfl,
    hsum, ungroupBlocks_length]
  omega

/-- Fiber the tokenized encoding by its actual label length and sum the exact finite-label
counts.  Unlike a fixed-length wrapper, this theorem permits every bad restriction to have a
different number of empty/confirmed blocks. -/
theorem canonFlatLabel_boundedLength_switching_count {w L : ℕ} [NeZero w]
    {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hlen : ∀ rho ∈ Bad, (canonFlatLabel w rho cs).length ≤ L)
    (hmem : ∀ rho ∈ Bad, complete rho (encLits rho cs) ∈ Short) :
    Bad.card ≤ ∑ l ∈ Finset.range (L + 1), Short.card * (w + 1) ^ l := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun rho : Restriction n => (canonFlatLabel w rho cs).length)
    (t := Finset.range (L + 1))]
  · apply Finset.sum_le_sum
    intro l hl
    apply canonFlatLabel_switching_count hcs hwidth
    · intro rho hrho
      exact (Finset.mem_filter.mp hrho).2
    · intro rho hrho
      exact hmem rho ((Finset.mem_filter.mp hrho).1)
  · intro rho hrho
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hlen rho hrho))

/-- **Additive term-overhead switching count.**  If the canonical path part has length at most
`s` and the DNF has at most `m` terms, the unconditional empty-block-safe encoding uses only
token lengths `0,...,s+m`.  Thus the old per-query term factor is replaced by a finite sum whose
largest exponent is `s+m`. -/
theorem canonFlatLabel_pathBound_switching_count {w s m : ℕ} [NeZero w]
    {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hm : cs.length ≤ m)
    (hpath : ∀ rho ∈ Bad,
      (ungroupBlocks (canonPosBlocks (encLits rho cs) ∅
        (cs.filter (termSat (complete rho (encLits rho cs)))))).length ≤ s)
    (hmem : ∀ rho ∈ Bad, complete rho (encLits rho cs) ∈ Short) :
    Bad.card ≤ ∑ l ∈ Finset.range (s + m + 1), Short.card * (w + 1) ^ l := by
  apply canonFlatLabel_boundedLength_switching_count hcs hwidth
  · intro rho hrho
    exact le_trans (canonFlatLabel_length_le_path_add_terms rho cs)
      (Nat.add_le_add (hpath rho hrho) hm)
  · exact hmem

/-- Closed-form cash-out of the bounded-length fiber sum. -/
theorem canonFlatLabel_pathBound_switching_count_closed {w s m : ℕ} [NeZero w]
    {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hm : cs.length ≤ m)
    (hpath : ∀ rho ∈ Bad,
      (ungroupBlocks (canonPosBlocks (encLits rho cs) ∅
        (cs.filter (termSat (complete rho (encLits rho cs)))))).length ≤ s)
    (hmem : ∀ rho ∈ Bad, complete rho (encLits rho cs) ∈ Short) :
    Bad.card ≤ (s + m + 1) * (Short.card * (w + 1) ^ (s + m)) := by
  apply le_trans
    (canonFlatLabel_pathBound_switching_count hcs hwidth hm hpath hmem)
  calc
    (∑ l ∈ Finset.range (s + m + 1), Short.card * (w + 1) ^ l)
        ≤ ∑ _l ∈ Finset.range (s + m + 1),
            Short.card * (w + 1) ^ (s + m) := by
          apply Finset.sum_le_sum
          intro l hl
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right (by omega)
            (Nat.le_of_lt_succ (Finset.mem_range.mp hl))
    _ = (s + m + 1) * (Short.card * (w + 1) ^ (s + m)) := by simp

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonFlatLabel_switching_count
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonFlatLabel_length_le_path_add_terms
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonFlatLabel_boundedLength_switching_count
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonFlatLabel_pathBound_switching_count
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonFlatLabel_pathBound_switching_count_closed
