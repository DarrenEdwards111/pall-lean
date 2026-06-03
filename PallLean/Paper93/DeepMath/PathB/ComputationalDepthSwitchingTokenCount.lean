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

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonFlatLabel_switching_count
