import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSkipDecodeBase
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullSeqWidth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullPathDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDnfCount

/-!
# Term-index-free max-depth counting: exact reduction to base recovery

This file packages the already proved skip-aware canonical path into the finite label type
`SkipLabel w s`, whose cardinality is `(4*w)^s`, and removes all remaining list/width/counting
bookkeeping from the desired term-index-free switching estimate.

The only hypothesis left by `deepest_count_skip_of_base_recovery` is the genuine empty-skip wall:
from the end state and skip label, recover a subrestriction base which agrees with the original
restriction on which terms are falsified.  The existing base-relative decoder then reconstructs the
selected set, and `deepestEnd_inj` reconstructs the original restriction.

Thus any future solution of base recovery immediately yields the unconditional, clause-count-free
bound `|Bad| <= |Short| * (4*w)^s`; no further encoding or cardinal arithmetic is needed.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

variable {n : ℕ}

/-- Clamp a skip step into the finite width-`w` alphabet. -/
def skipToFin (w : ℕ) [NeZero w] (t : ℕ × Bool × Bool) : SkipStepLabel w :=
  (⟨t.1 % w, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne w))⟩, t.2.1, t.2.2)

/-- Forget the finite proof carried by a skip step. -/
def finToSkip {w : ℕ} (t : SkipStepLabel w) : ℕ × Bool × Bool :=
  (t.1.val, t.2.1, t.2.2)

/-- Pack a variable-length skip sequence into a fixed-length label. -/
def flatToSkipLabel (w s : ℕ) [NeZero w] (l : List (ℕ × Bool × Bool)) : SkipLabel w s :=
  fun i => (l[i.val]?).elim default (skipToFin w)

/-- Packing and reading back is exact for a length-`s`, width-bounded skip sequence. -/
theorem map_finToSkip_flatToSkipLabel {w s : ℕ} [NeZero w]
    (l : List (ℕ × Bool × Bool)) (hlen : l.length = s)
    (hb : ∀ t ∈ l, t.1 < w) :
    (List.ofFn (flatToSkipLabel w s l)).map finToSkip = l := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_ofFn, hlen]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_ofFn]
    have hi : i < l.length := by
      rw [hlen]
      rwa [List.length_map, List.length_ofFn] at h1
    have hsome : l[i]? = some l[i] := List.getElem?_eq_getElem hi
    have hbnd := hb l[i] (List.getElem_mem hi)
    simp only [flatToSkipLabel, hsome, Option.elim_some, finToSkip, skipToFin,
      Nat.mod_eq_of_lt hbnd]

end SwitchingCounting

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The exact remaining decoder interface.  The base is computed only from the public encoding
`(end state, skip label)`, and on every bad restriction it is a subrestriction with identical term
falsification state. -/
def SkipBaseRecoverable {w s F : ℕ} [NeZero w] (cs : List (Clause n))
    (Bad : Finset (Restriction n)) : Prop :=
  ∃ B : Restriction n → SkipLabel w s → Restriction n,
    ∀ ρ ∈ Bad,
      let lab := flatToSkipLabel w s (deepestSkipSeq cs F ρ)
      SubRestriction (B (deepestEnd cs F ρ) lab) ρ ∧
        ∀ U ∈ cs, termFalsified (B (deepestEnd cs F ρ) lab) U = termFalsified ρ U

/-- Equality of the finite skip labels recovers equality of their underlying skip sequences on the
depth-`s`, width-`w` event. -/
theorem deepestSkipSeq_eq_of_label_eq {w s F : ℕ} [NeZero w] (cs : List (Clause n))
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) {ρ σ : Restriction n}
    (hρ : (canonicalDT cs F ρ).depth = s) (hσ : (canonicalDT cs F σ).depth = s)
    (hlab : flatToSkipLabel w s (deepestSkipSeq cs F ρ) =
      flatToSkipLabel w s (deepestSkipSeq cs F σ)) :
    deepestSkipSeq cs F ρ = deepestSkipSeq cs F σ := by
  have hlen : ∀ τ : Restriction n, (canonicalDT cs F τ).depth = s →
      (deepestSkipSeq cs F τ).length = s := by
    intro τ ht
    rw [deepestSkipSeq_length, deepestFullSeq_length_eq_depth, ht]
  have hb : ∀ τ : Restriction n, ∀ t ∈ deepestSkipSeq cs F τ, t.1 < w := by
    intro τ t ht
    have hm : (t.1, t.2.1) ∈ deepestFullSeq cs F τ := by
      rw [← deepestSkipSeq_map_full cs F τ]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    exact deepestFullSeq_pos_lt_width cs w hw F τ (t.1, t.2.1) hm
  rw [← map_finToSkip_flatToSkipLabel (deepestSkipSeq cs F ρ) (hlen ρ hρ) (hb ρ),
      ← map_finToSkip_flatToSkipLabel (deepestSkipSeq cs F σ) (hlen σ hσ) (hb σ), hlab]

/-- **Clause-count-free max-depth bound from the exact base-recovery wall.**  This theorem performs
the complete skip-label injection and cardinality argument. -/
theorem deepest_count_skip_of_base_recovery {w s F : ℕ} [NeZero w]
    {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hbase : SkipBaseRecoverable (w := w) (s := s) (F := F) cs Bad) :
    Bad.card ≤ Short.card * (4 * w) ^ s := by
  obtain ⟨B, hB⟩ := hbase
  refine card_bad_le_label_card (deepestEnd cs F)
    (fun ρ => flatToSkipLabel w s (deepestSkipSeq cs F ρ)) (card_skipLabels_le w s) hmem ?_
  intro ρ hρ σ hσ hend hlab
  have hseq := deepestSkipSeq_eq_of_label_eq cs hw (hdepth ρ hρ) (hdepth σ hσ) hlab
  let labρ := flatToSkipLabel w s (deepestSkipSeq cs F ρ)
  let τ := B (deepestEnd cs F ρ) labρ
  have hBρ := hB ρ hρ
  have hBσ := hB σ hσ
  have hτeq : τ = B (deepestEnd cs F σ)
      (flatToSkipLabel w s (deepestSkipSeq cs F σ)) := by
    simp only [τ, labρ, hend, hlab]
  have hselρ := skipDecode_deepestSkipSeq_base cs F ρ τ hBρ.1 hBρ.2
  have hselσ := skipDecode_deepestSkipSeq_base cs F σ τ (hτeq ▸ hBσ.1) (hτeq ▸ hBσ.2)
  apply deepestEnd_inj cs F hend
  rw [← hselρ, ← hselσ, hend, hseq]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_count_skip_of_base_recovery
