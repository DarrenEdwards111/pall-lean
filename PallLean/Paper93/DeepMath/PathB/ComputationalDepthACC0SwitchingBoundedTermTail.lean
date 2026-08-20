import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingDepthCorrectedBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessDischarge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarShell
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CompactWitnessLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingShellBuckets

/-!
# Fixed-shell canonical-depth tail for bounded term count

The unconditional witnessed reconstruction pays `(2 w m)^s`, where `m` bounds the number of DNF
terms.  This file converts that theorem to a fixed-star cardinal bound and instantiates the first
honest dyadic case: width two, at most one term, `n=100`, `K=5`, bad depth at least three.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermTail

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingDepthCorrectedBridge
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

/-- Unconditional witnessed reconstruction converted to an exact fixed-star depth-shell count. -/
theorem canonicalDepth_shell_count_witness
    {n w K s F m : ℕ} [NeZero w] [NeZero m]
    (cs : List (Clause n)) {Bad : Finset (Restriction n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hstars : ∀ ρ ∈ Bad, stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s) :
    Bad.card ≤ n.choose (K - s) * 2 ^ (n - (K - s)) * (2 * w * m) ^ s := by
  let Short : Finset (Restriction n) :=
    Finset.univ.filter fun ρ => stars ρ = K - s
  have hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short := by
    intro ρ hρ
    simpa only [Short] using
      (deepestEnd_mem_shell cs F ρ (hstars ρ hρ) (hdepth ρ hρ))
  have h := deepest_count_witness_unconditional hw hm hdepth hmem
  simpa only [Short, card_stars_eq] using h

/-- For width-two DNFs with at most one term, the *actual canonical-depth* bad part of the five-star
shell has dyadic mass at most `1/8`.  This is the corrected counterpart of the earlier block-stream
tail, now controlling the same max-depth quantity used by the semantic collapse. -/
theorem oneTerm_depthCorrectBad_dyadic
    (cs : List (Clause 100))
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) (hm : cs.length ≤ 1) :
    (depthCorrectBad cs).card * 2 ^ 3 ≤ (100).choose 5 * 2 ^ (100 - 5) := by
  let B : ℕ → Finset (Restriction 100) := fun s =>
    (depthCorrectBad cs).filter fun ρ => (canonicalDT cs 5 ρ).depth = s
  have shell (s : ℕ) :
      (B s).card ≤ (100).choose (5 - s) * 2 ^ (100 - (5 - s)) * (2 * 2 * 1) ^ s := by
    apply canonicalDepth_shell_count_witness cs hw hm
    · intro ρ hρ
      have hbad : ρ ∈ depthCorrectBad cs := (Finset.mem_filter.mp hρ).1
      exact (mem_depthCorrectBad_iff cs ρ).mp hbad |>.1
    · intro ρ hρ
      exact (Finset.mem_filter.mp hρ).2
  have h3 := shell 3
  have h4 := shell 4
  have h5 := shell 5
  have hsum : (depthCorrectBad cs).card = (B 3).card + (B 4).card + (B 5).card := by
    rw [depthCorrectBad_card_eq_shell_sum]
    have hi : Finset.Icc 3 5 = {3, 4, 5} := by decide
    rw [hi]
    simp [B, add_assoc]
  rw [hsum]
  norm_num [Nat.choose] at h3 h4 h5 ⊢
  omega

/-- **Corrected selected-bucket work bound for the one-term fragment.**  The tail now controls
canonical max depth, the concrete buckets partition that same bad set, and the good cost `2^2`
matches genuine canonical depth below three. -/
theorem oneTerm_depthCorrect_selectedBucket_activeGap
    (cs : List (Clause 100))
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) (hm : cs.length ≤ 1) :
    ∃ i : Fin ((100).choose 5),
      goodBadWork 100 (100 - 5) (2 ^ (100 - 5))
        (concreteBadCount (K := 5) (depthCorrectBad cs) i) 2
        ≤ 2 ^ (100 - 2) := by
  have hstars : ∀ ρ ∈ depthCorrectBad cs, stars ρ = 5 := by
    intro ρ hρ
    exact (mem_depthCorrectBad_iff cs ρ).mp hρ |>.1
  have hsum := sum_concreteBadCount (Bad := depthCorrectBad cs) hstars
  have htail := oneTerm_depthCorrectBad_dyadic cs hw hm
  refine aggregateTail_to_selectedBucket_activeGap 100 ((100).choose 5) (100 - 5) 2 2
    (Nat.choose_pos (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (concreteBadCount (K := 5) (depthCorrectBad cs)) ?_ (by norm_num)
  simpa [hsum] using htail

/-! ## Two terms: restore the tail by lowering the fixed-shell density -/

/-- Actual canonical-depth failures for the two-term `n=1000`, `K=5` instance. -/
def twoTermDepthBad (cs : List (Clause 1000)) : Finset (Restriction 1000) :=
  Finset.univ.filter fun ρ => stars ρ = 5 ∧ 3 ≤ (canonicalDT cs 5 ρ).depth

theorem mem_twoTermDepthBad_iff (cs : List (Clause 1000)) (ρ : Restriction 1000) :
    ρ ∈ twoTermDepthBad cs ↔ stars ρ = 5 ∧ 3 ≤ (canonicalDT cs 5 ρ).depth := by
  simp [twoTermDepthBad]

theorem twoTermDepthBad_card_eq_shell_sum (cs : List (Clause 1000)) :
    (twoTermDepthBad cs).card =
      ∑ s ∈ Finset.Icc 3 5,
        ((twoTermDepthBad cs).filter fun ρ => (canonicalDT cs 5 ρ).depth = s).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ρ : Restriction 1000 => (canonicalDT cs 5 ρ).depth)
    (t := Finset.Icc 3 5)]
  intro ρ hρ
  have hρ' : ρ ∈ twoTermDepthBad cs := hρ
  rw [mem_twoTermDepthBad_iff] at hρ'
  exact Finset.mem_Icc.mpr ⟨hρ'.2, canonicalDT_depth_le cs 5 ρ⟩

/-- At density `5/1000`, the witnessed `(2wm)^s` count supports two width-two terms while retaining
the dyadic `1/8` exceptional bound. -/
theorem twoTerm_depthBad_dyadic
    (cs : List (Clause 1000))
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) (hm : cs.length ≤ 2) :
    (twoTermDepthBad cs).card * 2 ^ 3 ≤ (1000).choose 5 * 2 ^ (1000 - 5) := by
  let B : ℕ → Finset (Restriction 1000) := fun s =>
    (twoTermDepthBad cs).filter fun ρ => (canonicalDT cs 5 ρ).depth = s
  have shell (s : ℕ) :
      (B s).card ≤ (1000).choose (5 - s) * 2 ^ (1000 - (5 - s)) * (2 * 2 * 2) ^ s := by
    apply canonicalDepth_shell_count_witness cs hw hm
    · intro ρ hρ
      have hbad : ρ ∈ twoTermDepthBad cs := (Finset.mem_filter.mp hρ).1
      exact (mem_twoTermDepthBad_iff cs ρ).mp hbad |>.1
    · intro ρ hρ
      exact (Finset.mem_filter.mp hρ).2
  have h3 := shell 3
  have h4 := shell 4
  have h5 := shell 5
  have hsum : (twoTermDepthBad cs).card = (B 3).card + (B 4).card + (B 5).card := by
    rw [twoTermDepthBad_card_eq_shell_sum]
    have hi : Finset.Icc 3 5 = {3, 4, 5} := by decide
    rw [hi]
    simp [B, add_assoc]
  rw [hsum]
  norm_num [Nat.choose] at h3 h4 h5 ⊢
  omega

/-- Good restrictions in the two-term instance collapse soundly to width-at-most-two CNF. -/
theorem twoTerm_good_collapses_to_twoCNF (cs : List (Clause 1000))
    (ρ : Restriction 1000) (hstars : stars ρ = 5) (hgood : ρ ∉ twoTermDepthBad cs) :
    (∀ x, DTree.agreeRestriction ρ x →
        cnfValue (dtreeToCNF (toDTree (canonicalDT cs 5 ρ))) x = DTree.dnfValue cs x)
      ∧ (∀ C ∈ dtreeToCNF (toDTree (canonicalDT cs 5 ρ)), C.lits.length ≤ 2) := by
  have hshallow : (canonicalDT cs 5 ρ).depth < 3 := by
    rw [mem_twoTermDepthBad_iff] at hgood
    simp only [hstars, true_and, not_le] at hgood
    exact hgood
  have hcollapse := collapse_core_tight 5 3 cs (ρ := ρ) (by omega) hshallow
  exact ⟨hcollapse.1, fun C hC => Nat.le_of_lt_succ (hcollapse.2 C hC)⟩

/-- **Two-term corrected selected-bucket speedup.** -/
theorem twoTerm_depthCorrect_selectedBucket_activeGap
    (cs : List (Clause 1000))
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) (hm : cs.length ≤ 2) :
    ∃ i : Fin ((1000).choose 5),
      goodBadWork 1000 (1000 - 5) (2 ^ (1000 - 5))
        (concreteBadCount (K := 5) (twoTermDepthBad cs) i) 2
        ≤ 2 ^ (1000 - 2) := by
  have hstars : ∀ ρ ∈ twoTermDepthBad cs, stars ρ = 5 := by
    intro ρ hρ
    exact (mem_twoTermDepthBad_iff cs ρ).mp hρ |>.1
  have hsum := sum_concreteBadCount (Bad := twoTermDepthBad cs) hstars
  have htail := twoTerm_depthBad_dyadic cs hw hm
  refine aggregateTail_to_selectedBucket_activeGap 1000 ((1000).choose 5) (1000 - 5) 2 2
    (Nat.choose_pos (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (concreteBadCount (K := 5) (twoTermDepthBad cs)) ?_ (by norm_num)
  simpa [hsum] using htail

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermTail

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermTail.canonicalDepth_shell_count_witness
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermTail.oneTerm_depthCorrectBad_dyadic
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermTail.oneTerm_depthCorrect_selectedBucket_activeGap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermTail.twoTerm_depthBad_dyadic
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermTail.twoTerm_good_collapses_to_twoCNF
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermTail.twoTerm_depthCorrect_selectedBucket_activeGap
