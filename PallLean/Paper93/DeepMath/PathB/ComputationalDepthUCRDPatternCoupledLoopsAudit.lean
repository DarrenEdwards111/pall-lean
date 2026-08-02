import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDIndependentIrreversibleLoopsAudit

/-!
# UCRD pattern-coupled loop audit

Private-coordinate loops are too easy. This file tests a denser family: every
`n`-bit pattern names a legal loop, and returning around that loop merges the
whole pattern into the observer state by coordinate-wise disjunction.

The family has `2^n` distinct loop holonomies. A dense pattern can change all
`n` coordinates at once, the updates are persistent and irreversible, and
different pattern loops are genuinely coupled through the same state.
Nevertheless:

* the loop name itself is only an `n`-bit pattern;
* one loop update is one linear scan, charged `n + 3` work;
* every holonomy is represented by the same uniform coordinate-wise operation;
* all pattern holonomies commute and are idempotent.

Thus exponential contextual variety and dense coupling may still be one
polynomially evaluable family. A useful SAT obstruction must rule out a uniform
succinct evaluator for the coupled transports; merely exhibiting exponentially
many contexts or high fan-in updates does not do so.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDPatternCoupledLoopsAudit

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.UCRDLegalLoopTransportAudit
open PallLean.Paper93.DeepMath.PathB.UCRDIndependentIrreversibleLoopsAudit

attribute [local instance] Classical.propDecidable

/-- Merge a contextual pattern irreversibly into the retained global state. -/
def mergePattern {n : Nat} (p s : LoopState n) : LoopState n :=
  fun j ↦ p j || s j

theorem mergePattern_zero {n : Nat} (p : LoopState n) :
    mergePattern p (zeroState n) = p := by
  funext j
  simp [mergePattern, zeroState]

theorem mergePattern_idempotent {n : Nat} (p s : LoopState n) :
    mergePattern p (mergePattern p s) = mergePattern p s := by
  funext j
  simp [mergePattern]

theorem mergePattern_commute {n : Nat} (p q s : LoopState n) :
    mergePattern p (mergePattern q s) =
      mergePattern q (mergePattern p s) := by
  funext j
  simp only [mergePattern]
  rw [← Bool.or_assoc, Bool.or_comm (p j) (q j), Bool.or_assoc]

/-- One four-stage legal context cycle for each succinct pattern. -/
abbrev PatternContext (n : Nat) := LoopState n × ExperienceContext

def patternLegal {n : Nat} : PatternContext n → PatternContext n → Prop
  | (p, c), (q, d) => p = q ∧ experienceLegal c d

/-- Returning from pattern context `p` merges all bits of `p` into state. -/
def patternLoop {n : Nat} (p : LoopState n) :
    LegalTransportLoop (PatternContext n) (LoopState n) where
  legal := patternLegal
  c0 := (p, .opening)
  c1 := (p, .rising)
  c2 := (p, .turning)
  c3 := (p, .returning)
  legal01 := by exact ⟨rfl, trivial⟩
  legal12 := by exact ⟨rfl, trivial⟩
  legal23 := by exact ⟨rfl, trivial⟩
  legal30 := by exact ⟨rfl, trivial⟩
  transport01 := id
  transport12 := id
  transport23 := id
  transport30 := mergePattern p
  cost01 := 1
  cost12 := 1
  cost23 := 1
  cost30 := n

theorem patternLoop_holonomy {n : Nat} (p s : LoopState n) :
    (patternLoop p).holonomy s = mergePattern p s := by
  rfl

theorem patternLoop_recovers_name {n : Nat} (p : LoopState n) :
    (patternLoop p).holonomy (zeroState n) = p := by
  rw [patternLoop_holonomy, mergePattern_zero]

/-- Distinct pattern names yield distinct global holonomy functions. -/
theorem pattern_holonomy_injective {n : Nat} :
    Function.Injective (fun p : LoopState n ↦ (patternLoop p).holonomy) := by
  intro p q hpq
  calc
    p = (patternLoop p).holonomy (zeroState n) :=
      (patternLoop_recovers_name p).symm
    _ = (patternLoop q).holonomy (zeroState n) := congrFun hpq (zeroState n)
    _ = q := patternLoop_recovers_name q

theorem loopState_card_eq_two_pow (n : Nat) :
    Fintype.card (LoopState n) = 2 ^ n := by
  simp [LoopState]

/-- The family therefore contains exactly `2^n` succinct loop names and at
least that many distinct holonomies. -/
theorem exponential_distinct_pattern_holonomies (n : Nat) :
    Fintype.card (LoopState n) = 2 ^ n ∧
      Function.Injective
        (fun p : LoopState n ↦ (patternLoop p).holonomy) :=
  ⟨loopState_card_eq_two_pow n, pattern_holonomy_injective⟩

theorem patternLoop_idempotent {n : Nat} (p s : LoopState n) :
    (patternLoop p).holonomy ((patternLoop p).holonomy s) =
      (patternLoop p).holonomy s := by
  simp only [patternLoop_holonomy]
  exact mergePattern_idempotent p s

theorem patternLoop_holonomies_commute {n : Nat}
    (p q s : LoopState n) :
    (patternLoop p).holonomy ((patternLoop q).holonomy s) =
      (patternLoop q).holonomy ((patternLoop p).holonomy s) := by
  simp only [patternLoop_holonomy]
  exact mergePattern_commute p q s

/-- A maximally dense loop name changes every coordinate from the zero state. -/
def densePattern (n : Nat) : LoopState n := fun _ ↦ true

theorem densePattern_changes_every_coordinate (n : Nat) (j : Fin n) :
    (patternLoop (densePattern n)).holonomy (zeroState n) j = true := by
  simp [patternLoop_holonomy, mergePattern, densePattern, zeroState]

theorem patternLoop_work {n : Nat} (p : LoopState n) :
    (patternLoop p).loopWork = n + 3 := by
  simp [LegalTransportLoop.loopWork, patternLoop]
  omega

/-- Uniform work for evaluating one requested coupled loop. -/
def patternQueryWork (n : Nat) : Nat := n + 3

theorem patternQueryWork_isPolynomialBudget :
    IsPolynomialBudget patternQueryWork := by
  refine ⟨1, 4, ?_⟩
  intro n
  simp [patternQueryWork, pow_one]
  omega

/-- Dense, irreversible, exponentially varied loop semantics remain uniformly
polynomial per requested context. -/
theorem coupledLoop_uniform_calibration (n : Nat) :
    Fintype.card (LoopState n) = 2 ^ n ∧
    (∀ p : LoopState n, (patternLoop p).loopWork = patternQueryWork n) :=
  ⟨loopState_card_eq_two_pow n, fun p ↦ patternLoop_work p⟩

end PallLean.Paper93.DeepMath.PathB.UCRDPatternCoupledLoopsAudit

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPatternCoupledLoopsAudit.pattern_holonomy_injective
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPatternCoupledLoopsAudit.exponential_distinct_pattern_holonomies
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPatternCoupledLoopsAudit.patternLoop_holonomies_commute
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPatternCoupledLoopsAudit.patternQueryWork_isPolynomialBudget
