import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingCoverCashout

/-!
# First actual full cover: an OR of shallow decision-tree terms

This file constructs, rather than assumes, a `SwitchingCover` for a named broader top-control class.
A `TreeDNFRepresentation` expresses the top control as an OR of `L` Boolean decision trees, each of
depth at most `d`.  It is a decision-tree analogue of explicit DNF: each residual tree is one term,
and the list of terms covers acceptance in both directions.

The resulting cover has exactly `L` leaves and residual depth `d`.  If `L ≤ 2^q`, total work is at
most `2^(q+d)`.  Against the true `r+k` active variables, `q+d ≤ (r+k)-s` gives a genuine
`2^((r+k)-s)` algorithm.  In particular, polynomially many constant-depth terms give exponential
savings.

This does not yet cover arbitrary AC0 controls.  Its importance is that it is the first concrete
non-padding construction satisfying the full semantic cover interface; the next lift must compile
a syntactic bounded-width DNF (and then switched AC0 residuals) into this representation with the
same quantitative budget.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TreeDNFFullCover

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl
open PallLean.Paper93.DeepMath.PathB.ACC0SeparatorPivotBranching
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCoverCashout

variable {r k : ℕ}

/-- The top control is an OR of `termCount` decision-tree terms, uniformly depth-bounded. -/
structure TreeDNFRepresentation (C : OracleControl k) where
  termCount : ℕ
  depthBound : ℕ
  term : Fin termCount → BoolDecisionTree k
  eval_iff : ∀ y, controlEval C y = true ↔ ∃ i, (term i).eval y = true
  termDepth : ∀ i, (term i).depth ≤ depthBound

/-- An OR-of-trees representation constructs the required full semantic switching cover. -/
def toSwitchingCover (C : SeparatorPivotCircuit r k) (R : TreeDNFRepresentation C.top)
    (branchBits : ℕ) (hterms : R.termCount ≤ 2 ^ branchBits) : SwitchingCover C where
  leafCount := R.termCount
  branchBits := branchBits
  residualDepth := R.depthBound
  tree := R.term
  correct := by
    rw [sat_iff_top]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨i, hi⟩ := (R.eval_iff y).mp hy
      exact ⟨i, y, hi⟩
    · rintro ⟨i, y, hi⟩
      exact ⟨y, (R.eval_iff y).mpr ⟨i, hi⟩⟩
  leafBound := hterms
  depthBound := R.termDepth

/-- Exact cover-work expression for the constructed Tree-DNF cover. -/
theorem coverWork_toSwitchingCover (C : SeparatorPivotCircuit r k)
    (R : TreeDNFRepresentation C.top) (q : ℕ) (hterms : R.termCount ≤ 2 ^ q) :
    coverWork (toSwitchingCover C R q hterms) = R.termCount * 2 ^ R.depthBound := rfl

/-- Quantitative full-cover bound for the named Tree-DNF class. -/
theorem treeDNF_cover_work_le (C : SeparatorPivotCircuit r k)
    (R : TreeDNFRepresentation C.top) (q : ℕ) (hterms : R.termCount ≤ 2 ^ q) :
    coverWork (toSwitchingCover C R q hterms) ≤ 2 ^ (q + R.depthBound) :=
  coverWork_le_combined (toSwitchingCover C R q hterms)

/-- **Genuine active-normalized speedup for Tree-DNF tops.** -/
theorem treeDNF_active_speedup (C : SeparatorPivotCircuit r k)
    (R : TreeDNFRepresentation C.top) (q saving : ℕ)
    (hterms : R.termCount ≤ 2 ^ q) (hpos : 0 < saving) (hs : saving ≤ r + k)
    (hbudget : q + R.depthBound ≤ (r + k) - saving) :
    coverWork (toSwitchingCover C R q hterms) < 2 ^ (r + k) :=
  coverWork_lt_active_bruteforce (toSwitchingCover C R q hterms)
    saving hpos hs hbudget

/-- The constructed cover carries the original circuit's SAT semantics in both directions. -/
theorem treeDNF_cover_correct (C : SeparatorPivotCircuit r k)
    (R : TreeDNFRepresentation C.top) (q : ℕ) (hterms : R.termCount ≤ 2 ^ q) :
    (∃ σ p, C.eval σ p = true) ↔
      ∃ i : Fin R.termCount, ∃ y, (R.term i).eval y = true :=
  (toSwitchingCover C R q hterms).correct

end PallLean.Paper93.DeepMath.PathB.ACC0TreeDNFFullCover

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TreeDNFFullCover.toSwitchingCover
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TreeDNFFullCover.treeDNF_cover_work_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TreeDNFFullCover.treeDNF_active_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TreeDNFFullCover.treeDNF_cover_correct
