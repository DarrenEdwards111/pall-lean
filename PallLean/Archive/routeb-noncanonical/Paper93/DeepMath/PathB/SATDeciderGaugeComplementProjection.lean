import Mathlib.LinearAlgebra.Projection
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNecessaryRankDrop

/-!
# Complement projections are not the final SAT-decider gauge

This file records a small linear-algebra sanity check around the remaining
`SATDeciderGaugeMap` frontier.

Classically, if the line spanned by the Cook-Levin compiled polynomial is a
proper subspace, mathlib can choose a complement and project onto that line.
That gives a nonidentity idempotent gauge which fixes the compiled polynomial.

The point is negative: by `SATDeciderGaugeNecessaryRankDrop`, any successful
paper-scale gauge must change the relevant SPDP rank of the compiled
polynomial.  Therefore these ordinary complement projections are real linear
maps, but not a route to the load-bearing `Π⋆`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- If the Cook-Levin compiled polynomial spans a proper line, there is a
nonidentity idempotent linear projection fixing that polynomial.

This is only ordinary vector-space linear algebra.  It makes no SPDP
rank-monotonicity or P-side collapse claim. -/
theorem exists_nonidentity_projection_fixing_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hproper :
      Submodule.span Rat
          ({compiledPoly (cook_levin_compilation M n hn2 htb hns)} :
            Set (SATDeciderGaugeSpace M n hn2 htb hns)) ≠ ⊤) :
    ∃ gauge : SATDeciderGaugeMap M n hn2 htb hns,
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
          compiledPoly (cook_levin_compilation M n hn2 htb hns) ∧
        IsIdempotentElem gauge ∧
          gauge ≠ LinearMap.id := by
  classical
  let p : SATDeciderGaugeSpace M n hn2 htb hns :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let U : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns) :=
    Submodule.span Rat ({p} : Set (SATDeciderGaugeSpace M n hn2 htb hns))
  obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
  refine ⟨Submodule.IsCompl.projection hUW, ?_,
    Submodule.IsCompl.projection_isIdempotentElem hUW, ?_⟩
  · have hp_mem : p ∈ U :=
      Submodule.subset_span (by simp [p])
    simp [p, U]
  · intro hid
    have hUtop : U = ⊤ := by
      rw [← Submodule.IsCompl.projection_range hUW, hid, LinearMap.range_id]
    exact hproper (by simpa [U, p] using hUtop)

/-- Any such projection fixing the compiled polynomial is impossible as a
successful SAT-decider gauge package at the paper scale. -/
theorem nonidentity_projection_fixing_compiledPoly_not_subgoals_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (_hidempotent : IsIdempotentElem gauge)
    (_hnonid : gauge ≠ LinearMap.id)
    (hfix :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        compiledPoly (cook_levin_compilation M n hn2 htb hns)) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns gauge :=
  satDeciderGauge_image_eq_raw_compiledPoly_not_subgoals_at_large_n
    M n hn hn2 htb hns gauge hfix

/-! ## Axiom audit anchors -/

#print axioms exists_nonidentity_projection_fixing_compiledPoly
#print axioms nonidentity_projection_fixing_compiledPoly_not_subgoals_at_large_n

end PallLean.Paper93.DeepMath.PathB
