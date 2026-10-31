import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4ParityDecisionTreeCore
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueObserver

/-!
# The decision-tree observer: function-level switching collapse cashed out

The switching arc proves the *function-level* collapse — with high probability over a random restriction, an `AC⁰`
sub-function (`DNF`/`CNF`) collapses to a **shallow decision tree** (`depth_collapse_mass_ge`,
`hastad_switching_prob_tail`).  This file supplies the missing **cash-out**: it converts *decision-tree depth* — the
function-complexity measure switching reduces — into the deduplicated-observer boundary of `…ACC0ResidueObserver`.

The key is that a depth-`d` decision tree's value is determined by the **leaf it reaches**, and a depth-`d` tree has at
most `2^d` leaves.  Crucially the boundary is the *function's* leaf — **independent of how many variables the function
syntactically reads** — so this is a genuinely function-level boundary, not the syntactic-support boundary of
`…ACC0DedupShrink`.  The query node combines its subtrees' boundaries by a **sum** type (`S_low ⊕ S_high`, additive =
leaf count), not a product, which is exactly why the bound is `2^d` and not `2^{(\#queried vars)}`.

So: a function computed by a shallow decision tree (`2^{depth} < 2^n`) is SAT-searchable below brute force.  Composed
with the switching tail (`depth < s` with mass `≥ 1 - (4pw/(1-p))^s`), this is the function-level collapse: whp the
restricted `AC⁰` sub-function has a `< 2^s`-cell observer boundary.

## What is proved (clean axioms, no `sorry`)

* `dt_observed` — **`BoolDecisionTree.eval T` is `ObservedBy` a statistic of cell-count `≤ 2^{T.depth}`** (induction;
  query node uses the sum-typed leaf observer).
* `dt_searchable` — a depth-`d` decision-tree function with `2^d < 2^n` is SAT-searchable in `< 2^n` cells.
* `function_collapse_of_dt` — any function *computed by* such a decision tree is SAT-searchable below brute force.

## Honest scope

This is the cash-out connector, on the clean `BoolDecisionTree` type.  The probabilistic input — that a random
restriction makes the restricted `AC⁰` sub-function shallow with high probability — is the **already-proved** switching
content (`Depth3.depth_collapse_mass_ge`), in the sibling `DTree` representation; a literal `DTree → BoolDecisionTree`
translation is a separate representation step and is **not** done here (I do not fake it).  And switching provably does
**not** collapse `MOD` gates (the proved MOD no-go), so this function-level boundary is for the `AC⁰` layer only.  Still
the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DecisionTreeObserver

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver

variable {n : ℕ}

/-- **The decision-tree observer (proved, induction): `eval T` is observed by a statistic of cell-count `≤ 2^{depth}`.**
The statistic is the *leaf reached*; the query node combines its subtrees by a **sum** type (additive leaf count), which
is what makes the bound `2^{depth}` rather than the (much larger) `2^{\#queried-variables}`. -/
theorem dt_observed (T : BoolDecisionTree n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S),
      ObservedBy (BoolDecisionTree.eval T) stat ∧ Fintype.card S ≤ 2 ^ T.depth := by
  induction T with
  | leaf b =>
      exact ⟨Unit, inferInstance, inferInstance, fun _ => (), ⟨fun _ => b, fun _ => rfl⟩, by simp⟩
  | query i low high ihlow ihhigh =>
      obtain ⟨Sl, fl, dl, statl, ⟨gl, hgl⟩, hcl⟩ := ihlow
      obtain ⟨Sh, fh, dh, stath, ⟨gh, hgh⟩, hch⟩ := ihhigh
      letI := fl; letI := dl; letI := fh; letI := dh
      refine ⟨Sl ⊕ Sh, inferInstance, inferInstance,
        fun x => if x i then Sum.inr (stath x) else Sum.inl (statl x), ?_, ?_⟩
      · refine ⟨Sum.elim gl gh, fun x => ?_⟩
        simp only [BoolDecisionTree.eval, Sum.elim_inr, Sum.elim_inl, apply_ite (Sum.elim gl gh)]
        rw [hgh x, hgl x]
      · simp only [Fintype.card_sum, BoolDecisionTree.depth]
        calc Fintype.card Sl + Fintype.card Sh
            ≤ 2 ^ low.depth + 2 ^ high.depth := Nat.add_le_add hcl hch
          _ ≤ 2 ^ max low.depth high.depth + 2 ^ max low.depth high.depth :=
              Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
                             (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
          _ = 2 ^ (max low.depth high.depth + 1) := by rw [pow_succ]; ring

/-- **A shallow decision-tree function is SAT-searchable below brute force (proved).**  Its image search over the
`≤ 2^{depth}` leaf-cells decides SAT; `< 2^n` once `2^{depth} < 2^n`. -/
theorem dt_searchable (T : BoolDecisionTree n) (hreg : 2 ^ T.depth < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (g : S → Bool),
      (Satisfiable (BoolDecisionTree.eval T) ↔ ∃ s ∈ Finset.univ.image stat, g s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n := by
  obtain ⟨S, fS, dS, stat, ⟨g, hg⟩, hcard⟩ := dt_observed T
  letI := fS; letI := dS
  exact ⟨S, fS, dS, stat, g, observed_sat_iff g hg,
    lt_of_le_of_lt (le_trans (observed_cellCount_le stat) hcard) hreg⟩

/-- **Function-level collapse cash-out (proved): any function *computed by* a shallow decision tree is SAT-searchable
below brute force.**  This is the consequence of the switching collapse: when a random restriction makes the restricted
`AC⁰` sub-function computable by a depth-`d` tree (`2^d < 2^n`), its SAT is decided by an image search over the
function's own leaf-boundary — regardless of how many variables it reads. -/
theorem function_collapse_of_dt (F : (Fin n → Bool) → Bool) (T : BoolDecisionTree n)
    (hT : T.Computes F) (hreg : 2 ^ T.depth < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (g : S → Bool),
      (Satisfiable F ↔ ∃ s ∈ Finset.univ.image stat, g s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n := by
  have hFT : F = BoolDecisionTree.eval T := funext (fun x => (hT x).symm)
  rw [hFT]
  exact dt_searchable T hreg

end PallLean.Paper93.DeepMath.PathB.ACC0DecisionTreeObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DecisionTreeObserver.dt_observed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DecisionTreeObserver.function_collapse_of_dt
