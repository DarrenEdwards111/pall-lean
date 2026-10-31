import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DecisionTreeObserver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalTree

/-!
# The `DTree → BoolDecisionTree` bridge: switching's canonical tree meets the observer

`…ACC0DecisionTreeObserver` proved the function-level cash-out on the clean `BoolDecisionTree` type
(`dt_observed`: a depth-`d` tree's function has a `≤ 2^d`-cell observer boundary).  The switching arc, however,
expresses its canonical decision tree in a *different* datatype `Depth3.DTree` (`canonicalDTree`).  This file builds
the missing **representation bridge** `toBoolDT : DTree n → BoolDecisionTree n` and proves it preserves both
**semantics** (`eval`) and **depth** — so the observer cash-out transfers verbatim to `DTree`, and in particular to
the switching arc's `canonicalDTree`.

The two datatypes are constructor-for-constructor isomorphic (`leaf`/`node` ↔ `leaf`/`query`, same branch convention,
same depth recurrence), so the bridge is a direct structural map and the preservation proofs are one-line inductions.
The payoff is the genuine composition: the **canonical decision tree of a width-`w` DNF with fuel `F`**
(`canonicalDTree`, depth `≤ F·w` by `canonicalDTree_depth_le`) has an observer boundary of `≤ 2^{F·w}` cells, hence
is SAT-searchable in `< 2^n` once `2^{F·w} < 2^n`.

## What is proved (clean axioms, no `sorry`)

* `toBoolDT` / `toBoolDT_eval` / `toBoolDT_depth` — the bridge and its semantics/depth preservation.
* `dtree_observed` / `dtree_searchable` — `dt_observed`/`dt_searchable` transferred to `Depth3.DTree`.
* `canonicalDTree_observed` / `canonicalDTree_searchable` — the switching canonical tree (depth `≤ F·w`) has a
  `≤ 2^{F·w}`-cell observer boundary, SAT-searchable in `< 2^n` when `2^{F·w} < 2^n`.

## Honest scope

The bridge is the mechanical representation step flagged as separate in `…ACC0DecisionTreeObserver`; it is now done, so
the function-level collapse composes end to end with the switching `canonicalDTree`.  Two honest caveats remain
unchanged: (1) `DTree.eval (canonicalDTree …)` *equals the restricted DNF function* is the canonical-tree soundness
(`Depth3` arc, cited, not re-proved here) — the observer statements here hold for the tree's own function regardless;
(2) switching provably does **not** collapse `MOD` gates (the MOD no-go), so this is the `AC⁰` layer only.  Still the
cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DTreeBridge

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0DecisionTreeObserver
open PallLean.Paper93.DeepMath.PathB.Depth3

variable {n : ℕ}

/-- **The bridge**: re-express a switching `DTree` as a clean `BoolDecisionTree` (constructor-for-constructor). -/
def toBoolDT : Depth3.DTree n → BoolDecisionTree n
  | .leaf b => BoolDecisionTree.leaf b
  | .node v lo hi => BoolDecisionTree.query v (toBoolDT lo) (toBoolDT hi)

/-- **The bridge preserves semantics (proved).** -/
theorem toBoolDT_eval (t : Depth3.DTree n) (x : Fin n → Bool) :
    BoolDecisionTree.eval (toBoolDT t) x = Depth3.DTree.eval t x := by
  induction t with
  | leaf b => rfl
  | node v lo hi ihlo ihhi =>
      simp only [toBoolDT, BoolDecisionTree.eval, Depth3.DTree.eval, ihlo, ihhi]

/-- **The bridge preserves depth (proved).** -/
theorem toBoolDT_depth (t : Depth3.DTree n) :
    (toBoolDT t).depth = Depth3.DTree.depth t := by
  induction t with
  | leaf b => rfl
  | node v lo hi ihlo ihhi =>
      simp only [toBoolDT, BoolDecisionTree.depth, Depth3.DTree.depth, ihlo, ihhi]

/-- **The decision-tree observer transferred to `Depth3.DTree` (proved): `DTree.eval t` is observed by a statistic of
cell-count `≤ 2^{depth t}`.** -/
theorem dtree_observed (t : Depth3.DTree n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S),
      ObservedBy (Depth3.DTree.eval t) stat ∧ Fintype.card S ≤ 2 ^ Depth3.DTree.depth t := by
  obtain ⟨S, fS, dS, stat, hobs, hcard⟩ := dt_observed (toBoolDT t)
  have hfun : BoolDecisionTree.eval (toBoolDT t) = Depth3.DTree.eval t := funext (toBoolDT_eval t)
  rw [hfun] at hobs
  rw [toBoolDT_depth] at hcard
  exact ⟨S, fS, dS, stat, hobs, hcard⟩

/-- **A shallow `Depth3.DTree` function is SAT-searchable below brute force (proved).** -/
theorem dtree_searchable (t : Depth3.DTree n) (hreg : 2 ^ Depth3.DTree.depth t < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (g : S → Bool),
      (Satisfiable (Depth3.DTree.eval t) ↔ ∃ s ∈ Finset.univ.image stat, g s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n := by
  have hfun : BoolDecisionTree.eval (toBoolDT t) = Depth3.DTree.eval t := funext (toBoolDT_eval t)
  have hreg' : 2 ^ (toBoolDT t).depth < 2 ^ n := by rw [toBoolDT_depth]; exact hreg
  obtain ⟨S, fS, dS, stat, g, hsat, hcard⟩ := dt_searchable (toBoolDT t) hreg'
  rw [hfun] at hsat
  exact ⟨S, fS, dS, stat, g, hsat, hcard⟩

/-! ## The switching canonical tree, observed -/

/-- **The switching canonical decision tree has a `≤ 2^{F·w}`-cell observer boundary (proved).**  Composes the bridge
with `canonicalDTree_depth_le` (depth `≤ F·w` for a width-`≤ w` DNF). -/
theorem canonicalDTree_observed (cs : List (Clause n)) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F : ℕ) (σ : Fin n → Option Bool) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S),
      ObservedBy (Depth3.DTree.eval (canonicalDTree cs w F σ)) stat ∧ Fintype.card S ≤ 2 ^ (F * w) := by
  obtain ⟨S, fS, dS, stat, hobs, hcard⟩ := dtree_observed (canonicalDTree cs w F σ)
  exact ⟨S, fS, dS, stat, hobs,
    le_trans hcard (Nat.pow_le_pow_right (by norm_num) (canonicalDTree_depth_le cs w hw F σ))⟩

/-- **The switching canonical tree is SAT-searchable below brute force when `2^{F·w} < 2^n` (proved).** -/
theorem canonicalDTree_searchable (cs : List (Clause n)) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F : ℕ) (σ : Fin n → Option Bool) (hreg : 2 ^ (F * w) < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (g : S → Bool),
      (Satisfiable (Depth3.DTree.eval (canonicalDTree cs w F σ)) ↔ ∃ s ∈ Finset.univ.image stat, g s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n :=
  dtree_searchable (canonicalDTree cs w F σ)
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (canonicalDTree_depth_le cs w hw F σ)) hreg)

end PallLean.Paper93.DeepMath.PathB.ACC0DTreeBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DTreeBridge.toBoolDT_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DTreeBridge.dtree_observed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DTreeBridge.canonicalDTree_searchable
