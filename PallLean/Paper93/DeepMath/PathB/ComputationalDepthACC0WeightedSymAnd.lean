import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymmetricObserver

/-!
# The weighted-count `SYM` observer: closing the `ZMod p`-linear → count-mod-`p` gap

`…ACC0RSToSymAnd` showed the RS low-degree approximant is a `ZMod p`-**linear combination** of monomial-`AND` gates,
`∑_j cⱼ · monoAND_j`.  The remaining algebraic gap to the `SYM∘AND` form is that a `SYM` (symmetric/count) gate reads
an **unweighted count**, not a weighted sum.  This file closes it by **coefficient duplication**: the weighted count
`∑_j cⱼ · [gⱼ accepts]` is exactly the count of accepting gates in the multiset where gate `j` appears `cⱼ` times, so a
`SYM` gate over that (expanded) family computes it.

The weighted count has boundary `≤ (∑_j cⱼ) + 1` (not `2^m`), and over `ZMod p` (taking `cⱼ = (coeffⱼ).val`) its
residue is exactly the polynomial value `∑_j coeffⱼ · monoAND_j` — so a threshold of the `ZMod p` polynomial is a `SYM`
gate over the duplicated monomial-`AND`s, searchable in `< 2^n` once `∑ cⱼ + 1 < 2^n` (`≤ (p-1)·∑_{i≤D}C(n,i) + 1` for
the RS approximant).

## What is proved (clean axioms, no `sorry`)

* `weightedGateCount` / `weightedSymEval` — the weighted count of accepting gates and a symmetric function of it.
* `weightedGateCount_le` — the weighted count is `≤ ∑_j cⱼ` (total weight).
* `weightedSym_observed` / `weightedSym_count_card_le` / `weightedSym_searchable` — the weighted `SYM` observer
  (boundary `≤ ∑ cⱼ + 1`, searchable `< 2^n`).
* `weightedGateCount_cast_eq` — over `ZMod p`, the weighted count's residue is the polynomial value
  `∑_j coeffⱼ · (if gⱼ then 1 else 0)` (the coefficient-duplication identity).

## Honest scope

This closes the `ZMod p`-linear → count-mod-`p` (`SYM`) gap *exactly*: a `ZMod p`-combination of monomial-`AND`s is a
weighted-count `SYM∘AND`.  It does **not** remove the two remaining gaps: RS is *approximate* (the `1-ε` agreement), and
the exact `AC⁰[p] → SYM∘AND` across depth is the open structural wall (`MixedACCDepthReductionSocket`).  A small cell
count is not a uniform algorithm.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0WeightedSymAnd

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver

variable {n m : ℕ}

/-- The **weighted count** of accepting gates: `∑_j cⱼ · [gⱼ accepts]` — the value of the `ℕ`-coefficient polynomial,
equivalently the count over the multiset with gate `j` duplicated `cⱼ` times. -/
def weightedGateCount (c : Fin m → ℕ) (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  ∑ j : Fin m, c j * (if g j x then 1 else 0)

/-- A **symmetric** function of the weighted count (the `SYM` top over the duplicated gate family). -/
def weightedSymEval (c : Fin m → ℕ) (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool)
    (x : Fin n → Bool) : Bool :=
  h (weightedGateCount c g x)

/-- **The weighted count is `≤ ∑ⱼ cⱼ` (proved).** -/
theorem weightedGateCount_le (c : Fin m → ℕ) (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    weightedGateCount c g x ≤ ∑ j : Fin m, c j := by
  unfold weightedGateCount
  exact Finset.sum_le_sum (fun j _ => by split <;> simp)

/-- **The weighted symmetric function is observed by the weighted count (proved).** -/
theorem weightedSym_observed (c : Fin m → ℕ) (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool) :
    ObservedBy (weightedSymEval c g h) (weightedGateCount c g) :=
  ⟨h, fun _ => rfl⟩

/-- **The weighted count statistic has `≤ (∑ⱼ cⱼ) + 1` cells (proved): coefficient duplication, not `2^m`.** -/
theorem weightedSym_count_card_le (c : Fin m → ℕ) (g : Fin m → (Fin n → Bool) → Bool) :
    (Finset.univ.image (weightedGateCount c g)).card ≤ (∑ j : Fin m, c j) + 1 := by
  calc (Finset.univ.image (weightedGateCount c g)).card
      ≤ (Finset.range ((∑ j : Fin m, c j) + 1)).card := by
        apply Finset.card_le_card
        rw [Finset.image_subset_iff]
        intro x _
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (weightedGateCount_le c g x)
    _ = (∑ j : Fin m, c j) + 1 := Finset.card_range _

/-- **A weighted-`SYM` gate over `m` (weighted) gates is SAT-searchable below brute force (proved):
boundary `≤ ∑ⱼ cⱼ + 1`, `< 2^n` once `∑ⱼ cⱼ + 1 < 2^n`.** -/
theorem weightedSym_searchable (c : Fin m → ℕ) (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool)
    (hreg : (∑ j : Fin m, c j) + 1 < 2 ^ n) :
    (Satisfiable (weightedSymEval c g h) ↔
        ∃ k ∈ Finset.univ.image (weightedGateCount c g), h k = true)
      ∧ (Finset.univ.image (weightedGateCount c g)).card < 2 ^ n := by
  refine ⟨observed_sat_iff h (fun _ => rfl), ?_⟩
  exact lt_of_le_of_lt (weightedSym_count_card_le c g) hreg

/-- **Coefficient duplication identity (proved): over `ZMod p`, the weighted count (with `cⱼ = (coeffⱼ).val`) has
residue equal to the polynomial value `∑_j coeffⱼ · monoAND_j`.**  So a `ZMod p`-combination of gates is the
count-mod-`p` `SYM` gate over the duplicated family. -/
theorem weightedGateCount_cast_eq (p : ℕ) [NeZero p] (coeff : Fin m → ZMod p)
    (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    ((weightedGateCount (fun j => (coeff j).val) g x : ℕ) : ZMod p)
      = ∑ j : Fin m, coeff j * (if g j x then (1 : ZMod p) else 0) := by
  unfold weightedGateCount
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.cast_mul, ZMod.natCast_rightInverse (coeff j)]
  cases hg : g j x <;> simp

end PallLean.Paper93.DeepMath.PathB.ACC0WeightedSymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WeightedSymAnd.weightedSym_searchable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WeightedSymAnd.weightedGateCount_cast_eq
