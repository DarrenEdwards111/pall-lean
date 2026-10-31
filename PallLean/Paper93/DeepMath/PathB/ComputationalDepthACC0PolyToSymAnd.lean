import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymmetricObserver

/-!
# Low-degree polynomial → `SYM ∘ AND`: the next Yao–Beigel–Tarui chip

The YBT normal form is `SYM ∘ AND`.  This file makes the polynomial→`SYM∘AND` step concrete: a degree-`D` multilinear
polynomial with `0/1` coefficients (a sum of distinct monomials) is, on Boolean inputs, exactly the **count of its
accepting monomial-`AND` gates** — so it is `symEval` of those gates (`…ACC0SymmetricObserver`), with at most
`∑_{i≤D} C(n,i)` bottom gates (the number of monomials of degree `≤ D`).

Each monomial `∏_{i∈S} xᵢ` is an `AND` of the bits in `S` (`monoAND`), of fan-in `|S| ≤ D`.  The polynomial value
`∑_S monoAND_S(x)` is `gateCount` over those `AND`s, so any symmetric/threshold function of it (e.g. `= t`, `≠ 0`) is a
`SYM` gate observed by the count — searchable in `≤ m+1` cells (`m` = number of monomials).

## What is proved (clean axioms, no `sorry`)

* `monoAND` — the monomial `AND` gate (`true` iff every bit in `S` is set).
* `lowDegSubsets` / `lowDegSubsets_card` — the degree-`≤D` monomials and their count `∑_{i≤D} C(n,i)`.
* `monomial_count_le` — a family of distinct degree-`≤D` monomials has `≤ ∑_{i≤D} C(n,i)` gates (the bottom-gate bound).
* `lowDegreePoly_searchable` — a `SYM` gate over `m` monomial-`AND`s is SAT-searchable in `< 2^n` once `m+1 < 2^n`.

## Honest scope

This is the polynomial→`SYM∘AND` *cash-out* for a `0/1`-coefficient multilinear polynomial (general `ℕ`/`F_p`
coefficients duplicate each monomial gate, scaling the gate count by the coefficient bound).  It does **not** prove the
hard YBT direction — that an arbitrary `ACC⁰` circuit *is* such a low-degree polynomial / `SYM∘AND` form (that is the
Razborov–Smolensky low-degree-approximation + composition step, the open structural wall, socketed as
`MixedACCDepthReductionSocket`).  And a small cell count is not a uniform algorithm.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver

variable {n m D : ℕ}

/-- The monomial `AND` gate `∏_{i∈S} xᵢ`: accepts iff every bit in `S` is set. -/
def monoAND (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∀ i ∈ S, x i = true)

/-- The degree-`≤D` monomials: all subsets of `Fin n` of cardinality `≤ D`. -/
def lowDegSubsets (n D : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.range (D + 1)).biUnion (fun i => Finset.univ.powersetCard i)

/-- **There are exactly `∑_{i≤D} C(n,i)` degree-`≤D` monomials (proved).** -/
theorem lowDegSubsets_card (n D : ℕ) :
    (lowDegSubsets n D).card = ∑ i ∈ Finset.range (D + 1), n.choose i := by
  have hdisj : (↑(Finset.range (D + 1)) : Set ℕ).PairwiseDisjoint
      (fun i => (Finset.univ : Finset (Fin n)).powersetCard i) := by
    intro i _ i' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro S hS hS'
    rw [Finset.mem_powersetCard] at hS hS'
    exact absurd (hS.2.symm.trans hS'.2) hne
  unfold lowDegSubsets
  rw [Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **A family of distinct degree-`≤D` monomials has at most `∑_{i≤D} C(n,i)` gates (proved).** -/
theorem monomial_count_le (mono : Fin m → Finset (Fin n)) (hinj : Function.Injective mono)
    (hdeg : ∀ j, (mono j).card ≤ D) :
    m ≤ ∑ i ∈ Finset.range (D + 1), n.choose i := by
  rw [← lowDegSubsets_card n D]
  calc m = (Finset.univ.image mono).card := by
            rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ ≤ (lowDegSubsets n D).card := by
        apply Finset.card_le_card
        intro S hS
        rw [Finset.mem_image] at hS
        obtain ⟨j, _, rfl⟩ := hS
        unfold lowDegSubsets
        rw [Finset.mem_biUnion]
        exact ⟨(mono j).card, Finset.mem_range.mpr (Nat.lt_succ_of_le (hdeg j)),
          Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩

/-- **A `SYM` gate over `m` monomial-`AND`s is SAT-searchable below brute force (proved).**  The polynomial value is
`gateCount` over the monomial `AND`s; any symmetric/threshold function `h` of it is searchable in `≤ m+1` cells. -/
theorem lowDegreePoly_searchable (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool) (hreg : m + 1 < 2 ^ n) :
    (Satisfiable (symEval (fun j x => monoAND (mono j) x) h) ↔
        ∃ c ∈ Finset.univ.image (gateCount (fun j x => monoAND (mono j) x)), h c = true)
      ∧ (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card < 2 ^ n :=
  sym_searchable (fun j x => monoAND (mono j) x) h hreg

end PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd.lowDegSubsets_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd.monomial_count_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd.lowDegreePoly_searchable
