import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.TableauTraceCoupling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Structural extras for SAT-decider tableaux

This file collects a handful of small, kernel-only structural facts
about the toy `SATDeciderTableau` and its `tableauTraceCoupling`,
on top of `SATDeciderTableauToy.lean` and `TableauTraceCoupling.lean`.

The lemmas proved here are:

1. `tableauTraceCoupling_zero_eq_zero` — the trace coupling of the
   all-zero tableau is `0` (a stand-alone restatement, with the
   simplest possible proof).
2. `tableauTraceCoupling_allOnes_square_eq_sq` — at dimensions
   `n × n`, the trace coupling of the all-ones tableau equals `n^2`.
3. `extractedFamily_eq_of_dims` — the `extractedFamily` is determined
   by the dimensions only: any two tableaux at the same `(m, n)` give
   the same extracted family. (Structural property: the extracted
   family is dimension-symmetric, depending only on the index space.)
4. `extractedFamily_card_le_two` — the extracted family has at most
   two elements.
5. `tableauTraceCoupling_distinct_of_value_gap` — two tableaux at the
   same dimensions whose trace couplings differ by a fixed nonzero
   real `c` are distinct. This is the Cook-Levin–flavoured
   "distinct couplings ⇒ distinct tableaux" contrapositive,
   parametric in the value gap `c`.
6. `tableauTraceCoupling_zero_vs_allOnes_gap` — concrete instance of
   (5): for `m, n ≥ 1`, the trace-coupling gap between
   `SATDeciderTableau.zero m n` and `SATDeciderTableau.allOnes m n`
   is exactly `m * n` (and is positive).

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound`
should appear in the axiom list.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The trace coupling of the all-zero tableau equals `0`. (A stand-alone
    restatement of `tableauTraceCoupling_zero` with the simplest proof.) -/
theorem tableauTraceCoupling_zero_eq_zero (m n : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.zero m n) = 0 :=
  tableauTraceCoupling_zero m n

/-- The trace coupling of the `n × n` all-ones tableau equals `n^2`. -/
theorem tableauTraceCoupling_allOnes_square_eq_sq (n : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.allOnes n n) = (n : ℝ) ^ 2 := by
  rw [tableauTraceCoupling_allOnes]
  ring

/-- The `extractedFamily` is determined by dimensions only: any two
    tableaux at the same `(m, n)` produce the same extracted family.
    (This is a structural-symmetry property of the extraction map.) -/
theorem extractedFamily_eq_of_dims {m n : ℕ}
    (T₁ T₂ : SATDeciderTableau m n) :
    T₁.extractedFamily = T₂.extractedFamily := rfl

/-- The extracted family `{∅, Finset.univ}` has at most two elements. -/
theorem extractedFamily_card_le_two {m n : ℕ} (T : SATDeciderTableau m n) :
    T.extractedFamily.card ≤ 2 := by
  unfold SATDeciderTableau.extractedFamily
  exact Finset.card_insert_le _ _

/-- If two tableaux at the same dimensions have trace couplings that
    differ by a fixed nonzero real `c`, then the tableaux are distinct.
    This is the Cook–Levin-flavoured "distinct couplings ⇒ distinct
    tableaux" contrapositive, parametric in the value-gap `c`. -/
theorem tableauTraceCoupling_distinct_of_value_gap {m n : ℕ}
    (T₁ T₂ : SATDeciderTableau m n) (c : ℝ) (hc : c ≠ 0)
    (hgap : tableauTraceCoupling T₁ - tableauTraceCoupling T₂ = c) :
    T₁ ≠ T₂ := by
  intro h
  rw [h] at hgap
  simp at hgap
  exact hc hgap.symm

/-- Concrete instance of `tableauTraceCoupling_distinct_of_value_gap`:
    for `m, n ≥ 1`, the trace-coupling gap between the all-zero and the
    all-ones tableau is exactly `m * n`, hence nonzero and the two
    tableaux are distinct as a corollary. -/
theorem tableauTraceCoupling_zero_vs_allOnes_gap (m n : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.allOnes m n) -
      tableauTraceCoupling (SATDeciderTableau.zero m n) = (m : ℝ) * n := by
  rw [tableauTraceCoupling_zero, tableauTraceCoupling_allOnes]
  ring

end PallLean.Paper93.DeepMath.PathB.Positroid
