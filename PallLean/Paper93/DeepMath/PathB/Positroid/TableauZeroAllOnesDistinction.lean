import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.TableauTraceCoupling

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

/-- Zero and all-ones tableaus differ in their tableau function: zero gives 0, all-ones gives 1. -/
theorem zero_vs_allOnes_at_specific_entry (m n : ℕ) (i : Fin m) (j : Fin n) :
    (SATDeciderTableau.zero m n).tableau i j = 0 ∧
    (SATDeciderTableau.allOnes m n).tableau i j = 1 := ⟨rfl, rfl⟩

/-- For m ≥ 1 and n ≥ 1, the trace couplings are distinct. -/
theorem trace_couplings_distinct (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    tableauTraceCoupling (SATDeciderTableau.zero m n) ≠
    tableauTraceCoupling (SATDeciderTableau.allOnes m n) := by
  rw [tableauTraceCoupling_zero, tableauTraceCoupling_allOnes]
  have hmn : (1 : ℝ) ≤ (m : ℝ) * n := by
    have hm_cast : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hn_cast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have : (0 : ℝ) ≤ (m : ℝ) := le_trans (by norm_num) hm_cast
    nlinarith
  linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
