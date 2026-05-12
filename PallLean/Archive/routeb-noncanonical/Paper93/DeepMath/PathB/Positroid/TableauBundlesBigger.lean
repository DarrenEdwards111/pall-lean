import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.TableauTraceCoupling
import Mathlib.Tactic.NormNum

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

theorem tableauTraceCoupling_allOnes_5x5 :
    tableauTraceCoupling (SATDeciderTableau.allOnes 5 5) = 25 := by
  rw [tableauTraceCoupling_allOnes]; norm_num

theorem tableauTraceCoupling_allOnes_10x10 :
    tableauTraceCoupling (SATDeciderTableau.allOnes 10 10) = 100 := by
  rw [tableauTraceCoupling_allOnes]; norm_num

theorem tableauTraceCoupling_allOnes_20x20 :
    tableauTraceCoupling (SATDeciderTableau.allOnes 20 20) = 400 := by
  rw [tableauTraceCoupling_allOnes]; norm_num

theorem tableauTraceCoupling_zero_5x5 :
    tableauTraceCoupling (SATDeciderTableau.zero 5 5) = 0 :=
  tableauTraceCoupling_zero 5 5

theorem tableauTraceCoupling_zero_20x20 :
    tableauTraceCoupling (SATDeciderTableau.zero 20 20) = 0 :=
  tableauTraceCoupling_zero 20 20

end PallLean.Paper93.DeepMath.PathB.Positroid
