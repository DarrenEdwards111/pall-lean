import PallLean.Paper93.DeepMath.PathB.Positroid.TableauTraceCoupling
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

theorem zero_distinguishes_allOnes_3x3 :
    tableauTraceCoupling (SATDeciderTableau.zero 3 3) ≠
    tableauTraceCoupling (SATDeciderTableau.allOnes 3 3) := by
  rw [tableauTraceCoupling_zero, tableauTraceCoupling_allOnes]
  norm_num

theorem zero_distinguishes_allOnes_4x4 :
    tableauTraceCoupling (SATDeciderTableau.zero 4 4) ≠
    tableauTraceCoupling (SATDeciderTableau.allOnes 4 4) := by
  rw [tableauTraceCoupling_zero, tableauTraceCoupling_allOnes]
  norm_num

theorem allOnes_2x2_lt_allOnes_3x3 :
    tableauTraceCoupling (SATDeciderTableau.allOnes 2 2) <
    tableauTraceCoupling (SATDeciderTableau.allOnes 3 3) := by
  rw [tableauTraceCoupling_allOnes, tableauTraceCoupling_allOnes]
  norm_num

theorem allOnes_5x5_lt_allOnes_6x6 :
    tableauTraceCoupling (SATDeciderTableau.allOnes 5 5) <
    tableauTraceCoupling (SATDeciderTableau.allOnes 6 6) := by
  rw [tableauTraceCoupling_allOnes, tableauTraceCoupling_allOnes]
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
