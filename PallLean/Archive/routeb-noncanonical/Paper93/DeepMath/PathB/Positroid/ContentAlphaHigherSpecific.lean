import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

theorem contentDrivenAlpha_allOnes_5x5_eq_26 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 5 5) = 26 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

theorem contentDrivenAlpha_allOnes_10x10_eq_101 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 10 10) = 101 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

theorem contentDrivenAlpha_allOnes_20x20_eq_401 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 20 20) = 401 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

theorem contentDrivenAlpha_zero_5x5_eq_one :
    contentDrivenAlpha (SATDeciderTableau.zero 5 5) = 1 :=
  contentDrivenAlpha_zero 5 5

theorem contentDrivenAlpha_zero_20x20_eq_one :
    contentDrivenAlpha (SATDeciderTableau.zero 20 20) = 1 :=
  contentDrivenAlpha_zero 20 20

end PallLean.Paper93.DeepMath.PathB.Positroid
