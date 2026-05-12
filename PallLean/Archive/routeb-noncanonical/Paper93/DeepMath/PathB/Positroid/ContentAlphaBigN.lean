import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

theorem contentDrivenAlpha_zero_50x50_eq_one :
    contentDrivenAlpha (SATDeciderTableau.zero 50 50) = 1 :=
  contentDrivenAlpha_zero 50 50

theorem contentDrivenAlpha_zero_100x100_eq_one :
    contentDrivenAlpha (SATDeciderTableau.zero 100 100) = 1 :=
  contentDrivenAlpha_zero 100 100

theorem contentDrivenAlpha_allOnes_50x50 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 50 50) = 2501 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

theorem contentDrivenAlpha_allOnes_100x100 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 100 100) = 10001 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

theorem contentDrivenAlpha_allOnes_distinct_at_50_vs_100 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 50 50) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes 100 100) := by
  rw [contentDrivenAlpha_allOnes_50x50, contentDrivenAlpha_allOnes_100x100]
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
