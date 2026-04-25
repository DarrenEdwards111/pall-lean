import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

theorem contentDrivenAlpha_zero_200x200_eq_one :
    contentDrivenAlpha (SATDeciderTableau.zero 200 200) = 1 :=
  contentDrivenAlpha_zero 200 200

theorem contentDrivenAlpha_zero_500x500_eq_one :
    contentDrivenAlpha (SATDeciderTableau.zero 500 500) = 1 :=
  contentDrivenAlpha_zero 500 500

theorem contentDrivenAlpha_zero_1000x1000_eq_one :
    contentDrivenAlpha (SATDeciderTableau.zero 1000 1000) = 1 :=
  contentDrivenAlpha_zero 1000 1000

theorem contentDrivenAlpha_allOnes_200x200 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 200 200) = 40001 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

theorem contentDrivenAlpha_allOnes_500x500 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 500 500) = 250001 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

theorem contentDrivenAlpha_allOnes_1000x1000 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 1000 1000) = 1000001 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

theorem contentDrivenAlpha_distinct_at_500_vs_1000 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 500 500) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes 1000 1000) := by
  rw [contentDrivenAlpha_allOnes_500x500, contentDrivenAlpha_allOnes_1000x1000]
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
