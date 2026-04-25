import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

theorem contentDrivenAlpha_distinguishes_3x3 :
    contentDrivenAlpha (SATDeciderTableau.zero 3 3) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes 3 3) :=
  contentDrivenAlpha_distinguishes 3 3 (by norm_num)

theorem contentDrivenAlpha_distinguishes_4x4 :
    contentDrivenAlpha (SATDeciderTableau.zero 4 4) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes 4 4) :=
  contentDrivenAlpha_distinguishes 4 4 (by norm_num)

theorem contentDrivenAlpha_distinguishes_5x5 :
    contentDrivenAlpha (SATDeciderTableau.zero 5 5) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes 5 5) :=
  contentDrivenAlpha_distinguishes 5 5 (by norm_num)

theorem contentDrivenAlpha_at_zero_3x3_eq_one :
    contentDrivenAlpha (SATDeciderTableau.zero 3 3) = 1 :=
  contentDrivenAlpha_zero 3 3

theorem contentDrivenAlpha_at_allOnes_3x3_eq_10 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 3 3) = 10 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
