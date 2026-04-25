import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget5x5Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget6x6DetConcrete
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

-- α=16: α(α+2)=288, α(α+3)²=5776, α(α+4)³=128000, α(α+5)⁴=3111696, α(α+6)⁵=82458112
theorem compiledGadget_16_2_det : (compiledGadget 16 2).det = 288 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_16_3_det : (compiledGadget 16 3).det = 5776 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_16_4_det : (compiledGadget 16 4).det = 128000 := by
  rw [compiledGadget_4x4_det]; norm_num

theorem compiledGadget_α16_n5_det : (compiledGadget 16 5).det = 16 * 21^4 := by
  rw [compiledGadget_5x5_det]; norm_num

theorem compiledGadget_16_6_det : (compiledGadget 16 6).det = 82458112 := by
  rw [compiledGadget_6x6_det]; norm_num

-- α=17: α(α+2)=323, α(α+3)²=6800, α(α+4)³=157437, α(α+5)⁴=3982352, α(α+6)⁵=109417831
theorem compiledGadget_17_2_det : (compiledGadget 17 2).det = 323 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_17_3_det : (compiledGadget 17 3).det = 6800 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_17_4_det : (compiledGadget 17 4).det = 157437 := by
  rw [compiledGadget_4x4_det]; norm_num

theorem compiledGadget_17_5_det : (compiledGadget 17 5).det = 3982352 := by
  rw [compiledGadget_5x5_det]; norm_num

theorem compiledGadget_17_6_det : (compiledGadget 17 6).det = 109417831 := by
  rw [compiledGadget_6x6_det]; norm_num

-- α=18: α(α+2)=360, α(α+3)²=7938, α(α+4)³=191664, α(α+5)⁴=5037138, α(α+6)⁵=143327232
theorem compiledGadget_18_2_det : (compiledGadget 18 2).det = 360 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_18_3_det : (compiledGadget 18 3).det = 7938 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_18_4_det : (compiledGadget 18 4).det = 191664 := by
  rw [compiledGadget_4x4_det]; norm_num

theorem compiledGadget_18_5_det : (compiledGadget 18 5).det = 5037138 := by
  rw [compiledGadget_5x5_det]; norm_num

theorem compiledGadget_18_6_det : (compiledGadget 18 6).det = 143327232 := by
  rw [compiledGadget_6x6_det]; norm_num

-- α=19: α(α+2)=399, α(α+3)²=9196, α(α+4)³=231173, α(α+5)⁴=6303744, α(α+6)⁵=185546875
theorem compiledGadget_19_2_det : (compiledGadget 19 2).det = 399 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_19_3_det : (compiledGadget 19 3).det = 9196 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_19_4_det : (compiledGadget 19 4).det = 231173 := by
  rw [compiledGadget_4x4_det]; norm_num

theorem compiledGadget_19_5_det : (compiledGadget 19 5).det = 6303744 := by
  rw [compiledGadget_5x5_det]; norm_num

theorem compiledGadget_19_6_det : (compiledGadget 19 6).det = 185546875 := by
  rw [compiledGadget_6x6_det]; norm_num

-- α=20: α(α+2)=440, α(α+3)²=10580, α(α+4)³=276480, α(α+5)⁴=7812500, α(α+6)⁵=237627520
theorem compiledGadget_20_2_det : (compiledGadget 20 2).det = 440 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_20_3_det : (compiledGadget 20 3).det = 10580 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_20_4_det : (compiledGadget 20 4).det = 276480 := by
  rw [compiledGadget_4x4_det]; norm_num

theorem compiledGadget_20_5_det : (compiledGadget 20 5).det = 7812500 := by
  rw [compiledGadget_5x5_det]; norm_num

theorem compiledGadget_20_6_det : (compiledGadget 20 6).det = 237627520 := by
  rw [compiledGadget_6x6_det]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
