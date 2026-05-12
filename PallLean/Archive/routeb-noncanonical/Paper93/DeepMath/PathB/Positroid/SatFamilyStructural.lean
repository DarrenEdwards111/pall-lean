import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import Mathlib.Data.Finset.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

/-- satFamily is non-empty for any n. -/
theorem satFamily_nonempty (n : ℕ) : (satFamily n).Nonempty :=
  ⟨∅, satFamily_mem_empty n⟩

/-- satFamily contains exactly two elements when n ≥ 1. -/
theorem satFamily_card_2_general (n : ℕ) (hn : 1 ≤ n) :
    (satFamily n).card = 2 := satFamily_card n hn

/-- satFamily at n=1 has 2 elements. -/
theorem satFamily_n1_card : (satFamily 1).card = 2 := satFamily_card 1 (by decide)

/-- satFamily at n=10 has 2 elements. -/
theorem satFamily_n10_card : (satFamily 10).card = 2 := satFamily_card 10 (by decide)

/-- satFamily at n=100 has 2 elements. -/
theorem satFamily_n100_card : (satFamily 100).card = 2 := satFamily_card 100 (by decide)

end PallLean.Paper93.DeepMath.PathB.Positroid
