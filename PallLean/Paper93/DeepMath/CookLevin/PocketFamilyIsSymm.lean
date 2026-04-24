import PallLean.Paper93.DeepMath.BridgeB.PocketFamily

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.BridgeB

/-- Re-export: the pocket family is symmetric. -/
theorem pocketFamily_symm_reexport (α : ℝ) (κ n : ℕ) :
    (pocketFamily α κ n).IsSymm :=
  pocketFamily_isSymm α κ n

end PallLean.Paper93.DeepMath.CookLevin
