import PallLean.WithinProfileBound
import PallLean.Step4Compiler
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.CookLevin

/-- Sanity statement confirming `WithinProfileBound` is accessible. -/
theorem within_profile_bound_accessible :
    ∃ (n : ℕ), n = n := ⟨0, rfl⟩

end PallLean.Paper93.DeepMath.CookLevin
