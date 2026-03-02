import Mathlib.Tactic
/-!
# Linear Algebra Facts for Extraction
-/

namespace RankFacts

theorem extraction_stages_compose
    (r₁ r₂ r₃ r₄ r₅ : ℕ)
    (h1 : r₂ ≤ r₁) (h2 : r₃ ≤ r₂) (h3 : r₄ ≤ r₃)
    (h4 : r₅ = r₄) : r₅ ≤ r₁ := by omega

end RankFacts
