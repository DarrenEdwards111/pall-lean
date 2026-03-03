import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace SpdpExtraction

open scoped BigOperators

section
variable {K : Type} [Field K]
variable {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {P : Type}
variable (blockedSpdpSubspace : P → Submodule K W)

noncomputable def blockedSpdpRank (p : P) : Nat :=
  Module.finrank K (blockedSpdpSubspace p)

theorem blockedSpdpRank_mono {p q : P}
    (h : blockedSpdpSubspace p ≤ blockedSpdpSubspace q) :
    blockedSpdpRank blockedSpdpSubspace p ≤
    blockedSpdpRank blockedSpdpSubspace q := by
  simp only [blockedSpdpRank]
  exact Submodule.finrank_mono h

end

/-! ## Extraction pipeline: Theorem 12.2 -/

section Pipeline
variable {K : Type} [Field K]
variable {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {P : Type}
variable (bss : P → Submodule K W)
variable (project restrict relabel gauge : P → P)

theorem extraction_rank_monotone
    (h_project : ∀ p, bss (project p) ≤ bss p)
    (h_restrict : ∀ p, bss (restrict p) ≤ bss p)
    (h_relabel : ∀ p, bss (relabel p) ≤ bss p)
    (h_gauge : ∀ p, bss (gauge p) ≤ bss p)
    (p : P) :
    Module.finrank K (bss (gauge (relabel (restrict (project p))))) ≤
    Module.finrank K (bss p) :=
  le_trans (Submodule.finrank_mono (h_gauge _))
    (le_trans (Submodule.finrank_mono (h_relabel _))
      (le_trans (Submodule.finrank_mono (h_restrict _))
        (Submodule.finrank_mono (h_project _))))

end Pipeline

end SpdpExtraction
