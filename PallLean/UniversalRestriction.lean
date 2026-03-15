/-
  UniversalRestriction.lean — Fixed seed restriction (Paper §5.3, Lemma 5.6)

  The universal restriction ρ* from the fixed seed s* collapses ALL
  polynomial-size circuits simultaneously. Using a SHARED restriction
  is essential — with per-function existential ρ, every function would
  be InFSPDP via total restriction (fixing all variables makes SPDP rank 0).
-/
import PallLean.Restriction

namespace UniversalRestriction

/-- The universal restriction ρ* (Paper Lemma 5.6). -/
axiom universalRestriction (n : ℕ) : Restriction.Restriction n

/-- ρ* leaves at least 1 live variable for n ≥ 2. -/
axiom universalRestriction_nontrivial (n : ℕ) (hn : n ≥ 2) :
    Restriction.numLive (universalRestriction n) ≥ 1

/-- ρ* leaves < n live variables for n ≥ 2. -/
axiom universalRestriction_few_live (n : ℕ) (hn : n ≥ 2) :
    Restriction.numLive (universalRestriction n) < n

end UniversalRestriction
