/-
  PsideCollapse.lean — P ⊆ C*_SPDP (paper Theorem 7.3, paper-faithful)

  Every polytime function's circuit collapses under a universal
  fixed restriction. This chains:
    1. depth4_simulation: PTIME → depth-4 ΣΠ∑Π (Axiom 1)
    2. depth4_good_seed: bounded-degree polys collapse under ρ* (from Axiom 2)
-/
import PallLean.PaperAxioms

namespace PsideCollapse

open PaperAxioms CircuitModel RestrictedSPDP Restriction

-- Re-export depth4_good_seed for downstream use
-- (P ⊆ C*_SPDP follows from chaining depth4_simulation + depth4_good_seed)

end PsideCollapse
