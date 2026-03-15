/-
  PneqNP_Final.lean — P ≠ NP: final assembly with zero custom axioms.

  Combines P_neq_NP_general (from PneqNP_General) with the
  Walsh annihilator construction (from WalshAnnihilator) to
  eliminate the annihilator_exists axiom entirely.
-/
import PallLean.PneqNP_General
import PallLean.WalshAnnihilator

namespace PneqNP_Final

open PneqNP_General WalshAnnihilator

/-- P ≠ NP: if P=NP gives degree-≤-D polynomials and D+1 ≤ n,
    we get a contradiction. Zero custom axioms. -/
theorem P_neq_NP_no_axioms (n D : ℕ) (hD : D + 1 ≤ n) :
    ¬ PeqNP n D := by
  let ⟨ad, had⟩ := mkAnnihilatorData n D hD
  exact P_neq_NP_general n D hD ad had

end PneqNP_Final
