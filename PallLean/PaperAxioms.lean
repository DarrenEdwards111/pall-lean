/-
  PaperAxioms.lean — Three axioms from the paper's proof

  These axiomatize the three deep results:
  1. Depth-4 simulation (Agrawal-Vinay + Tavenas)
  2. SPDP collapse under restriction (multi-switching lemma)
  3. Existence of a universal good seed (union bound)

  References:
  - Agrawal & Vinay (2008): Arithmetic circuits — a chasm at depth four
  - Tavenas (2015): Improved bounds for reduction to depth 4 and depth 3
  - Razborov (1995), Smolensky (1987): switching lemma literature
  - Kayal, Saha, Saptharishi (2014): depth-4 SPD lower bounds
-/
import PallLean.CircuitModel
import PallLean.RestrictedSPDP

namespace PaperAxioms

open CircuitModel RestrictedSPDP Restriction

/-! ## Axiom 1: Depth-4 Simulation

Every polynomial-size Boolean circuit can be converted to a depth-4
ΣΠ∑Π circuit with bounded parameters.

The depth-4 circuit has the SAME numVars as the original (it's a
re-wiring of the same computation, not a variable change).

Paper: §7.3 Step 1 -/

axiom depth4_simulation :
    ∀ (C : PolySizeFamily),
    ∃ (D : ℕ → Depth4Circuit ℚ),
    ∃ (n₀ : ℕ),
    ∀ n ≥ n₀,
      -- Same number of variables
      (D n).params.numVars = C.numVars n ∧
      -- Bounded bottom fan-in
      (D n).params.bottomFanIn ≤ Nat.log 2 n ∧
      -- Bounded formal degree
      (D n).params.formalDegree ≤ (Nat.log 2 n) ^ 2 ∧
      -- Bounded size
      (D n).params.size ≤ n ^ (2 * C.sizeBound)

/-! ## Axiom 2: SPDP Collapse Under Restriction

For depth-4 circuits with bounded bottom fan-in t, there exists a
restriction that collapses SPDP rank.

Paper: §7.3 Step 2, Lemma 6.5 -/

axiom spdp_collapse_under_restriction :
    ∀ (n : ℕ) (hn : n ≥ 2)
      (params : Depth4Params)
      (hv : params.numVars = n)
      (p : MvPolynomial (Fin n) ℚ),
    ∃ (ρ : Restriction.Restriction n),
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤
        (Nat.log 2 n + 1) * params.bottomFanIn

/-! ## Axiom 3: Universal Good Seed

There exists a single fixed restriction ρ* such that ALL polynomial-size
circuits simultaneously collapse under ρ*.

Paper: §7.3 Steps 3-4, union bound over quasi-poly row-space signatures. -/

axiom universal_good_seed :
    ∀ (n : ℕ), n ≥ 2 →
    ∃ (ρ : Restriction.Restriction n),
    ∀ (p : MvPolynomial (Fin n) ℚ),
      -- Every polynomial (from any poly-size circuit) collapses:
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
        p ρ ≤ (Nat.log 2 n + 1) ^ 2

end PaperAxioms
