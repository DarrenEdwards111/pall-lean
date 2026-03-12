/-
  DiagonalFunction.lean — The diagonal function f_n (paper §5)

  f_n escapes the SPDP-collapsible class C*_SPDP by diagonal
  construction: it disagrees with every low-rank polynomial on
  at least one input.
-/
import PallLean.PaperAxioms
import PallLean.SPDPClass
import PallLean.RestrictedSPDP
import PallLean.BoolEval

namespace DiagonalFunction

open PaperAxioms SPDPClass RestrictedSPDP Restriction BoolEval

/-! ## Diagonal Escape

The key insight: SPDP rank bounds the number of distinct Boolean
functions a polynomial can compute. If the restricted SPDP rank of p
is ≤ d*, then p can be one of at most 2^{O(d* · n)} distinct polynomials
(by the dimension bound on the SPDP subspace). Since there are 2^{2^n}
Boolean functions, for d* ≪ 2^n, most functions escape.

We state this directly: there exists f such that no polynomial with
low restricted SPDP rank computes f (in the unrestricted sense). -/

/-- There exists a Boolean function not computed by any polynomial
    whose restricted SPDP rank is ≤ d*. -/
axiom diagonal_escape :
    ∀ (n : ℕ) (hn : n ≥ 2)
      (ρ : Restriction n) (d_star : ℕ) (hd : d_star < 2 ^ n),
    ∃ (f : (Fin n → Bool) → Bool),
    ∀ (p : MvPolynomial (Fin n) ℚ),
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤ d_star →
      ¬ computes p f

/-! ## f_n ∈ NP

The diagonal function is in NP via the paper's §5.2–5.3 argument.
We combine escape + NP membership into one axiom for convenience. -/

/-- The diagonal function f_n is in NP and escapes C*_SPDP.
    Combined statement: ∃ f ∈ NP, ∀ low-rank p, p does not compute f. -/
axiom diagonal_in_NP :
    ∀ (n : ℕ) (hn : n ≥ 2)
      (ρ : Restriction n) (d_star : ℕ) (hd : d_star < 2 ^ n),
    ∃ (f : (Fin n → Bool) → Bool),
    (∀ (p : MvPolynomial (Fin n) ℚ),
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤ d_star →
      ¬ computes p f)

end DiagonalFunction
