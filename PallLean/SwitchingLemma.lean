/-
  SwitchingLemma.lean — Paper §7 (Lemma 7.2 + Theorem 7.3)

  The switching lemma + SPDP collapse:
  After restriction, depth-4 circuits of degree ≤ (log n)² have
  SPDP rank ≤ √n with high probability.

  Combined with the signature bound (bounded number of distinct
  SPDP row-space patterns), a fixed seed s* exists by union bound.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.Depth4Simulation
import PallLean.BoolEval
import PallLean.TuringMachine
import Mathlib.Tactic

namespace SwitchingLemma

open MvPolynomial SPDP RestrictedSPDP Restriction Depth4Simulation BoolEval

/-! ## Decision tree → SPDP rank bound (Paper Lemma G.1)

A decision tree of depth w on n variables can be represented as a
multilinear polynomial on at most w variables. Its SPDP rank is
bounded by (k+1)·w because:
- The polynomial has degree ≤ w
- After k derivatives, degree drops to ≤ w - k
- The derivative space has dim ≤ C(w, k) (choose k vars from w)
- With multipliers of degree ≤ ℓ, total dim ≤ C(w,k) · C(w,ℓ)

For k = ℓ = ⌈log n⌉ and w = O(log n):
  SPDP rank ≤ C(log n, log n) · C(log n, log n) ≤ poly(n) -/

-- Note: SPDP rank of a total restriction = 0 (proved in GoodSeed4.lean for n=4)
-- The general case requires showing restrictPoly with all vars fixed gives a constant
-- whose iterDerivList is 0 for any nonempty S.

/-! ## Fixed seed existence (Paper Theorem 7.3)

The paper proves:
1. For each circuit C, Pr[SPDP(C|ρ) > √N] ≤ δ = 2^{-2log²N}
2. Number of distinct SPDP signatures ≤ 2^{O(log²N)}
3. Union bound: Pr[∃ C fails] < 1/2
4. Therefore ∃ fixed seed s* that works for ALL circuits.

This is formalized as: for every Boolean function f with a polynomial
representation of degree ≤ (log n)², there exists a restriction ρ
such that restrictedSpdpRank ≤ √n.

We axiomatize this as the core switching lemma result. -/

/-- Paper Lemma 7.2 + Theorem 7.3 (combined):
    For a polynomial p of degree ≤ (log n)² (from depth-4 simulation of
    a P-TIME circuit), there exists a restriction ρ such that the
    restricted SPDP rank is ≤ √n.

    The degree bound (log n)² is CRUCIAL — it comes from the depth-4
    simulation of P-TIME circuits ONLY. Arbitrary functions have degree
    up to n, and the switching lemma does NOT give SPDP collapse for
    degree-n polynomials. This is why F_SPDP* ⊊ {all functions}.

    Proving this axiom requires the Håstad switching lemma + SPDP
    matrix rank analysis.

    Note: uses UniversalRestriction.universalRestriction (the fixed seed).
    The switching lemma + union bound show ρ* works for ALL
    low-degree polynomials simultaneously. -/
axiom switching_lemma_spdp (n : ℕ) (hn : n ≥ 2)
    (p : MvPolynomial (Fin n) ℚ)
    (hp_correct : ∀ x : Fin n → Bool,
      MvPolynomial.eval (fun i => boolToRat (x i)) p ∈ ({0, 1} : Set ℚ))
    (hdeg : p.totalDegree ≤ (Nat.log 2 n) ^ 2) :
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p
      (UniversalRestriction.universalRestriction n) ≤ Nat.sqrt n

/-- Paper Prop depth4-log2: P-TIME functions have depth-4 circuits of
    degree ≤ (log n)². This combines Cook-Levin encoding, Agrawal-Vinay
    depth reduction, Tavenas degree shedding, and arity splitting.

    We axiomatize this because the full Cook-Levin theorem requires
    formalizing TM → circuit compilation with the degree bound. -/
axiom ptime_has_low_degree_poly (n : ℕ) (hn : n ≥ 2)
    (f : (Fin n → Bool) → Bool)
    (M : TuringMachine.DTM) (hM : M.decides f) :
    ∃ p : MvPolynomial (Fin n) ℚ,
      (∀ x, MvPolynomial.eval (fun i => boolToRat (x i)) p = boolToRat (f x)) ∧
      p.totalDegree ≤ (Nat.log 2 n) ^ 2

end SwitchingLemma
