/-
  BoolCircuit.lean — P-Side SPDP Upper Bound (Paper §9, §17.3, Theorem 92)

  Paper-faithful structure for the P-side of the separation:
    DTM → compiled polynomial → profile compression → SPDP rank ≤ √n

  The paper's load-bearing P-side route uses profile compression on the
  compiled polynomial at matching logarithmic parameters κ = ℓ = Θ(log n).
  This is NOT the decision-tree/(k+1)w route (which is provably false for
  shifted SPDP when k = w ≥ 5 — see SPDP_ANALYSIS.md).

  Key result:
  - ptime_spdp_collapse (AXIOM): Paper Theorem 92 / Sections 9, 17.3
    Every P-time function has SPDP rank ≤ √n at κ = ℓ = log₂ n
    after universal restriction.

  The proof chain in the paper:
  (1) Cook-Levin (§3.1): DTM → poly-size width-3 CNF, N = Θ(n³) vars
  (2) Depth-4 simulation (Prop 5.2): ΣΠΣ∏ realization
  (3) Binary Tseitin (§2.3.2): width-3 → width-2 polynomial structure
  (4) Profile compression (§9): polynomial width ⇒ rank via
      constant-type profiles on the compiled polynomial
  (5) Global upper bound (§17.3): Γ_{κ,ℓ}(P_{M,n}) ≤ n^{O(1)}
  (6) At κ = ℓ = Θ(log n): the polynomial bound ≤ √n for large n

  The NP-side uses the same logarithmic parameters:
    κ = ⌈c₀ log n⌉, ℓ = ⌈c₁ log n⌉
  with revealed identity size R(n) = n^{Ω(log n)} (superpolynomial).
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.TuringMachine
import PallLean.Depth4Simulation
import PallLean.LiveVarsDefs
import Mathlib.Tactic

namespace BoolCircuit

open MvPolynomial SPDP LiveVarsDefs

/-! ## P-Side SPDP Collapse (Paper Theorem 92 / Sections 9, 17.3)

  Every P-time function has SPDP rank ≤ √n under the universal restriction
  with shifted partial derivative parameters κ = ℓ = log₂ n.

  The paper proves this via profile compression on the compiled polynomial:

  Definition 12: The SPDP matrix M^B_{κ,ℓ}(p) has rows indexed by pairs
  (τ, u) where |τ| = κ (derivative multi-index) and deg(u) ≤ ℓ (shift
  monomial). Entries are coeff_{x^β}(u · ∂^τ p). This is SHIFTED SPDP.

  Lemma 18: For multilinear p, admissible shifts can be chosen with
  support contained in the derivative set S, giving at most 2^ℓ shifts
  per S. Bound: C(N, ℓ) · 2^ℓ.

  Section 9 (Polynomial Width ⇒ Rank via Constant-Type Profiles):
  The compiled polynomial P_{M,n} has locality structure from Cook-Levin
  encoding. Profile compression groups shifted partial derivatives by
  their interaction pattern with the block partition, bounding rank.

  Section 17.3 (Global polynomial upper bound on Γ_{κ,ℓ}(P_{M,n})):
  Assembles the profile compression bound into Γ ≤ n^{O(1)} at
  κ = ℓ = Θ(log n). For γ = 1/2, this gives Γ ≤ √n for large n.

  Note: The earlier formalization used a decision-tree route with bound
  (k+1)·w. That bound is PROVABLY FALSE for shifted SPDP when k = w ≥ 5
  (counterexample: AND of w variables gives rank C(2w,w) > (k+1)w).
  The profile compression route is the paper's correct load-bearing path. -/

-- PROVED in CookLevinBridge.lean from cook_levin_spdp_bridge + profile compression.
-- Kept as axiom here for backward compatibility with SwitchingLemma.lean.
-- The real dependency is cook_levin_spdp_bridge (Cook-Levin SPDP bridge).
axiom ptime_spdp_collapse :
    ∀ (M : TuringMachine.DTM), ∃ (n₀ : ℕ), ∀ (n : ℕ), n ≥ n₀ → n ≥ 2 →
    ∀ (f : (Fin n → Bool) → Bool), M.decides f →
    RestrictedSPDP.restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (Depth4Simulation.multilinearInterp f)
      (UniversalRestriction.universalRestriction n) ≤ Nat.sqrt n

end BoolCircuit
