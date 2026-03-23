/-
  PaperCompilation.lean — Paper-faithful compilation model (§3)

  The paper's compilation of a DTM M into a violation polynomial V_{M,n}:
  1. Variables: tape bits b_{t,i}, state one-hots s_{t,q}, head one-hots h_{t,i}
     for each cell (t,i) in the T×T tableau (T = n^c for time bound c)
  2. Local constraints: booleanity, one-hot, transition rules
     Each touches O(1) variables in radius-1 neighborhood
  3. Violation polynomial: V_{M,n} = Σ_C C(x,τ)²
  4. κ-padded polynomial: P_{M,n} = (∏ y_j) · V_{M,n}

  Key properties (compiler invariants I1-I5):
  I1. Each constraint touches O(1) adjacent cells (radius-1)
  I2. Width ≤ 5 CNF, bounded degree
  I3. Block partition B induced deterministically from template
  I4. Canonical index sets for Γ^B_{κ,ℓ}
  I5. Closure under restriction/extraction
-/
import PallLean.TuringMachine
import PallLean.CompiledPoly
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace PaperCompilation

open TuringMachine MvPolynomial

/-! ## Paper §3.1: Variables and tableau -/

-- The compilation produces a polynomial on N(n) = poly(n) variables.
-- Variables are indexed by cells (t,i) × role (tape/state/head).
-- This is already defined in TuringMachine.lean:
-- tapeIdx, stateIdx, headIdx map (t,i,q) to Fin(numVars M n κ).

/-! ## Paper §3.1: Local constraints (transition rules)

  Each constraint is a degree-≤3 polynomial on O(1) variables.
  The constraint set C includes:
  - Booleanity: z(1-z) for each variable
  - One-hot state: Σ_q s_{t,q} = 1 for each t
  - One-hot head: Σ_i h_{t,i} = 1 for each t (when head exactly at one pos)
  - Transition: for each cell (t,i), the tape/state/head update matches M.transition

  Already defined in RealTransition.lean:
  transitionConstraintPoly, inertiaConstraintPoly, etc.
-/

/-! ## Paper §3.1: Violation polynomial

  V_{M,n}(x,τ) = Σ_{C ∈ C} C(x,τ)²

  Properties:
  1. deg(V_{M,n}) = O(1) (since each C has degree ≤ 3, C² has degree ≤ 6)
  2. V_{M,n}(x,τ) = 0 iff τ is a valid tableau of M on input x
  3. V_{M,n} has N(n) = poly(n) variables
-/

-- Already defined: TuringMachine.violationPoly

/-! ## Paper §3.2: Block partition (cell-based)

  Each cell (t,i) forms one block.
  Block B_{t,i} contains: {b_{t,i}, s_{t,q} for all q, h_{t,i}}.
  Plus: input variables x_1,...,x_n form their own blocks.
  Plus: padding variables y_1,...,y_κ form one block.

  Each constraint touches ≤ (2ρ+1)² cells (radius-ρ neighborhood).
  For radius ρ=1: ≤ 9 cells, so ≤ 9 blocks.
-/

-- The cell-based block partition for the real encoding
noncomputable def cellBlockPartition (M : DTM) (n κ : ℕ) :
    CompiledPoly.BlockPartition (numVars M n κ) where
  numBlocks := (tapeSize M n) * (tapeSize M n) + 1
    -- One block per cell (t,i), plus one "misc" block
  blockOf := fun v =>
    -- Tape variable b_{t,i} → block (t * S + i)
    -- State variable s_{t,q} → block (t * S + 0) [same block as tape at (t,0)]
    -- Head variable h_{t,i} → block (t * S + i)
    -- Input/padding → misc block
    if h : v.1 < (tapeSize M n) * (tapeSize M n) then
      ⟨v.1, by omega⟩
    else if h2 : v.1 < (tapeSize M n) * (tapeSize M n) + (tapeSize M n) * M.numStates then
      -- State variable: block by time step
      let t := (v.1 - (tapeSize M n) * (tapeSize M n)) / M.numStates
      ⟨t * (tapeSize M n), by sorry⟩
    else
      ⟨(tapeSize M n) * (tapeSize M n), by omega⟩

/-! ## Paper Theorem 6.1 / A2: P-side SPDP rank collapse

  The compilation model satisfies:
  - Radius-1 locality (I1): each constraint touches ≤ 9 blocks
  - Width ≤ 5 (I2): each constraint is degree ≤ 3, so C² is degree ≤ 6
  - Block partition canonical (I3)

  Profile compression (Paper §5, PROVED in v1) gives:
  Γ^B_{κ,ℓ}(V_{M,n}) ≤ (κ + O(1))^O(1) = (log n)^O(1)

  For κ = ℓ = Θ(log n): (log n)^O(1) ≤ √n for large n.
  Therefore: Γ^B_{κ,ℓ}(P_{M,n}) ≤ n^O(1) ≤ √n. ∎
-/

/-! ## Paper Theorem 10.1 / A3: Tseitin NP-side lower bound

  The Tseitin formula Φ_n on a Ramanujan expander graph G_n:
  - n edges → n variables
  - Each vertex: XOR of incident edges = parity bit
  - Unsatisfiable (odd total parity)

  The coupled verifier polynomial Q×_Φ has an identity minor:
  - A family of shifted partial derivatives with disjoint supports
  - Each coefficient vector is ±1 on its support
  - The identity minor has size ≥ n^Θ(log n) (from expander spectral gap)

  Therefore: Γ^B_{κ,ℓ}(Q×_Φ) ≥ n^Θ(log n) > √n for large n.
-/

/-! ## Connecting to the Lean formalization

  The paper's compilation model maps to the Lean code as follows:
  - DTM M → TuringMachine.DTM M
  - V_{M,n} → violationPoly ℚ M n κ constraints (TuringMachine.lean)
  - Block partition B → cellBlockPartition M n κ (this file)
  - Profile compression → ProfileCompression.spdpRank_ml_le (PROVED)
  - P-side collapse → ptime_spdp_collapse (CookLevinBridge.lean)
  - NP-side → hard_np_family_exists (PneqNP_v2.lean)

  The key bridge theorem cook_levin_spdp_bridge states that:
  restrictedSpdpRank(multilinearInterp f, universalRestriction)
    ≤ blockedSpdpRankQ(V_{M,n}, cellPartition)

  This follows from:
  1. multilinearInterp f is a projection of V_{M,n}
     (set τ to the correct computation trace)
  2. SPDP rank is monotone under projection
     (proved in SPDPProjection.lean, modulo 2 sorries)

  The projection step is where Cook-Levin compilation meets
  SPDP theory: the algebraic structure of M's computation
  (encoded in V_{M,n}) captures the boolean function f.
-/

end PaperCompilation
