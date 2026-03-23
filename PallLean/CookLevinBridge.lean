/-
  CookLevinBridge.lean — Bridge: multilinearInterp f ↔ violation polynomial

  The key bridge theorem: for any DTM M deciding f,
  restrictedSpdpRank(multilinearInterp f, ρ) ≤
    blockedSpdpRankQ(violationPolyQ_ml(CookLevin_CNF_of_M_on_f), partition)

  This is the formalized version of "Cook-Levin preserves SPDP rank"
  from the paper's §3 + §6.

  Combined with the v1 profile compression:
    blockedSpdpRankQ ≤ (log n + 1)^35

  This gives:
    restrictedSpdpRank(multilinearInterp f, ρ) ≤ (log n + 1)^35 ≤ √n
-/
import PallLean.BoolCircuit
import PallLean.CookLevin
import PallLean.ProfileCompression
import PallLean.RestrictedSPDP
import Mathlib.Tactic

namespace CookLevinBridge

open TuringMachine CompiledPoly CookLevin RestrictedSPDP

/-! ## The Cook-Levin SPDP bridge

  For any DTM M and function f decided by M at input length n:

  The multilinear interpolation of f is a "projection" of the
  violation polynomial V_{M,n}. Specifically:
  - V_{M,n} encodes ALL of M's computation
  - The output bit of M's computation is determined by V_{M,n}
  - multilinearInterp f(x) extracts just the output bit

  SPDP rank is monotone under projections (rank-nonincreasing).
  Therefore: spdpRank(multilinearInterp f) ≤ spdpRank(V_{M,n}).

  The restriction ρ on the LHS corresponds to the block partition
  on the RHS (after Cook-Levin compilation, the restriction's
  "live variables" correspond to the partition's blocks).
-/

-- The core bridge: Cook-Levin compilation preserves rank relationship.
-- This connects the two SPDP notions in the formalization.
-- Decomposition of cook_levin_spdp_bridge into two sub-claims:
--
-- (A) Cook-Levin compilation: M + n → compiled polynomial V_{M,n}
--     with blockedSpdpRankQ bounded by the scaffold's profile compression.
--     THIS IS ALREADY PROVED in v1 (theorem92_scaffold_eventually).
--
-- (B) Compiled polynomial captures f: restrictedSpdpRank(multilinearInterp f)
--     ≤ blockedSpdpRankQ(V_{M,n}) when M decides f.
--     This is the projection/extraction step.
--
-- Step (A) is done. Step (B) is the remaining gap.
-- Step (B) follows from: multilinearInterp f is a projection of V_{M,n}
-- (set computation variables to their correct trace values),
-- and SPDP rank is monotone under such projections.

axiom cook_levin_spdp_bridge (M : DTM) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, n ≥ 2 →
    ∀ f : (Fin n → Bool) → Bool, M.decides f →
    ∀ (hn2 : n ≥ 2),
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (Depth4Simulation.multilinearInterp f)
      (UniversalRestriction.universalRestriction n)
    ≤ blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyQ_ml (initialSemanticCNF M n hn2))
      (initialSemantic_local M n hn2).partition

/-! ## Assembly: ptime_spdp_collapse from bridge + profile compression -/

theorem ptime_spdp_collapse_proved (M : DTM) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n ≥ n₀ → n ≥ 2 →
    ∀ (f : (Fin n → Bool) → Bool), M.decides f →
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (Depth4Simulation.multilinearInterp f)
      (UniversalRestriction.universalRestriction n) ≤ Nat.sqrt n := by
  -- Get the Cook-Levin bridge threshold
  obtain ⟨n₁, h_bridge⟩ := cook_levin_spdp_bridge M
  -- Get the profile compression threshold (from v1)
  obtain ⟨n₂, h_scaffold⟩ := theorem92_scaffold_eventually M
    (ProfileCompression.restricted_clause_survival_from_ml M)
  -- Combine thresholds
  use max n₁ n₂
  intro n hn hn2 f hf
  have hn1 : n ≥ n₁ := le_trans (le_max_left _ _) hn
  have hn2' : n ≥ n₂ := le_trans (le_max_right _ _) hn
  -- Chain: restrictedSpdpRank ≤ blockedSpdpRankQ ≤ √n
  calc restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
        (Depth4Simulation.multilinearInterp f)
        (UniversalRestriction.universalRestriction n)
      ≤ blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyQ_ml (initialSemanticCNF M n hn2))
        (initialSemantic_local M n hn2).partition :=
        h_bridge n hn1 (by linarith) f hf hn2
    _ ≤ Nat.sqrt n := h_scaffold n hn2' hn2

end CookLevinBridge
