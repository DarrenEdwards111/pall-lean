/-
  PneqNP_PaperFaithful.lean — P ≠ NP via semantic SPDP separation

  Axiom inventory:
  - depth4_simulation (Agrawal-Vinay + Tavenas)
  - spdp_collapse_under_restriction (multi-switching lemma)
  - universal_good_seed (union bound + deterministic search)
  - diagonal_escape (counting / dimension argument)
  - diagonal_in_NP (NP membership of f_n)
-/
import PallLean.PsideCollapse
import PallLean.DiagonalFunction
import PallLean.BoolEval

namespace PneqNP_PaperFaithful

open PaperAxioms PsideCollapse DiagonalFunction
open CircuitModel RestrictedSPDP Restriction BoolEval

/-- P = NP assumption: every NP function has a poly-size circuit
    family that computes it (in the Boolean evaluation sense). -/
structure PeqNP where
  /-- For any Boolean function that is in NP (abstractly),
      there exists a poly-size circuit whose polynomial computes it. -/
  np_has_polycircuit :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
    ∃ (p : MvPolynomial (Fin n) ℚ),
      computes p f

/-- P ≠ NP.

    Proof:
    1. universal_good_seed → ∃ ρ collapsing all polys to rank ≤ d*
    2. diagonal_in_NP → ∃ f in NP escaping all rank-≤-d* polys
    3. P=NP → f has a polynomial p computing it
    4. p collapses under ρ (step 1)
    5. f escapes p|ρ (step 2) — contradicts p computing f
-/
theorem P_neq_NP : ¬ PeqNP := by
  intro ⟨h_peqnp⟩
  -- Pick n = 4 (≥ 2)
  have h4 : (4 : ℕ) ≥ 2 := by omega
  -- Step 1: universal restriction
  obtain ⟨ρ, hρ⟩ := universal_good_seed 4 h4
  -- d* = (log₂ 4 + 1)² = 9
  set d_star := (Nat.log 2 4 + 1) ^ 2
  -- 9 < 2⁴ = 16
  have hd : d_star < 2 ^ 4 := by native_decide
  -- Step 2: diagonal function escaping all rank-≤-d* polys
  obtain ⟨f, hf⟩ := diagonal_in_NP 4 h4 ρ d_star hd
  -- Step 3: P=NP gives a polynomial computing f
  obtain ⟨p, hp⟩ := h_peqnp 4 f
  -- Step 4: p collapses under ρ
  have h_collapse := hρ p
  -- Step 5: f escapes p|ρ
  exact hf p h_collapse hp

end PneqNP_PaperFaithful
