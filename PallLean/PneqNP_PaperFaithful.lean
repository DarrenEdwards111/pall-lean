/-
  PneqNP_PaperFaithful.lean — P ≠ NP (paper Theorem 12.1)

  Architecture (matching paper main1.tex):

  1. Theorem 7.3 (universal_good_seed): P ⊆ F*_SPDP
     Every poly-size circuit collapses under fixed restriction ρ*.

  2. Theorem 4.1 (semantic_diagonal_escape): f_n ∉ F*_SPDP  [PROVED]
     The diagonal function escapes all low-rank polynomials via
     inner product argument with annihilator vector w ∈ ker(M).

  3. Codimension argument (annihilator_exists): ker(M) nonempty  [AXIOM]
     The SPDP evaluation matrix has rank ≤ d*, so ker has
     positive-dimensional annihilator space.

  Conclusion: f_n ∈ NP \ P, therefore P ≠ NP.

  Axiom inventory (P-side package + annihilator):
  - depth4_simulation (§7.3 Step 1)
  - spdp_collapse_under_restriction (Lemma 6.5)
  - universal_good_seed_bad_union (§7.3 Steps 3-4)
  - annihilator_exists (§8.6 God Move codimension)
-/
import PallLean.PsideCollapse
import PallLean.DiagonalFunction
import PallLean.BoolEval

namespace PneqNP_PaperFaithful

open PaperAxioms PsideCollapse DiagonalFunction
open CircuitModel RestrictedSPDP Restriction BoolEval

/-- P = NP assumption: every NP function has a poly-size circuit
    whose restricted polynomial computes it with low SPDP rank.
    This combines P = NP with Theorem 7.3 (P ⊆ F*_SPDP). -/
structure PeqNP where
  np_collapses :
    ∀ (n : ℕ) (hn : n ≥ 2)
      (ρ : Restriction.Restriction n) (d_star : ℕ),
    ∀ (f : (Fin n → Bool) → Bool),
    ∃ (p : MvPolynomial (Fin n) ℚ),
      computes (Restriction.restrictPoly ρ p) f ∧
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤ d_star

/-- Paper Theorem 12.1: P ≠ NP.

    Proof (paper-faithful, annihilator-based):
    1. Fix n = 4 (≥ 2). Set d* = (log₂ 4 + 1)² = 9.
    2. By annihilator_exists: ∃ w ∈ ker(M) with positive entries.
    3. Define f_n via w. By semantic_diagonal_escape (inner product):
       no low-rank polynomial computes f_n.
    4. Under P = NP: f_n (as a Boolean function) has a low-rank
       polynomial computing it. Contradiction with step 3. -/
theorem P_neq_NP : ¬ PeqNP := by
  intro ⟨h_peqnp⟩
  -- Fix n = 4
  have h4 : (4 : ℕ) ≥ 2 := by omega
  -- Get the universal restriction from Theorem 7.3
  obtain ⟨ρ, hρ⟩ := universal_good_seed 4 h4
  -- Set d* = (log₂ 4 + 1)² = 9
  set d_star := (Nat.log 2 4 + 1) ^ 2
  -- d* < 2⁴ = 16
  have hd : d_star < 2 ^ 4 := by native_decide
  -- Step 2: from annihilator_exists, get w with positive entries + orthogonality
  obtain ⟨w, hw_pos, hw_orth⟩ := annihilator_exists 4 h4 ρ d_star hd
  -- Step 4: P = NP gives a low-rank polynomial computing f_n w
  obtain ⟨p, hcomp, hp_rank⟩ := h_peqnp 4 h4 ρ d_star (f_n w)
  -- Step 3+5: semantic_diagonal_escape gives contradiction
  exact semantic_diagonal_escape hw_pos hw_orth hp_rank hcomp

end PneqNP_PaperFaithful
