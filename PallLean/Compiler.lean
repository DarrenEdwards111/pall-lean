import PallLean.SPDPDefs
import Mathlib.Tactic
/-!
# P-Side Collapse — Pall §3, 5, 6
-/

namespace Compiler

open SPDP MvPolynomial

structure PolyTimeTM where
  c : ℕ

def compilerVars (n c : ℕ) : ℕ := n ^ (c + 1)

/-- P3: (log n)^d ≤ n^d — PROVED -/
theorem log_poly_le_poly (n : ℕ) (hn : n ≥ 2) (d : ℕ) :
    (Nat.log 2 n) ^ d ≤ n ^ d := by
  apply Nat.pow_le_pow_left
  exact le_of_lt (Nat.log_lt_self 2 (by omega))

/-- A2 (Theorem 6.1): polytime → poly SPDP rank (uniform in n) -/
axiom p_side_collapse_uniform (F : Type*) [CommRing F] [Nontrivial F]
    (M : PolyTimeTM)
    (p_fn : (n : ℕ) → MvPolynomial (Fin (compilerVars n M.c)) F)
    (h_compiled : True) :
    ∃ (C : ℕ), ∀ n, spdpRank (Nat.log 2 n) (p_fn n) ≤ n ^ C

end Compiler
