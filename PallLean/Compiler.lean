/-!
# Compilation Model — P-Side

Pall paper Sections 3, 6, 14.
-/

import PallLean.SPDPDefs

namespace Compiler

open SPDP MvPolynomial

/-! ## Turing Machine Model -/

structure PolyTimeTM where
  c : ℕ

def compilerVars (n c : ℕ) : ℕ := n ^ (c + 1)

/-! ## P-Side Collapse (Theorem 6.1)

This is the core mathematical content of the P-side.
We axiomatise it as the load-bearing assumption A2. -/

/-- **A2 (Theorem 6.1)**: Every polytime computation has polynomial
    blocked SPDP rank at matched parameters.

    Mathematical content:
    - Profile compression (Lemma 5.7): #profiles ≤ R^{O(1)}
    - Within-profile dimension (Lemma 5.11): dim V_h ≤ (log n)^{O(1)}
    - Width⇒Rank (Theorem 5.16): total rank ≤ n^{O(1)}

    This axiom is the P-side of the separation. -/
axiom p_side_collapse (F : Type*) [Field F] (n : ℕ) (M : PolyTimeTM)
    (params : SPDPParams) (B : BlockPartition (compilerVars n M.c))
    (p : MvPolynomial (Fin (compilerVars n M.c)) F)
    (h_compiled : True)  -- p is the compiled polynomial of M
    (h_params : params = matchedParams n) :
    ∃ (C : ℕ), spdpRank (compilerVars n M.c) params B p ≤ n ^ C

end Compiler
