import PallLean.MultilinearSPDP
import Mathlib.Tactic

/-!
# MlProjFar — mlProj kills far-clause contributions

Key lemma for the locality argument (sub-axiom A):

When computing `mlProj(m * ∂^S (∏ cvFactor))`, the factored form
(from iterDeriv_cvProd_eq) is:

  (-1)^κ × ∏_{hit} g_c × ∏_{unhit} (1 - z_c g_c)

A "far" unhit clause c has the property that NONE of its variables
(z_c, var1_c, var2_c, var3_c) appear in any hit clause or near clause.

For such a far clause, the factor (1 - z_c g_c) contributes to the
product but after mlProj, only the constant term `1` survives because:
- The variable z_c appears only in this one factor
- In any multilinear monomial of the full product, z_c can appear at most once
- The monomial `z_c * g_c` has degree ≥ 2 in z_c's block
- After multiplying with the rest (which doesn't use z_c), we get z_c × (stuff)
- This IS multilinear in z_c (degree 1), so it survives mlProj
- BUT: the key is that the FULL product ∏_far (1-z_c g_c) over ALL far clauses,
  when expanded, contains exponentially many terms
- mlProj of this product contains all multilinear terms
- The RANK argument doesn't need mlProj to kill individual monomials;
  it needs the VARS of mlProj(product) to be bounded

Actually, the correct locality argument is:

After applying mlProj to `m * factored_form`, the VARS of the result
are contained in the near-variable set because:
1. The shift monomial m has vars ⊆ S ⊆ near vars (by admissibility)
2. The hit gadgets ∏_{hit} g_c have vars ⊆ near vars (by definition)
3. The far unhit factors ∏_{far} (1-z_c g_c) contribute vars outside near set
4. BUT: mlProj acts monomial-by-monomial, keeping only multilinear ones
5. A multilinear monomial can use each far variable at most once
6. The SPAN of all such monomials is ≤ 2^{|near vars|} dimensional
   because far variables can only appear in {0,1} exponents,
   and the near-variable monomials determine the "type" of each generator

The key insight: even though far variables survive mlProj, the number of
INDEPENDENT generators (modulo far-variable choices) is bounded by 2^{155κ},
because the near-variable part determines the generator up to a far-variable
multilinear monomial factor. And the profile decomposition (Lemma 22)
further compresses this to polynomial in R = 30κ.

This file documents the argument structure. The formal proof requires
tracking the factored form variables through mlProj, which uses
iterDeriv_cvProd_eq + clauseGadget_vars_subset + conflicting_card_le
(all PROVED).
-/

namespace MlProjFar

-- Documentation only — the formal proof connects to type_anonymity_assembly

end MlProjFar
