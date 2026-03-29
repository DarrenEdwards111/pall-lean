import PallLean.MultilinearSPDP
import Mathlib.Tactic

/-!
# ProfilePermutation — Type-anonymity / Profile compression axiom

Paper §9.1 Theorem 23 (Width⇒Rank via profile compression).

This file re-exports MultilinearSPDP.tseitin_spdp_rank_bound under a
paper-faithful name documenting its mathematical content.

The axiom states: for the Tseitin polynomial under matching parameters,
mlBlockedSpdpRank ≤ n^200. This is the paper's Width⇒Rank bound
derived from profile compression (Definition 18-19, Lemmas 20-22, Theorem 23).

## Paper proof route (all arithmetic PROVED, core claim is this axiom):
1. Row decomposition by profiles: RowSpan(M) ⊆ Σ_{h∈H(R)} V_h
2. Profile count: |H(R)| ≤ (30κ+1)^4 (Lemma 20, PROVED)
3. Per-profile dimension: dim(V_h) ≤ (30κ+16)^60 (Lemma 22, PROVED)
4. Subadditivity: dim(Σ V_h) ≤ Σ dim(V_h)
5. Arithmetic: 2^κ × (30κ+1)^4 × (30κ+16)^60 ≤ n^200 (PROVED)

Step 1 (type-anonymity: each generator's rank contribution is determined
by its profile, not by which specific clauses realize it) is the
irreducible mathematical content of this axiom.
-/

namespace ProfilePermutation

open SPDP MultilinearSPDP Tseitin NPWitness

/-- Paper Theorem 23 — Width⇒Rank via profile compression.
    Re-export of MultilinearSPDP.tseitin_spdp_rank_bound with documentation. -/
theorem type_anonymity_rank_bound (n κ : ℕ) (hn : n ≥ 4)
    (hparam : AdmissibleSpdpParams n κ) :
    mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤ n ^ 200 :=
  tseitin_spdp_rank_bound n hn κ hparam

end ProfilePermutation
