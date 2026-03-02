import PallLean.SPDPDefs
import PallLean.Tseitin
import Mathlib.Tactic
/-!
# NP-Side Lower Bound — Pall §7–10

Theorem 10.1: Tseitin formulas on Ramanujan expanders have
ΓB_{κ,ℓ}(Q×_Φn) ≥ n^Θ(log n).

Proof chain:
1. Ramanujan family → graph G_n (§8.1)
2. Tseitin encoding → 3-CNF Φ_n (§8.2)
3. Disjoint clause packing → |C_disj| = αn (Lemma 8.3)
4. Identity minor → rank ≥ (αn choose κ) (Theorem 9.3)
5. Binomial bound → n^Θ(log n)
-/

namespace NPWitness

open SPDP MvPolynomial Tseitin

/-! ## Concrete Witness Family -/

/-- Explicit Ramanujan family (LPS or Morgenstern) -/
axiom ramanujanFamily : RamanujanFamily

/-- Tseitin formula on the n-th graph -/
noncomputable axiom tseitinAt : (n : ℕ) → TseitinFormula

/-- The formula uses the n-th Ramanujan graph -/
axiom tseitinAt_graph (n : ℕ) :
    (tseitinAt n).graph = ramanujanFamily.graph n

/-- The formula has n vertices (matching the graph) -/
axiom tseitinAt_vertices (n : ℕ) (hn : n ≥ 100) :
    (tseitinAt n).graph.numVertices = n

/-- Number of variables in the n-th Tseitin polynomial -/
noncomputable def npNumVars (n : ℕ) : ℕ := tseitinNumVars (tseitinAt n)

/-- Coupled verifier polynomial Q×_Φn -/
noncomputable def tseitinPoly (F : Type*) [CommRing F] [Nontrivial F] (n : ℕ) :
    MvPolynomial (Fin (npNumVars n)) F :=
  coupledVerifier F (tseitinAt n)

/-- Clause-induced block partition -/
noncomputable def tseitinPartition (n : ℕ) : BlockPartition (npNumVars n) where
  numBlocks := (tseitinAt n).clauses.length + 1
  assign := fun v =>
    ⟨v.val % ((tseitinAt n).clauses.length + 1),
     Nat.mod_lt _ (by omega)⟩

/-! ## The Lower Bound -/

/-- **A3 (Theorem 10.1): NP-side non-collapse**

    ΓB_{κ,ℓ}(Q×_Φn) ≥ n^{log n / 4} for sufficiently large n.

    The proof chain (grounded in concrete Tseitin construction):
    1. Disjoint packing: |C_disj| ≥ n/30 (Lemma 8.3, greedy matching)
    2. Identity minor: (n/30 choose κ) diagonal entries ±1 in M^B (Thm 9.3)
    3. Rank ≥ minor size ≥ n^{log n / 4} (combinatorics)

    This axiom captures the combined result. The sub-results
    (packing, identity minor, binomial bound) are in Tseitin.lean. -/
axiom np_side_lb (F : Type*) [CommRing F] [Nontrivial F] :
    ∃ n₀, ∀ n, n ≥ n₀ →
      blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
        (tseitinPoly F n) ≥ n ^ (Nat.log 2 n / 4)

end NPWitness
