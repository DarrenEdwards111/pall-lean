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

/-- Binomial lower bound: (n/30 choose log₂ n) ≥ n^{log₂ n / 4} for large n.

    Proof: (L choose k) ≥ (L/k)^k. With L = n/30, k = log₂ n:
    (n/(30·log n))^{log n} ≥ n^{log n / 4} for large enough n
    (since n/(30·log n) ≥ n^{1/4} eventually). -/
theorem binomial_lower_bound :
    ∃ n₀, ∀ n, n ≥ n₀ →
      Nat.choose (n / 30) (Nat.log 2 n) ≥ n ^ (Nat.log 2 n / 4) := by
  -- Standard combinatorial bound; (L choose k) ≥ (L/k)^k
  -- For L = n/30, k = log n: (n/(30 log n))^{log n} grows as n^{Θ(log n)}
  sorry

/-- **Theorem 10.1**: NP-side non-collapse.
    Proved from identity_minor_lower_bound + disjoint_packing + binomial bound. -/
theorem np_side_lb (F : Type*) [CommRing F] [Nontrivial F] :
    ∃ n₀, ∀ n, n ≥ n₀ →
      blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
        (tseitinPoly F n) ≥ n ^ (Nat.log 2 n / 4) := by
  obtain ⟨n₀, hn₀⟩ := binomial_lower_bound
  -- Need n large enough that log₂ n ≤ n/30 (holds for n ≥ 2^10 = 1024)
  use max n₀ (2^10)
  intro n hn
  have hn₀' : n ≥ n₀ := le_trans (le_max_left _ _) hn
  have hn1024 : n ≥ 2^10 := le_trans (le_max_right _ _) hn
  have hn100 : n ≥ 100 := by omega
  -- Step 1: Get disjoint packing of size ≥ n/30
  have hv := tseitinAt_vertices n hn100
  have pack := Tseitin.disjoint_packing_exists (tseitinAt n) (by omega)
  -- Step 2: Identity minor gives rank ≥ (pack.selected.length choose κ)
  have h_minor := identity_minor_lower_bound F (tseitinAt n)
    (tseitinPartition n) pack (Nat.log 2 n) (Nat.log 2 n)
    (by -- κ = log₂ n ≤ n/30 ≤ pack.selected.length for n ≥ 1024
        have hps := pack.size_bound; rw [hv] at hps
        -- log₂ n ≤ n/30 for n ≥ 1024: since 30 * log₂ n ≤ n
        -- (30k ≤ 2^k for k ≥ 8, and log₂ n ≤ k when n ≤ 2^k)
        sorry)
  -- Step 3: pack.selected.length ≥ n/30, so choose ≥ (n/30 choose κ) ≥ n^{κ/4}
  -- tseitinPoly F n = coupledVerifier F (tseitinAt n), so types match
  calc blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly F n)
      ≥ Nat.choose pack.selected.length (Nat.log 2 n) := h_minor
    _ ≥ Nat.choose (n / 30) (Nat.log 2 n) := by
        apply Nat.choose_le_choose
        have := pack.size_bound
        rw [hv] at this
        exact this
    _ ≥ n ^ (Nat.log 2 n / 4) := hn₀ n hn₀'

end NPWitness
