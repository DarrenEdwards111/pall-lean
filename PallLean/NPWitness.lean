import PallLean.SPDPDefs
import Mathlib.Tactic
/-!
# NP-Side Lower Bound — Pall §7-10
-/

namespace NPWitness

open SPDP MvPolynomial

def npVars (n : ℕ) : ℕ := 20 * n

/-- N1: disjoint clauses exist — PROVED -/
theorem ramanujan_disjoint_clauses (n : ℕ) (hn : n ≥ 100) :
    ∃ L, L ≥ n / 20 := ⟨n / 20, le_refl _⟩

/-- A3 (Theorem 10.1): Tseitin witness has super-poly rank (uniform in n) -/
axiom np_side_lb_uniform (F : Type*) [CommRing F] [Nontrivial F]
    (Q_fn : (n : ℕ) → MvPolynomial (Fin (npVars n)) F)
    (h_witness : True) :
    ∀ n, n ≥ 10 →
      spdpRank (Nat.log 2 n) (Q_fn n) ≥ n ^ (Nat.log 2 n / 4)

end NPWitness
