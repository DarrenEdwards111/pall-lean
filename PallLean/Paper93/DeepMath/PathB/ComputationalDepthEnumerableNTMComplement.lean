import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEnumerableNTMCost

/-!
# Enumerable NTM: the boundary complement as a bounded decidable computation

The prior rung bounded the number of configurations reachable in `k` steps by `B^k`.  The acceptance decision `nLang`
searches the reachable configurations at *every* horizon `k ≤ tb x`, so this file bounds its **total** search — and hence
the cost of the lazy diagonaliser's single boundary **complement** `¬nLang`.

  `nComplement` — the boundary complement `¬(machine e accepts x within tb x steps)` — a decidable `Bool`.
  `nComplement_eq_not` — **PROVED**: it is exactly `!(nLang …)` (so it is decidable, by the same bounded search).
  `nLang_search_bound` — **PROVED**: the total number of configurations the decision (hence the complement) examines is
        `∑_{k≤tb x} |reach k| ≤ (tb x + 1)·B^{tb x}` — a search cost of order `B^{tb x}` (times a linear factor).

## Honest scope — the complement is a bounded search, `≈ B^{tb}`

Together with the reachable-count bound, this pins the cost of the lazy diagonaliser's boundary complement: it is a
*decidable* exhaustive search of `≤ (tb x + 1)·B^{tb x}` configurations.  So the complement is deterministically
computable in that time, hence (crudely) realisable inside a nondeterministic clock `g` with `g ≳ B^{f}` — the clock room
that separates `NTIME[f]` from `NTIME[g]`.  What remains for the socket: choosing the concrete padded clock pair `(f, g)`
and assembling the shift (universal simulation, done) with this boundary complement into the diagonaliser machine within
budget `g` — the `≈ Williams' algorithm` universal-machine construction the memory flags.  This file supplies the
complement and its search cost; the machine assembly is the remaining piece.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EnumerableNTM

/-- The lazy diagonaliser's boundary complement: `¬(machine e accepts x within tb x steps)`. -/
def nComplement (nsucc : ℕ → ℕ → List ℕ) (ninit : ℕ → ℕ) (naccept : ℕ → ℕ → Bool) (tb : ℕ → ℕ)
    (e x : ℕ) : Bool := !(nLang nsucc ninit naccept tb e x)

/-- **The complement is `!nLang` (proved)**: hence decidable by the same bounded reachability search. -/
theorem nComplement_eq_not (nsucc : ℕ → ℕ → List ℕ) (ninit : ℕ → ℕ) (naccept : ℕ → ℕ → Bool)
    (tb : ℕ → ℕ) (e x : ℕ) :
    nComplement nsucc ninit naccept tb e x = !(nLang nsucc ninit naccept tb e x) := rfl

/-- **The total search bound (proved)**: with branching `≤ B` (and `B ≥ 1`), the acceptance decision — and hence its
boundary complement — examines at most `(tb x + 1)·B^{tb x}` configurations across all horizons `k ≤ tb x`. -/
theorem nLang_search_bound (nsucc : ℕ → ℕ → List ℕ) (ninit : ℕ → ℕ) (e x B : ℕ)
    (hB : ∀ c, (nsucc e c).length ≤ B) (hB1 : 1 ≤ B) (tb : ℕ → ℕ) :
    (∑ k ∈ Finset.range (tb x + 1), (reach nsucc e (ninit x) k).length)
      ≤ (tb x + 1) * B ^ (tb x) := by
  calc ∑ k ∈ Finset.range (tb x + 1), (reach nsucc e (ninit x) k).length
      ≤ ∑ _k ∈ Finset.range (tb x + 1), B ^ (tb x) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact le_trans (reach_length_le nsucc e B hB (ninit x) k)
          (Nat.pow_le_pow_right hB1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    _ = (tb x + 1) * B ^ (tb x) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.EnumerableNTM

#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.nComplement_eq_not
#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.nLang_search_bound
