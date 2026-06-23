import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearisation

/-!
# The full `MOD`/`AND`/`OR` tower is sparse: `(n+1)^{K^depth}` monomial-`AND` sets (PROVED)

The cash-out's `SYM∘AND` **width** piece.  (Honest correction: the Toda representation `frep`/`vrep` is a
*large* integer — only its residue mod `p^{2^k}` is the Boolean value, cf. `full_tower_extract`.  So the
cash-out is **not** "the integer value is small"; it is the **`SYM∘AND` structure**: a *symmetric* readout
of *few* `AND` monomials.)  The width — the number of distinct monomial supports (= `AND` gates) — is
quasipolynomial:

  `full_tower_sparse` — `((frep p k t).support.image (·.support)).card ≤ (n+1)^(K^(fdepth t))`,
  `K = max(w, 3^k(p−1))`.

This is the third `SYM∘AND` ingredient, joining the **degree** (`frep_totalDegree_le`: `≤ K^depth`) and
the **value** (`full_tower`/`full_tower_extract`/`vval_mem_bool`: exact Boolean over `ZMod (p^{2^k})`).  So
the full tower's polynomial is a degree-`K^depth`, `(n+1)^{K^depth}`-sparse polynomial over `ZMod (p^{2^k})`
whose value is the circuit's exact Boolean output — quasipoly for `w, 3^k(p−1) = polylog`, constant depth.

## What is proved (clean axioms, no `sorry`)

* `full_tower_sparse` — the `(n+1)^{K^depth}` monomial-set bound (reusing `beigelTarui_monomial_count_le`
  and `support_mem_lowDeg`).

## Honest scope

The `SYM∘AND` width of the full tower's polynomial.  The remaining cash-out: the `2^k`-vs-global-count
choice (making the `ZMod (p^{2^k})` readout the exact Boolean output of the *whole* circuit) and the
`NEXP ⊄ ACC⁰` contradiction.  Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSparse

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerDegree (FTower frep fdepth FBounded frep_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity (beigelTarui_monomial_count_le)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (support_mem_lowDeg)

/-- **Full-tower `SYM∘AND` width (proved): `(n+1)^{K^depth}` distinct monomial-`AND` sets.**  The full
`MOD`/`AND`/`OR` tower's polynomial uses at most `(n+1)^(K^(fdepth t))` monomial supports —
quasipolynomial for `K = max(w, 3^k(p−1)) = polylog` and constant depth. -/
theorem full_tower_sparse (p k w n : ℕ) (hpos : 1 ≤ max w (3 ^ k * (p - 1)))
    (t : FTower (Fin n)) (h : FBounded w t) :
    ((frep p k t).support.image (fun d => d.support)).card
      ≤ (n + 1) ^ ((max w (3 ^ k * (p - 1))) ^ fdepth t) := by
  have hdeg : (frep p k t).totalDegree ≤ (max w (3 ^ k * (p - 1))) ^ fdepth t :=
    frep_totalDegree_le p k w hpos t h
  refine le_trans (Finset.card_le_card ?_) (beigelTarui_monomial_count_le n _)
  intro S hS
  rw [Finset.mem_image] at hS
  obtain ⟨d, hd, rfl⟩ := hS
  exact support_mem_lowDeg (frep p k t) hdeg hd

/-!
**Full-tower sparsity proved.**  `(n+1)^{K^depth}` distinct monomial-`AND` sets — the `SYM∘AND` width,
quasipoly for polylog `K` and constant depth.  With the degree (`frep_totalDegree_le`) and value
(`full_tower`/`full_tower_extract`/`vval_mem_bool`) bounds, the full tower is a low-degree, sparse, exact
`SYM∘AND` over `ZMod (p^{2^k})`.  The `2^k`-vs-count choice and the `NEXP ⊄ ACC⁰` contradiction remain.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSparse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSparse.full_tower_sparse
