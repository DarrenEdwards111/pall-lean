import Mathlib

/-!
# Lazy diagonalization — the telescoping contradiction (proved), the simulation socketed

Entry 200 proved the Cantor diagonalization kernel (`diag enum ∉ range enum`) but left **`DiagonalInNexp`** (the diagonal
language is `NEXP`-decidable) as a socket, because the naive complement-diagonal `¬ enum i w` is **not** obviously
decidable in a *nondeterministic* class — nondeterministic classes are not known to be closed under complement.  Cook's
**lazy diagonalization** (Cook 1972; Seiferas–Fischer–Meyer; Žák) resolves this: instead of complementing on a single
input, the diagonal **lazily copies** `M_i` on the *next* input across a block of inputs, and complements only **once**,
at the block boundary.  A single complement is nondeterministically affordable, so the lazy diagonal *is* in the bigger
class — yet it still forces a disagreement, via a **telescoping chain**.

The telescoping heart.  Suppose the lazy diagonal `L` on a block `[a, a+len]` satisfies `L(a+k) = M(a+k+1)` for
`k < len` (lazy copy of `M` on the next input) and `L(a+len) = ¬M(a)` (complement at the boundary), and `M` *decides*
`L` (`∀ x, M x = L x`).  Then `M(a) = L(a) = M(a+1) = L(a+1) = ⋯ = M(a+len)` (telescoping through the block) but also
`M(a+len) = L(a+len) = ¬M(a)`, so `M(a) = ¬M(a)` — a contradiction.  This is *why* lazy diagonalization works **without**
closure under complement: the single boundary complement, threaded through the lazy chain, is enough.

## What is proved (clean axioms, no `sorry`)

* **`lazy_telescope`** — the telescoping chain: lazy equalities `M(a+k) = M(a+k+1)` for `k < len` give `M(a) =
  M(a+len)`.
* **`lazy_diag_false`** — the lazy-diagonalization contradiction: if `M` decides a lazy diagonal `L` (lazy copy on the
  block, complement at the boundary), then `False` — so no machine decides its own lazy diagonal.

## Honest scope

This proves the genuine **logical heart of lazy diagonalization** — the telescoping contradiction that forces a
disagreement using only a *single* complement (at the block boundary), the reason the technique works for
*nondeterministic* classes that lack closure under complement — completely, in pure `Bool`/`ℕ` arithmetic.  This is
exactly the NTM-specific subtlety that entry-200's `DiagonalInNexp` socket hid: the *contradiction mechanism* is now
proved.  What remains the socket is the **simulation** — that the lazy diagonal `L` is actually decidable in the bigger
nondeterministic time class `NEXP` (simulate `M_i` on the next input within the block, plus the one boundary complement,
within the time bound).  That simulation is now reduced to the *lazy-feasible* form (one complement, not closure under
complement) — the genuine remaining NTM-cost content.  This proves the lazy contradiction, not the time-bounded
simulation.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonal

/-- **The telescoping chain (PROVED).**  If `M(a+k) = M(a+k+1)` for every `k < len` (the lazy equalities along the
block), then `M(a) = M(a+len)` — the lazy copy threads `M`'s value across the whole block.  Induction on `len`. -/
theorem lazy_telescope (M : ℕ → Bool) (a : ℕ) :
    ∀ len, (∀ k, k < len → M (a + k) = M (a + k + 1)) → M a = M (a + len) := by
  intro len
  induction len with
  | zero => intro _; simp
  | succ m ih =>
      intro hstep
      have h1 : M a = M (a + m) := ih (fun k hk => hstep k (by omega))
      have h2 : M (a + m) = M (a + m + 1) := hstep m (by omega)
      have he : a + (m + 1) = a + m + 1 := by omega
      rw [he, h1, h2]

/-- **The lazy-diagonalization contradiction (PROVED).**  Suppose `M` decides the lazy diagonal `L` (`∀ x, M x = L x`),
where on the block `[a, a+len]` `L` lazily copies `M` on the next input (`L(a+k) = M(a+k+1)` for `k < len`) and
complements at the boundary (`L(a+len) = ¬M(a)`).  Then `False`: the lazy equalities telescope (`lazy_telescope`) to
`M(a) = M(a+len)`, but the boundary gives `M(a+len) = ¬M(a)`, so `M(a) = ¬M(a)`.  *No machine decides its own lazy
diagonal* — and this used only the **single** boundary complement, so it applies to nondeterministic classes without
closure under complement. -/
theorem lazy_diag_false (M L : ℕ → Bool) (a len : ℕ)
    (hdecide : ∀ x, M x = L x)
    (hlazy : ∀ k, k < len → L (a + k) = M (a + k + 1))
    (hbdy : L (a + len) = ! M a) : False := by
  have step : ∀ k, k < len → M (a + k) = M (a + k + 1) := by
    intro k hk; rw [hdecide (a + k), hlazy k hk]
  have htel : M a = M (a + len) := lazy_telescope M a len step
  have hb : M (a + len) = ! M a := by rw [hdecide (a + len), hbdy]
  rw [← htel] at hb
  exact (Bool.not_ne_self (M a)) hb.symm

end PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonal

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonal.lazy_telescope
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonal.lazy_diag_false
