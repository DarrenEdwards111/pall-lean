import Mathlib.Tactic

/-!
# Time hierarchy, rung 3: the lazy-diagonalisation core (the nondeterministic lift)

Rungs 1–2 built the *deterministic* diagonalisation on the real RAM machine.  The `NondetTimeHierarchy` socket is
**nondeterministic**, and there the deterministic argument fails: to diagonalise you must complement a machine's answer,
but nondeterministic time classes are **not closed under complement** — negating an `NTIME[t]` computation is not itself
an `NTIME[t]` computation.  The classical fix (Cook 1972; Seiferas–Fischer–Meyer 1978; Žák 1983) is **lazy
diagonalisation**: instead of complementing machine `M_i` at a single input, spread the diagonalisation across a whole
**range** of inputs `[b, b+L]`, using cheap nondeterministic *shifts* and a single expensive *complement* at the range
boundary, amortised by padding.

This file proves the **self-contained mathematical core** of that argument — the *chain collapse* — with no machine
machinery, exactly as rung 1 isolated the deterministic diagonalisation core.

  `lazyDiag a L j` — the lazy diagonal against a machine whose acceptance values are `a`: on input `j < L` it **shifts**
        (`= a (j+1)`, i.e. simulate the machine on the *next* input — a nondeterministic simulation, no complement); on
        the boundary `j = L` it **flips** (`= !(a 0)`, the one complementation).
  `shift_const` — **the lazy collapse (proved)**: the shift forces the machine to be *constant* across the whole range,
        `a 0 = a j` for all `j ≤ L`.  This is why the delay works — the cheap shifts chain the machine's values
        together.
  `lazyDiag_no_fixpoint` — **PROVED**: no machine can agree with its own lazy diagonal on the range.  If `a = lazyDiag a`
        on `[0, L]`, the shift makes `a` constant, so `a 0 = a L`, while the boundary flip gives `a L = !(a 0)` — an
        impossible chain `a 0 = !(a 0)`.
  `lazyDiag_escapes` / `lazyDiag_escapes_range` — **PROVED**: the lazy diagonal differs from the machine at some input of
        the range `[0, L]` (resp. `[b, b+L]`) — it escapes the machine, *without* the diagonaliser ever complementing
        the machine except at the single boundary input.

## Why this is the nondeterministic content

Deterministic diagonalisation needs `d j = !(a j)` at *every* input — one complement per input.  Lazy diagonalisation
needs only the **shift** `d j = a (j+1)` (a plain nondeterministic simulation of the machine on a later input) plus
**one** complement `d L = !(a 0)` at the range end.  The shift is complement-free, so `d` restricted to the range is
computable in nondeterministic time; the single boundary complement is afforded by the range's padding.  `shift_const`
is exactly the lemma that makes those cheap shifts add up to a contradiction — the crux that distinguishes the
nondeterministic hierarchy from the deterministic one.

## Honest scope

This is the combinatorial core of lazy diagonalisation, fully proved.  It is **not** the `NondetTimeHierarchy` socket:
realising `lazyDiag` as an actual nondeterministic machine — the shift as a clocked universal `NTM` simulation of `M_i`
on the next input, the boundary complement within the padded budget, and the range function `f(i) = b`, `f(i+1) = b+L`
chosen so an `NTIME[f]` machine has room to do the boundary complement while an `NTIME[g]` machine does not — is the
machine-level construction that remains (the nondeterministic analogue of rungs 1–2's RAM interpreter).  This lemma
isolates *why* that construction works.  Nothing here is `NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LazyDiagonalization

/-- The **lazy diagonal** against a machine with acceptance values `a`, over the range `[0, L]`: **shift** on the
interior (`j < L` ↦ `a (j+1)`, a complement-free simulation on the next input) and **flip** at the boundary
(`j = L` ↦ `!(a 0)`, the single complementation). -/
def lazyDiag (a : ℕ → Bool) (L : ℕ) (j : ℕ) : Bool := if j < L then a (j + 1) else !(a 0)

/-- **The lazy collapse (proved)**: if a machine agrees with the shift across the range (`a j = a (j+1)` for `j < L`),
its value is *constant* over the whole range — `a 0 = a j` for all `j ≤ L`.  The cheap shifts chain the values
together; this is the mechanism that makes lazy diagonalisation work. -/
theorem shift_const (a : ℕ → Bool) (L : ℕ) (hshift : ∀ j, j < L → a j = a (j + 1)) :
    ∀ j, j ≤ L → a 0 = a j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hjL : j < L := hj
    exact (ih (Nat.le_of_lt hjL)).trans (hshift j hjL)

/-- **No machine decides its own lazy diagonal (proved)**: if `a` agrees with `lazyDiag a L` on all of `[0, L]`, the
shift makes `a` constant (`a 0 = a L`) while the boundary flip gives `a L = !(a 0)` — the impossible chain
`a 0 = !(a 0)`.  This is the lazy-diagonalisation analogue of the deterministic diagonalisation core. -/
theorem lazyDiag_no_fixpoint (a : ℕ → Bool) (L : ℕ)
    (hfix : ∀ j, j ≤ L → a j = lazyDiag a L j) : False := by
  have hshift : ∀ j, j < L → a j = a (j + 1) := by
    intro j hjL
    have h := hfix j (Nat.le_of_lt hjL)
    rwa [lazyDiag, if_pos hjL] at h
  have h0L : a 0 = a L := shift_const a L hshift L (le_refl L)
  have hLflip : a L = !(a 0) := by
    have h := hfix L (le_refl L)
    rwa [lazyDiag, if_neg (lt_irrefl L)] at h
  rw [← h0L] at hLflip
  revert hLflip
  cases a 0 <;> decide

/-- **The lazy diagonal escapes the machine (proved)**: at some input of the range `[0, L]`, the machine's value differs
from its lazy diagonal — established using only shifts and a *single* boundary complement. -/
theorem lazyDiag_escapes (a : ℕ → Bool) (L : ℕ) :
    ∃ j, j ≤ L ∧ a j ≠ lazyDiag a L j := by
  by_contra h
  push_neg at h
  exact lazyDiag_no_fixpoint a L (fun j hj => h j hj)

/-- **The lazy diagonal escapes over a based range (proved)**: over the genuine input range `[b, b+L]` (as in the real
construction's `[f(i), f(i+1))`), the machine differs from the lazy diagonal — shift `a (b+k) ↦ a (b+k+1)` on the
interior, flip `↦ !(a b)` at the boundary — at some input. -/
theorem lazyDiag_escapes_range (a : ℕ → Bool) (b L : ℕ) :
    ∃ k, k ≤ L ∧ a (b + k) ≠ (if k < L then a (b + k + 1) else !(a b)) := by
  obtain ⟨k, hk, hne⟩ := lazyDiag_escapes (fun k => a (b + k)) L
  refine ⟨k, hk, ?_⟩
  simpa [lazyDiag] using hne

end PallLean.Paper93.DeepMath.PathB.LazyDiagonalization

#print axioms PallLean.Paper93.DeepMath.PathB.LazyDiagonalization.shift_const
#print axioms PallLean.Paper93.DeepMath.PathB.LazyDiagonalization.lazyDiag_no_fixpoint
#print axioms PallLean.Paper93.DeepMath.PathB.LazyDiagonalization.lazyDiag_escapes
#print axioms PallLean.Paper93.DeepMath.PathB.LazyDiagonalization.lazyDiag_escapes_range
