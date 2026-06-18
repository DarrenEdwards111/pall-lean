import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LazyDiagonal

/-!
# The lazy diagonal escapes the enumeration — complement-free class escape (proved)

Attacking the single classical gate (the nondeterministic time hierarchy inside Williams' `NEXP ⊄ ACC⁰`), the
diagonalization logic is already decomposed deep: entry 200 proved the **Cantor** escape `diag enum ∉ range enum`, but
with the *naive direct-complement* diagonal `diag enum w := ¬ enum i w` — which is **not** decidable in a
nondeterministic class (no closure under complement).  Entry 219 proved the **lazy** telescoping *contradiction*
(`lazy_diag_false`): a single boundary complement, threaded through a lazy copy-the-next-input chain, forces a
disagreement *without* complementation.  This file supplies the **missing link** between them: the lazy diagonal
*escapes the whole enumeration* — the complement-free analog of entry 200's `diag_not_mem_range`, built directly on the
proved lazy kernel.  This is the form of the escape that genuinely applies to nondeterministic classes.

**The escape.**  Fix an enumeration `enum : ℕ → (ℕ → Bool)` of the smaller class.  For each index `i`, the lazy diagonal
`D` is set up on a block `[block i, block i + len i]` to *lazily copy* `enum i` on the next input
(`D(block i + k) = enum i (block i + k + 1)` for `k < len i`) and complement *only* at the boundary
(`D(block i + len i) = ¬ enum i (block i)`).  Then by `lazy_diag_false`, no `enum i` decides `D`: `D ≠ enum i` for every
`i` (`lazy_diag_escapes_enumeration`), so `D ∉ range enum` (`lazy_diag_not_mem_range`).  Crucially this used only the
*single* boundary complement per block — nondeterministically affordable — so it is the escape the real hierarchy uses.

## What is proved (clean axioms, no `sorry`)

* **`lazy_diag_escapes_enumeration`** — `D ≠ enum i` for every `i`, via the proved lazy kernel `lazy_diag_false`
  (complement-free: only the per-block boundary flip).
* **`lazy_diag_not_mem_range`** — `D ∉ Set.range enum`: the lazy diagonal escapes the *entire* enumeration of the
  smaller class — the complement-free upgrade of entry 200's `diag_not_mem_range`.

## Honest scope

This proves the **complement-free class escape** — the lazy analog of the Cantor escape, the form that applies to
nondeterministic classes — completing the diagonalization-logic side of the nondeterministic time hierarchy: the
*contradiction* (entry 219), the `NEXP`-*placement* (NTIME accounting), and now the *enumeration escape* (here) are all
proved.  What remains is **not** the diagonalization logic but the **realization** primitive: that the lazy diagonal `D`
is actually decidable by a clocked NTM in the *bigger* time bound (the universal simulation of `enum i` on the next
input across the block, plus one boundary complement) — the `ClockedSimulation` / universal-simulation model substrate,
a *proven* classical fact (efficient universal NTM) whose formalization is engineering, not an open obstruction
(`NEXP ⊄ ACC⁰` is a proven theorem, Williams 2011).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LazyHierarchyEscape

open PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonal

/-- **The lazy diagonal differs from every machine in the enumeration (PROVED).**  With `D` set up on each index `i`'s
block to lazily copy `enum i` on the next input and complement only at the boundary, the proved lazy kernel
`lazy_diag_false` gives `D ≠ enum i` for every `i` — using only the *single* boundary complement per block, hence valid
for nondeterministic classes (no closure under complement needed). -/
theorem lazy_diag_escapes_enumeration
    (enum : ℕ → (ℕ → Bool)) (D : ℕ → Bool) (block len : ℕ → ℕ)
    (hlazy : ∀ i k, k < len i → D (block i + k) = enum i (block i + k + 1))
    (hbdy : ∀ i, D (block i + len i) = ! enum i (block i)) :
    ∀ i, D ≠ enum i := by
  intro i heq
  exact lazy_diag_false (enum i) D (block i) (len i)
    (fun x => (congrFun heq x).symm) (hlazy i) (hbdy i)

/-- **The lazy diagonal escapes the whole enumeration (PROVED).**  `D ∉ Set.range enum`: no machine in the enumeration
of the smaller class decides `D`.  This is the complement-free analog of entry 200's Cantor `diag_not_mem_range`, built
on the lazy kernel — the escape that applies to nondeterministic classes. -/
theorem lazy_diag_not_mem_range
    (enum : ℕ → (ℕ → Bool)) (D : ℕ → Bool) (block len : ℕ → ℕ)
    (hlazy : ∀ i k, k < len i → D (block i + k) = enum i (block i + k + 1))
    (hbdy : ∀ i, D (block i + len i) = ! enum i (block i)) :
    D ∉ Set.range enum := by
  rintro ⟨i, hi⟩
  exact lazy_diag_escapes_enumeration enum D block len hlazy hbdy i hi.symm

/-!
**The probe's result.**  Attacking the single classical gate to its core: the nondeterministic time hierarchy's
*diagonalization logic* is now fully proved — the telescoping **contradiction** (`lazy_diag_false`, entry 219), the
`NEXP`-**placement** (NTIME accounting), and the **enumeration escape** (`lazy_diag_not_mem_range`, here, the
complement-free upgrade of entry 200).  The lazy diagonal escapes the entire enumeration of the smaller class using only
one boundary complement per block, so the argument genuinely applies to nondeterministic classes.  What remains is not
diagonalization but the **realization** primitive — a clocked NTM deciding `D` in the bigger time bound via universal
simulation — a *proven* classical fact (efficient universal NTM); and likewise IKW easy-witness and NW guess-verify are
proven classical lemmas.  The gate is the formalization of Williams' **theorem** (2011), decomposed to model-substrate
and classical-lemma atoms, **not** an open obstruction.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0LazyHierarchyEscape

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyHierarchyEscape.lazy_diag_escapes_enumeration
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyHierarchyEscape.lazy_diag_not_mem_range
