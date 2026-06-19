import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LazyHierarchyEscape

/-!
# The lazy diagonal, concretely constructed — block bookkeeping, unconditional escape (proved)

Entry 294 proved the lazy diagonal *escapes* the enumeration **given** a block layout (`block`, `len`) and a language
`D` satisfying the lazy structure (copy on the next input, complement at the boundary).  This file **constructs** that
layout concretely — the per-block bookkeeping the lazy-diagonal decider needs — and discharges entry 294's hypotheses,
yielding an **unconditional** escape: a single, explicit `lazyDiagLang enum` that is in no enumerated language's range.

**The block bookkeeping.**  The simplest layout: block `i` is the pair of inputs `{2i, 2i+1}` (`block i = 2i`,
`len i = 1`).  On the copy position `2i` the diagonal copies `enum i` on the next input `2i+1`; on the boundary `2i+1`
it complements `enum i` at the block start `2i`:

```
lazyDiagLang enum n  :=  if n even (n = 2i)  then  enum i (2i+1)       -- copy the next input
                                              else  ¬ enum i (2i)       -- one boundary complement
```

Every input lies in exactly one block at one position, so `lazyDiagLang` is total and the blocks tile `ℕ`.  The two
lazy equations (`hlazy`, `hbdy` of entry 294) are then arithmetic facts about `2i`, `2i+1`, discharged by `omega` — so
`lazy_diag_not_mem_range` applies with no hypotheses left.

## What is proved (clean axioms, no `sorry`)

* **`lazyDiagLang`** — the concrete lazy diagonal with `block i = 2i`, `len i = 1` (copy on even, complement on odd).
* **`lazyDiagLang_escapes`** — **unconditional**: `lazyDiagLang enum ∉ Set.range enum`, for *every* enumeration `enum`
  (entry 294's escape with the block layout discharged).

## Honest scope

This constructs the lazy diagonal's **block bookkeeping** concretely (`block i = 2i`, `len i = 1`) and proves the escape
*unconditionally* — the per-block layout the lazy-diagonal decider machine routes over.  It is the structural skeleton
of the decider: a total language tiling `ℕ` into copy/boundary positions per index, escaping every enumeration.  What
remains is the **decider machine** computing `lazyDiagLang` within the bigger time bound — the copy positions via the
universal simulation (entries 296/297) of `enum i` on the next input, the boundary via the decidable complement (entry
299), clocked (entry 298).  That is physical engineering over this layout, proven-classical, not an open obstruction
(`NEXP ⊄ ACC⁰` is Williams 2011).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonalConstruction

/-- **The concrete lazy diagonal.**  Block `i = {2i, 2i+1}` (`block i = 2i`, `len i = 1`): copy `enum i` on the next
input at the even position `2i`, complement `enum i` at the block start on the odd boundary `2i+1`. -/
def lazyDiagLang (enum : ℕ → (ℕ → Bool)) : ℕ → Bool :=
  fun n => if n % 2 = 0 then enum (n / 2) (n + 1) else ! enum (n / 2) (n - 1)

/-- **The lazy diagonal escapes the enumeration unconditionally (PROVED).**  With the concrete block layout
(`block i = 2i`, `len i = 1`), entry 294's lazy structure holds by arithmetic, so `lazyDiagLang enum ∉ Set.range enum`
for every `enum` — no hypotheses. -/
theorem lazyDiagLang_escapes (enum : ℕ → (ℕ → Bool)) :
    lazyDiagLang enum ∉ Set.range enum := by
  refine ACC0LazyHierarchyEscape.lazy_diag_not_mem_range enum (lazyDiagLang enum)
    (fun i => 2 * i) (fun _ => 1) ?_ ?_
  · -- copy: ∀ i k, k < 1 → lazyDiagLang enum (2i + k) = enum i (2i + k + 1)
    intro i k hk
    interval_cases k
    simp only [lazyDiagLang, Nat.add_zero]
    rw [if_pos (by omega : (2 * i) % 2 = 0), show (2 * i) / 2 = i from by omega]
  · -- boundary: ∀ i, lazyDiagLang enum (2i + 1) = ¬ enum i (2i)
    intro i
    simp only [lazyDiagLang]
    rw [if_neg (by omega : ¬ (2 * i + 1) % 2 = 0), show (2 * i + 1) / 2 = i from by omega,
        show (2 * i + 1) - 1 = 2 * i from by omega]

/-!
**The block bookkeeping, concrete.**  `lazyDiagLang enum` tiles `ℕ` into blocks `{2i, 2i+1}` — copy on the even
position, one boundary complement on the odd — and escapes *every* enumeration unconditionally
(`lazyDiagLang_escapes`).  This is the structural skeleton the lazy-diagonal decider routes over.  The remaining decider
machine (compute `lazyDiagLang` within the bigger bound — copy via universal simulation 296/297, boundary via the
decidable complement 299, clocked 298) is physical engineering over this layout, proven-classical.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonalConstruction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonalConstruction.lazyDiagLang_escapes
