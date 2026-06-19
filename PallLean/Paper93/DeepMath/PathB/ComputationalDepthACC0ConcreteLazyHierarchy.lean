import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalNTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RealizationClocking

/-!
# Entry 327 — the concrete nondeterministic time hierarchy, complement-safe, reduced to the routing decider (proved)

Entry 326 reduced the abstract hierarchy residue to placement + diagonalisation, but could not discharge enumerability
(the abstract `NTM` has an arbitrary `Config`).  The *concrete* model fixes that: `ACC0UniversalNTM` proves
`enum_covers` — `cNTIME f ⊆ Set.range (enum f)` — using `TMachine ≃ ℕ`.  This file assembles the **concrete**
nondeterministic time hierarchy on top of it, reducing `¬ (cNTIME f ⊆ cNTIME g)` to exactly **one** genuine residual: a
`TMachine` deciding the diagonal language within the bigger bound `f` (the *routing decider*).

**Complement-safe.**  The existing `cTime_hierarchy` (`…ACC0UniversalNTM`) uses the *Cantor flip* diagonal
(`diag_not_mem_range`); but the flip requires *complementing* an `NTM` computation, which nondeterministic time is not
closed under — so its `diag_in_big` socket is not achievable for a nondeterministic decider.  The honest hierarchy uses
the **complement-safe lazy** diagonal (entry 302, `lazyDiagLang_escapes`): a language that escapes the whole enumeration
without any complement.  This file states the hierarchy against *any* language `D` that escapes `enum g`, so it is
instantiated by the lazy diagonal, not the flip.

## What is proved (clean axioms, no `sorry`)

* **`concrete_lazy_hierarchy`** (PROVED) — for any `D` with `D ∉ Set.range (enum g)` (the complement-safe
  diagonalisation) and `D ∈ cNTIME f` (placement), `¬ (cNTIME f ⊆ cNTIME g)`: composes the proved `enum_covers` with the
  escape.  No complement used.
* **`concrete_lazy_hierarchy_of_decider`** (PROVED) — the same with placement supplied by a *routing decider*: a
  `TMachine M` deciding `D` within `f` (`∀ x, D x ↔ acceptsWithin (toNTM M) x (f |x|)`).  So the concrete hierarchy rests
  on exactly two residues — the complement-safe escape (proved mechanism, entry 302) and the routing decider.
* **`place_of_decider`** (PROVED) — `D ∈ cNTIME f` from a routing decider `TMachine` (the membership packaging).

## Honest scope

This lands the **concrete nondeterministic time hierarchy** on a single genuine residual — the *routing decider*: one
`TMachine` that, on input `x`, runs the lazy-diagonal logic (block layout → universal simulation of `enum`-machines on
the shifted input, clocked, with one boundary complement) within `f(|x|)` steps.  Everything else is discharged:
enumerability (`enum_covers`, via `TMachine ≃ ℕ`, proved in `…ACC0UniversalNTM`), the complement-safe diagonalisation
(entry 302), the clocking and overhead-1 universal simulation (entries 296–298), and the decidable boundary complement
(entry 299).  The routing decider is the genuine remaining construction — the low-level transition-table compilation of
that routing — *not built here and not faked*: it is substantial formalisation engineering, and it is the only thing
between this and a fully formalised concrete hierarchy.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ConcreteLazyHierarchy

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM (cNTIME enum enum_covers)

/-- **Placement from a routing decider (PROVED).**  A `TMachine M` deciding `D` within `f` puts `D ∈ cNTIME f` — the
membership packaging (the definition of `cNTIME`). -/
theorem place_of_decider (f : ℕ → ℕ) (D : Lang) (M : TMachine)
    (hM : ∀ x, D x ↔ acceptsWithin (toNTM M) x (f x.length)) :
    D ∈ cNTIME f :=
  ⟨M, hM⟩

/-- **The concrete nondeterministic time hierarchy, complement-safe (PROVED).**  Any language `D` that *escapes the
enumeration* of `cNTIME g` (`D ∉ Set.range (enum g)` — the complement-safe diagonalisation, no flip) and lies in
`cNTIME f` (placement) witnesses `¬ (cNTIME f ⊆ cNTIME g)`.  Proof: if `cNTIME f ⊆ cNTIME g` then `D ∈ cNTIME g`, so by
the proved `enum_covers` `D ∈ Set.range (enum g)`, contradicting the escape. -/
theorem concrete_lazy_hierarchy (f g : ℕ → ℕ) (D : Lang)
    (hescape : D ∉ Set.range (enum g)) (hplace : D ∈ cNTIME f) :
    ¬ (cNTIME f ⊆ cNTIME g) := by
  intro hsub
  exact hescape (enum_covers g (hsub hplace))

/-- **The concrete hierarchy, reduced to the routing decider (PROVED).**  With the complement-safe escape, the concrete
nondeterministic time hierarchy follows from a single `TMachine` deciding the diagonal `D` within the bigger bound `f` —
the routing decider.  Everything else (enumerability, diagonalisation, clocking, universal simulation, boundary
complement) is already discharged; this is the lone genuine residual. -/
theorem concrete_lazy_hierarchy_of_decider (f g : ℕ → ℕ) (D : Lang)
    (hescape : D ∉ Set.range (enum g))
    (M : TMachine) (hM : ∀ x, D x ↔ acceptsWithin (toNTM M) x (f x.length)) :
    ¬ (cNTIME f ⊆ cNTIME g) :=
  concrete_lazy_hierarchy f g D hescape (place_of_decider f D M hM)

/-- **Enumerability is discharged (re-export, PROVED in `…ACC0UniversalNTM`).**  `cNTIME g ⊆ Set.range (enum g)` via the
machine enumeration `TMachine ≃ ℕ` — the concrete-model fact the abstract `NTM` (entry 326) could not provide. -/
theorem cNTIME_enumerable (g : ℕ → ℕ) : cNTIME g ⊆ Set.range (enum g) := enum_covers g

/-!
**The concrete hierarchy, complement-safe, on one residual.**  `concrete_lazy_hierarchy_of_decider` reduces
`¬ (cNTIME f ⊆ cNTIME g)` to a single `TMachine` deciding the (complement-safe lazy) diagonal within `f` — the routing
decider.  Enumerability is proved (`enum_covers`, `TMachine ≃ ℕ`); the diagonalisation is the proved complement-safe
lazy escape (entry 302), *not* the Cantor flip (unsound for nondeterministic time); clocking, overhead-1 universal
simulation, and the decidable boundary complement are proved (296–299).  The routing decider — the low-level
transition-table compilation of block-layout → clocked universal simulation → one boundary complement — is the lone
genuine remaining construction, substantial formalisation engineering, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ConcreteLazyHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ConcreteLazyHierarchy.place_of_decider
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ConcreteLazyHierarchy.concrete_lazy_hierarchy
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ConcreteLazyHierarchy.concrete_lazy_hierarchy_of_decider
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ConcreteLazyHierarchy.cNTIME_enumerable
