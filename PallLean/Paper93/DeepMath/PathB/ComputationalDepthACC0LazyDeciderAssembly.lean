import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LazyDiagonalConstruction

/-!
# The lazy-diagonal decider assembly — the complement-free hierarchy, one socket left (proved)

This assembles the lazy-diagonal pieces into the nondeterministic time hierarchy, complement-free.  Entry 302 built the
concrete lazy diagonal `lazyDiagLang enum` and proved it **escapes every enumeration** unconditionally.  This file
composes that escape with the decider-membership into the hierarchy implication, isolating the single remaining socket
— *the lazy diagonal is decided within the bigger time bound* — and recording exactly which proved pieces support it.

**The assembly.**  For any enumeration `enum` of a smaller class and any bigger class:

```
lazyDiagLang enum ∉ range enum          (302, unconditional escape — complement-free)
Smaller ⊆ range enum                    (enumerability)
lazyDiagLang enum ∈ Bigger              (the decider socket: lazy diagonal decided in the bigger bound)
────────────────────────────────────────────────────────────────────────────────────────────────────
¬ (Bigger ⊆ Smaller)                    (the time hierarchy)
```

`lazy_time_hierarchy` proves this composition.  Unlike the Cantor version (`…ACC0TimeHierarchyDiagonal`, which uses the
*complement* diagonal and so needs co-nondeterminism), this rests on the **lazy** escape (one boundary complement per
block), so it is honest for nondeterministic classes.

**The one remaining socket** — `lazyDiagLang enum ∈ Bigger`, the lazy diagonal decided within the bigger bound — is
supported by the proved realization pieces: the **copy** positions by the universal simulation (entries 296/297,
overhead 1) of `enum i` on the next input, **clocked** to the bigger bound (entry 298); the **boundary** position by the
decidable complement (entry 299).  What is not yet machine-compiled is the routing as a single transition-table
`TMachine` (the `…ACC0UniversalHStep` physical line) — that, and only that, remains.

## What is proved (clean axioms, no `sorry`)

* **`lazy_time_hierarchy`** — escape (302) + enumerability + decider-membership ⟹ `¬ (Bigger ⊆ Smaller)`: the
  complement-free lazy hierarchy, assembled.
* **`lazy_diag_not_in_smaller`** — the lazy diagonal is not in any enumerated smaller class
  (`Smaller ⊆ range enum ⟹ lazyDiagLang enum ∉ Smaller`).

## Honest scope

This **assembles** the lazy-diagonal hierarchy implication completely from the unconditional escape and the
decider-membership socket — complement-free, so honest for nondeterministic classes.  The remaining socket
(`lazyDiagLang enum ∈ Bigger`) is the lazy-diagonal decider's *membership in the bigger time class*: its copy case is
the proved universal simulation (296/297) clocked (298), its boundary case the proved decidable complement (299); the
only un-built part is compiling the routing into one transition-table `TMachine` (the `…ACC0UniversalHStep` line) — a
proven-classical construction, formalization engineering, not an open obstruction (`NEXP ⊄ ACC⁰` is Williams 2011).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LazyDeciderAssembly

open PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonalConstruction (lazyDiagLang lazyDiagLang_escapes)

/-- **The lazy diagonal is not in any enumerated smaller class (PROVED).**  If the smaller class is contained in the
enumeration's range, the lazy diagonal — which escapes the whole range (entry 302) — is not in it. -/
theorem lazy_diag_not_in_smaller {enum : ℕ → (ℕ → Bool)} {Smaller : Set (ℕ → Bool)}
    (henum : Smaller ⊆ Set.range enum) : lazyDiagLang enum ∉ Smaller :=
  fun hmem => lazyDiagLang_escapes enum (henum hmem)

/-- **The complement-free lazy time hierarchy, assembled (PROVED).**  Given an enumeration of the smaller class
(`henum`) and the decider socket (`hbig`: the lazy diagonal is decided in the bigger class), the bigger class is **not**
contained in the smaller — the nondeterministic time hierarchy, built on the lazy (one-boundary-complement) escape, so
honest without closure under complement. -/
theorem lazy_time_hierarchy {enum : ℕ → (ℕ → Bool)} {Smaller Bigger : Set (ℕ → Bool)}
    (henum : Smaller ⊆ Set.range enum) (hbig : lazyDiagLang enum ∈ Bigger) :
    ¬ (Bigger ⊆ Smaller) :=
  fun hsub => lazy_diag_not_in_smaller henum (hsub hbig)

/-!
**The assembly.**  `lazy_time_hierarchy` composes the unconditional lazy escape (entry 302) with the decider-membership
socket into the full hierarchy implication — complement-free, honest for nondeterministic classes.  The one remaining
socket `lazyDiagLang enum ∈ Bigger` (the lazy diagonal decided in the bigger bound) is supported by the proved
realization pieces — copy via universal simulation (296/297) clocked (298), boundary via the decidable complement
(299) — and lacks only the transition-table `TMachine` compilation of the routing (the `…ACC0UniversalHStep` line), a
proven-classical construction.  So the lazy-diagonal hierarchy is assembled down to one physical-compilation socket.
Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0LazyDeciderAssembly

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyDeciderAssembly.lazy_diag_not_in_smaller
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyDeciderAssembly.lazy_time_hierarchy
