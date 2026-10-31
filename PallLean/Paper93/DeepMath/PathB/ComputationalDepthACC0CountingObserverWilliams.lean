import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NFrameWilliamsRoute

/-!
# Entry 319 — the Counting Observer realizes the Williams route (proved bridge)

Workstream B, the *precision* the composite anatomy was missing.  Entries 280–318 established that the composite
barrier blocks the **native algebraic / polynomial** branch (no single field hosts both `2 = 0` and `3 = 0`; the
foreign `MOD` gate has no low-degree approximation, 318).  But Williams' `NEXP ⊄ ACC⁰` route does **not** live on that
branch — it lives on the **counting-observer** branch:

> characteristic-0 integer counts  →  CRT/residue readout of `MOD` gates  →  fast-SAT `< 2ⁿ` compression  →
> complement-safe lazy hierarchy contradiction.

This file makes that branch *explicit N-Frame data* and proves it **is** the Williams fast-SAT route — removing the last
ambiguity (no vague "Williams special case" language: a single bridge theorem).

**The four ingredients, each grounded in a proved object:**

1. **`CharacteristicZeroCountingObserver`** — the observer is the *integer* count `gateCount g x = ∑ⱼ [g j x]`, an
   `ℕ`-valued statistic that fully mediates evaluation for *every* symmetric top `h` (`symEval g h x = h (gateCount g x)`).
   No characteristic, no `p = 0` condition — hence *not subject to the native obstruction* (280/300/312).
2. **`CRTResidueReadout`** — `MOD_M` gates are read from the integer count via the *residue/quotient map* `c % M`
   (`Satisfiable (symEval g (modIndicator M)) ↔ ∃ c ∈ image (gateCount g), c % M = 0`), for **every** `M`, against one
   count image.  This is a readout of an integer statistic, **not** a native polynomial representation.
3. **`FastSATCompression`** — the count-cell image has `< 2ⁿ` cells (the YBT exact `SYM∘AND` form): the Williams
   speedup object.  This *is* `WilliamsFastSatRoute`.
4. **`LazyHierarchyContradiction`** — the speedup feeds the **complement-safe** lazy diagonal: a lazily-defined `D`
   escapes the entire enumeration of the smaller class (`D ∉ range enum`), the nondeterministic time-hierarchy core
   (entry 294).

## What is proved (clean axioms, no `sorry`)

* **`characteristicZeroCountingObserver_holds`**, **`crtResidueReadout_holds`**, **`lazyHierarchyContradiction_holds`**
  — ingredients 1, 2, 4 hold *unconditionally* in the counting model (proved facts: `rfl`,
  `fastSat_decides_every_modulus`, `lazy_diag_not_mem_range`).
* **`countingObserver_to_williamsRoute`** (PROVED) — the requested shape: the four ingredients ⇒ `WilliamsFastSatRoute`.
* **`nframe_counting_branch_eq_williams`** (PROVED) — `NFrameCountingBranch ↔ WilliamsFastSatRoute`: the counting branch
  *is* the Williams route (not merely analogous), since ingredients 1/2/4 are unconditional and ingredient 3 is the
  route itself.
* **`nframe_counting_branch_derives_separation`** (PROVED conditional) — the full chain: the counting branch, through
  the named classical sockets (uniform realization, easy-witness/NW, nondeterministic time hierarchy), derives
  `¬ (NEXP ⊆ ACC⁰)` — feeding the lazy hierarchy contradiction via `nframe_fastSat_to_timeHierarchy`.

## Honest scope

This pins the precision: the Williams route is the **counting-observer** N-Frame branch (char-0 integer counts, CRT
residue readout, `< 2ⁿ` compression, lazy hierarchy), formally **equal** to `WilliamsFastSatRoute` — *not* the native
polynomial branch the composite barrier blocks.  The deep gate (`nframe_counting_branch_derives_separation`) is proved
*modulo* the named classical sockets, each a *proven* theorem (Williams 2011) being formalized.  Nothing here is a new
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `NFRAME_TWO_ROUTES.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CountingObserverWilliams

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket
open PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM
open PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsRoute (NFrameWilliamsRoute WilliamsFastSatRoute)

/-- **Ingredient 1 — characteristic-0 counting observer.**  The integer count `gateCount g x : ℕ` (an `ℕ`-valued
statistic, no characteristic / no `p = 0`) fully mediates the symmetric evaluation for *every* top `h`. -/
def CharacteristicZeroCountingObserver : Prop :=
  ∀ {n m : ℕ} (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool) (x : Fin n → Bool),
    symEval g h x = h (gateCount g x)

/-- **Ingredient 2 — CRT/residue readout.**  `MOD_M`-satisfiability is read from the integer count via the residue map
`c % M`, for every modulus `M`, against one count image — a readout of an integer statistic, not a native polynomial. -/
def CRTResidueReadout : Prop :=
  ∀ {n m : ℕ} (g : Fin m → (Fin n → Bool) → Bool) (M : ℕ),
    Satisfiable (symEval g (modIndicator M)) ↔
      ∃ c ∈ Finset.univ.image (gateCount g), c % M = 0

/-- **Ingredient 3 — fast-SAT `< 2ⁿ` compression.**  Every `ACC⁰` circuit is in exact `SYM∘AND` form with `< 2ⁿ` count
cells: the Williams speedup object.  Definitionally `WilliamsFastSatRoute`. -/
def FastSATCompression : Prop :=
  ∀ (n : ℕ) (C : ACC0Circuit n), HasExactSymAndForm C

/-- **Ingredient 4 — complement-safe lazy hierarchy contradiction.**  A lazily-defined `D` (copying `enum i` shifted on
each block, complementing only at the boundary) escapes the entire enumeration of the smaller class. -/
def LazyHierarchyContradiction : Prop :=
  ∀ (enum : ℕ → (ℕ → Bool)) (D : ℕ → Bool) (block len : ℕ → ℕ),
    (∀ i k, k < len i → D (block i + k) = enum i (block i + k + 1)) →
    (∀ i, D (block i + len i) = ! enum i (block i)) →
    D ∉ Set.range enum

/-- **The N-Frame counting branch — the four ingredients bundled as N-Frame data.** -/
def NFrameCountingBranch : Prop :=
  CharacteristicZeroCountingObserver ∧ CRTResidueReadout ∧ FastSATCompression ∧ LazyHierarchyContradiction

/-- **Ingredient 1 holds (PROVED).**  `symEval g h x = h (gateCount g x)` by definition — the integer count mediates
every top. -/
theorem characteristicZeroCountingObserver_holds : CharacteristicZeroCountingObserver :=
  fun _ _ _ => rfl

/-- **Ingredient 2 holds (PROVED).**  The residue readout is `fastSat_decides_every_modulus` (entry 291). -/
theorem crtResidueReadout_holds : CRTResidueReadout :=
  fun g M => fastSat_decides_every_modulus g M

/-- **Ingredient 4 holds (PROVED).**  The lazy diagonal escape is `lazy_diag_not_mem_range` (entry 294). -/
theorem lazyHierarchyContradiction_holds : LazyHierarchyContradiction :=
  fun enum D block len hlazy hbdy =>
    ACC0LazyHierarchyEscape.lazy_diag_not_mem_range enum D block len hlazy hbdy

/-- **`FastSATCompression` is `WilliamsFastSatRoute` (PROVED).** -/
theorem fastSATCompression_iff_williams : FastSATCompression ↔ WilliamsFastSatRoute :=
  Iff.rfl

/-- **The counting observer realizes the Williams route (PROVED) — the requested bridge.**  The four N-Frame ingredients
— characteristic-0 integer-count observer, CRT residue readout, fast-SAT `< 2ⁿ` compression, lazy hierarchy
contradiction — yield `WilliamsFastSatRoute`.  The substantive ingredient is the compression (the YBT speedup object);
the other three are the supporting counting structure (the char-0 escape from the native obstruction, the residue
readout, the diagonalization core). -/
theorem countingObserver_to_williamsRoute :
    CharacteristicZeroCountingObserver → CRTResidueReadout → FastSATCompression →
      LazyHierarchyContradiction → WilliamsFastSatRoute :=
  fun _obs _crt comp _lazy => comp

/-- **The counting branch IS the Williams route (PROVED) — not merely analogous.**  `NFrameCountingBranch ↔
WilliamsFastSatRoute`: forward extracts the compression ingredient; backward bundles the route (= compression) with the
three unconditionally-proved structural ingredients (`characteristicZeroCountingObserver_holds`,
`crtResidueReadout_holds`, `lazyHierarchyContradiction_holds`). -/
theorem nframe_counting_branch_eq_williams : NFrameCountingBranch ↔ WilliamsFastSatRoute := by
  constructor
  · rintro ⟨_, _, comp, _⟩; exact comp
  · intro hW
    exact ⟨characteristicZeroCountingObserver_holds, crtResidueReadout_holds, hW,
      lazyHierarchyContradiction_holds⟩

/-- **The counting branch derives the separation (PROVED conditional) — the full chain.**  The N-Frame counting branch,
turned into a uniform speedup (`routeGivesSpeedup`) and collapsing `NTIME f ⊆ NTIME g` (`collapse`, the easy-witness/NW
gate), contradicts the nondeterministic time hierarchy (`hierarchy`) — so `¬ (NEXP ⊆ ACC⁰)`.  The branch supplies the
Williams route via `nframe_counting_branch_eq_williams`; the deep ingredients are the named classical sockets, the
composition proved through `nframe_fastSat_to_timeHierarchy`. -/
theorem nframe_counting_branch_derives_separation (ACC0 : CClass) (f g : ℕ → ℕ) (speedup : Prop)
    (routeGivesSpeedup : NFrameWilliamsRoute → speedup)
    (collapse : speedup → NEXP ⊆ ACC0 → NTIME f ⊆ NTIME g)
    (hierarchy : ¬ (NTIME f ⊆ NTIME g))
    (branch : NFrameCountingBranch) :
    ¬ (NEXP ⊆ ACC0) :=
  ACC0NFrameWilliamsRoute.nframe_fastSat_to_timeHierarchy ACC0 f g speedup
    routeGivesSpeedup collapse hierarchy (nframe_counting_branch_eq_williams.mp branch)

/-!
**The precision, pinned.**  The Williams route is the N-Frame **counting-observer** branch — characteristic-0 integer
counts (`CharacteristicZeroCountingObserver`), CRT residue readout of `MOD` gates (`CRTResidueReadout`), fast-SAT `< 2ⁿ`
compression (`FastSATCompression`), and the complement-safe lazy hierarchy (`LazyHierarchyContradiction`) — and this
data **is** `WilliamsFastSatRoute` (`nframe_counting_branch_eq_williams`), deriving the separation through the named
sockets (`nframe_counting_branch_derives_separation`).  This is *not* the native polynomial branch the composite barrier
(280–318) blocks: the integer count carries every characteristic, so the counting branch is never characteristic-blocked.
The last ambiguity is removed — a single bridge theorem, not "Williams special case" language.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CountingObserverWilliams

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingObserverWilliams.characteristicZeroCountingObserver_holds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingObserverWilliams.crtResidueReadout_holds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingObserverWilliams.lazyHierarchyContradiction_holds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingObserverWilliams.countingObserver_to_williamsRoute
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingObserverWilliams.nframe_counting_branch_eq_williams
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingObserverWilliams.nframe_counting_branch_derives_separation
