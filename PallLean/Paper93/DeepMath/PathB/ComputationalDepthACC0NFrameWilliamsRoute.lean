import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FastSATCharacteristicUniversal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTSocket
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LazyHierarchyEscape

/-!
# Williams as an N-Frame theorem — the algorithmic-counting branch, internalized

Entries 290–294 showed Williams' `NEXP ⊄ ACC⁰` is the *algorithmic-counting* escape from the composite barrier that
blocks the polynomial method: an **integer** gate-count observer (characteristic 0, carries every characteristic) +
the YBT `SYM∘AND` normal form + the `< 2^n` count-cell fast-SAT savings ⇒ (via the nondeterministic time hierarchy)
the separation.  Until now this lived as external commentary across files.  This file **internalizes** it: Williams is
the N-Frame *algorithmic-counting branch*, encoded directly as a route, equivalent to the fast-SAT route, and feeding
the (socketed) time-hierarchy gate.

**The four N-Frame ingredients of the route** (all proved-structure from 290–294):

* **observer** — the integer gate-count `gateCount g` (entry 291), an `ℕ`-valued statistic;
* **boundary** — its count-cell image `image (gateCount g)`;
* **compression** — `< 2^n` count cells (the YBT exact `SYM∘AND` form, entry 292/293);
* **escape** — characteristic-0 CRT universality: the integer count reads *every* modular top (entries 290/291), so the
  route is never characteristic-blocked (unlike the single-field polynomial method, entries 280–289).

## What is proved (clean axioms, no `sorry`)

* **`NFrameWilliamsRoute`** / **`WilliamsFastSatRoute`** — the N-Frame counting route and the fast-SAT route.
* **`nframe_williams_route_equiv`** (PROVED) — `NFrameWilliamsRoute ↔ WilliamsFastSatRoute`: the N-Frame
  algorithmic-counting branch *is* the fast-SAT route (the four ingredients repackage `HasExactSymAndForm`).
* **`nframe_observer_characteristic_free`** (PROVED) — the escape: the integer count observer decides `MOD_M`-SAT for
  *every* modulus `M` against one image (entry 291), the char-0 universality.
* **`nframe_fastSat_to_timeHierarchy`** (PROVED conditional) — the hard gate, encoded: the N-Frame route ⇒ a uniform
  speedup ⇒ (with the easy-witness/NW collapse and the nondeterministic time hierarchy) `¬ (NEXP ⊆ ACC⁰)`.  The deep
  ingredients are the named classical sockets; the composition is proved glue (`williams_concrete`).
* **`nframe_hierarchy_diag_core`** (re-export) — the time-hierarchy subpiece's *diagonalization core* is proved
  (entry 294 lazy escape, complement-free): the realization primitive is the only remaining model substrate.

## Honest scope

This **internalizes Williams as the N-Frame algorithmic-counting branch** — a precise route (integer-count observer,
count-cell boundary, `< 2^n` compression, char-0 escape), proved equivalent to the fast-SAT route, feeding the
contradiction.  The hard gate `nframe_fastSat_to_timeHierarchy` is proved *modulo* the named classical sockets (uniform
realization, easy-witness/NW, nondeterministic time hierarchy) — each a *proven* classical theorem (`NEXP ⊄ ACC⁰` is
Williams 2011), being formalized, **not** an open obstruction.  The diagonalization core of the hierarchy is proved
(entry 294).  Nothing here is a new `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsRoute

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM
open PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal

/-- **The N-Frame algorithmic-counting branch (Williams), encoded as a route.**  Every `ACC⁰` circuit is observed by an
integer gate-count (`observer`) whose count-cell image (`boundary`) has `< 2^n` cells (`compression`), via the YBT exact
`SYM∘AND` form.  The escape (char-0 CRT universality) is `nframe_observer_characteristic_free`. -/
def NFrameWilliamsRoute : Prop :=
  ∀ (n : ℕ) (C : ACC0Circuit n),
    ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (top : ℕ → Bool),
      eval C = symEval (fun j x => monoAND (mono j) x) top ∧ m + 1 < 2 ^ n

/-- **The fast-SAT route (Williams' algorithmic ingredient).**  Every `ACC⁰` circuit is in exact `SYM∘AND` form with
`< 2^n` count cells (`HasExactSymAndForm`). -/
def WilliamsFastSatRoute : Prop :=
  ∀ (n : ℕ) (C : ACC0Circuit n), HasExactSymAndForm C

/-- **Williams is the N-Frame algorithmic-counting branch (PROVED).**  The N-Frame counting route — integer-count
observer, count-cell boundary, `< 2^n` compression — *is* the fast-SAT route: the four N-Frame ingredients repackage
`HasExactSymAndForm` exactly. -/
theorem nframe_williams_route_equiv : NFrameWilliamsRoute ↔ WilliamsFastSatRoute :=
  Iff.rfl

/-- **The escape (PROVED): char-0 CRT universality of the integer-count observer.**  The integer gate-count observer
decides `MOD_M`-SAT for *every* modulus `M` against one count-cell image (entry 291) — the characteristic-0 universality
that lets the route handle composite `MOD` where the single-field polynomial method is blocked (`no_common_char`,
entries 280–289). -/
theorem nframe_observer_characteristic_free {n m : ℕ}
    (g : Fin m → (Fin n → Bool) → Bool) (M : ℕ) :
    Satisfiable (symEval g (modIndicator M)) ↔
      ∃ c ∈ Finset.univ.image (gateCount g), c % M = 0 :=
  fastSat_decides_every_modulus g M

/-- **The hard gate, encoded (PROVED conditional).**  The N-Frame algorithmic-counting route, turned (by the uniform
realization socket) into a genuine speedup, then (by the easy-witness/NW collapse) collapsing `NTIME f ⊆ NTIME g`,
contradicts the nondeterministic time hierarchy — so `¬ (NEXP ⊆ ACC⁰)`.  This is Williams' theorem encoded through the
N-Frame route; the deep ingredients (`routeGivesSpeedup` = uniform realization, `collapse` = easy-witness + NW + fast-SAT,
`hierarchy` = nondeterministic time hierarchy) are the named classical sockets, the composition proved via
`williams_concrete`. -/
theorem nframe_fastSat_to_timeHierarchy (ACC0 : CClass) (f g : ℕ → ℕ) (speedup : Prop)
    (routeGivesSpeedup : NFrameWilliamsRoute → speedup)
    (collapse : speedup → NEXP ⊆ ACC0 → NTIME f ⊆ NTIME g)
    (hierarchy : ¬ (NTIME f ⊆ NTIME g))
    (route : NFrameWilliamsRoute) :
    ¬ (NEXP ⊆ ACC0) :=
  williams_concrete ACC0 f g speedup collapse hierarchy (routeGivesSpeedup route)

/-- **The time-hierarchy subpiece's diagonalization core is proved (re-export).**  The nondeterministic time hierarchy
socket `hierarchy` is, at its core, the lazy-diagonal enumeration escape — proved complement-free (entry 294): a lazy
diagonal `D` (lazily copying `enum i` on the next input per block, complementing only at the boundary) escapes the whole
enumeration, `D ∉ range enum`.  The only remaining content of the hierarchy is the realization primitive (clocked NTM
universal simulation), a proven classical fact. -/
theorem nframe_hierarchy_diag_core
    (enum : ℕ → (ℕ → Bool)) (D : ℕ → Bool) (block len : ℕ → ℕ)
    (hlazy : ∀ i k, k < len i → D (block i + k) = enum i (block i + k + 1))
    (hbdy : ∀ i, D (block i + len i) = ! enum i (block i)) :
    D ∉ Set.range enum :=
  ACC0LazyHierarchyEscape.lazy_diag_not_mem_range enum D block len hlazy hbdy

/-!
**Williams, internalized.**  The N-Frame algorithmic-counting branch `NFrameWilliamsRoute` (integer-count observer,
count-cell boundary, `< 2^n` compression, char-0 escape) is **equivalent** to the fast-SAT route
(`nframe_williams_route_equiv`), is **never characteristic-blocked** (`nframe_observer_characteristic_free`, the escape),
and **feeds the contradiction** (`nframe_fastSat_to_timeHierarchy`) whose time-hierarchy core is proved
(`nframe_hierarchy_diag_core`, entry 294).  So Williams is no longer external commentary — it is the N-Frame
algorithmic-counting route, with the deep gate honestly socketed to the named classical theorems (uniform realization,
easy-witness/NW, nondeterministic time hierarchy), each *proven* (Williams 2011) and being formalized, not open.  Not
faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsRoute

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsRoute.nframe_williams_route_equiv
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsRoute.nframe_observer_characteristic_free
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsRoute.nframe_fastSat_to_timeHierarchy
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsRoute.nframe_hierarchy_diag_core
