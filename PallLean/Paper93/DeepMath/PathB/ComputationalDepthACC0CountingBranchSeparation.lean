import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CountingObserverWilliams

/-!
# Entry 320 — the counting branch separation, packaged with all residues explicit (proved)

Entry 319 proved the counting-observer branch *is* the Williams route (`nframe_counting_branch_eq_williams`) and gave
the chain to `¬ (NEXP ⊆ ACC⁰)` with the three classical sockets as loose hypotheses
(`nframe_counting_branch_derives_separation`).  This file **packages the whole route into one clean theorem**:

```
nframe_counting_branch_to_williams_separation :
  WilliamsClassicalResidues ACC0 f g speedup →
  NFrameCountingBranch →
  ¬ (NEXP ⊆ ACC0)
```

with the entire residue surface bundled into a single, self-documenting hypothesis `WilliamsClassicalResidues`.  Nothing
is hidden: the only inputs beyond the N-Frame counting branch are the three named classical theorems (each *proven* —
Williams 2011 — being formalized), and they are named, one field each.

**The residue surface (exactly three, all proven classical theorems).**

* `uniformRealization : NFrameWilliamsRoute → speedup` — the uniform realization theorem (the `< 2ⁿ` count-cell fast-SAT
  turned into a genuine uniform `NTIME` speedup).  Ground down to primitive TM ops across entries 304–311.
* `easyWitnessNWCollapse : speedup → NEXP ⊆ ACC0 → NTIME f ⊆ NTIME g` — the easy-witness / NW collapse (`IKW` +
  Karp–Lipton + NW-derandomisation), assembled to named residues across entries 307/313/314/315/316.
* `nondetTimeHierarchy : ¬ (NTIME f ⊆ NTIME g)` — the nondeterministic time hierarchy, whose diagonalization core is
  proved complement-free (entry 294, `lazy_diag_not_mem_range`); only the realization primitive remains.

## What is proved (clean axioms, no `sorry`)

* **`WilliamsClassicalResidues`** — the three named classical sockets bundled as one `Prop` structure.
* **`nframe_counting_branch_to_williams_separation`** (PROVED) — `WilliamsClassicalResidues … → NFrameCountingBranch →
  ¬ (NEXP ⊆ ACC0)`: the complete Williams/N-Frame route in one theorem, residues fully explicit.
* **`williams_separation_from_residues`** (PROVED) — the same with the branch supplied by
  `nframe_counting_branch_eq_williams` from any `WilliamsFastSatRoute`, exhibiting the route ⇒ separation form directly.

## Honest scope

This is a *packaging* entry: it consolidates the proved counting-branch ⇒ separation chain into a single theorem with the
residue surface made completely explicit (one structure, three named fields), so the Williams/N-Frame route is as clean
as it can be *without proving new lower bounds*.  The three residues are *proven* classical theorems (Williams 2011)
being formalized — `nframe_counting_branch_to_williams_separation` does **not** prove them, it names them.  This is
**not** a new `NEXP ⊄ ACC⁰`, and emphatically **not** `P ≠ NP` (which remains beyond both the Williams route and the
composite barrier).  See `NFRAME_TWO_ROUTES.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CountingBranchSeparation

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM
open PallLean.Paper93.DeepMath.PathB.ACC0NFrameWilliamsRoute (NFrameWilliamsRoute WilliamsFastSatRoute)
open PallLean.Paper93.DeepMath.PathB.ACC0CountingObserverWilliams
  (NFrameCountingBranch nframe_counting_branch_eq_williams nframe_counting_branch_derives_separation)

/-- **The Williams classical residue surface, bundled (the entire non-N-Frame input).**  Exactly the three named
classical theorems the counting-branch separation rests on — each *proven* (Williams 2011), being formalized.  Bundling
them makes the residue surface a single, inspectable hypothesis. -/
structure WilliamsClassicalResidues (ACC0 : CClass) (f g : ℕ → ℕ) (speedup : Prop) : Prop where
  /-- The uniform realization theorem: the `< 2ⁿ` count-cell fast-SAT becomes a genuine uniform speedup (entries
  304–311, ground down to primitive TM ops). -/
  uniformRealization : NFrameWilliamsRoute → speedup
  /-- The easy-witness / NW collapse: a speedup collapses `NTIME f ⊆ NTIME g` under `NEXP ⊆ ACC0` (IKW + Karp–Lipton +
  NW-derandomisation, entries 307/313/314/315/316). -/
  easyWitnessNWCollapse : speedup → NEXP ⊆ ACC0 → NTIME f ⊆ NTIME g
  /-- The nondeterministic time hierarchy (diagonalization core proved complement-free, entry 294). -/
  nondetTimeHierarchy : ¬ (NTIME f ⊆ NTIME g)

/-- **The packaged counting-branch separation (PROVED).**  The complete Williams/N-Frame route in one theorem: given the
bundled classical residues, the N-Frame counting branch yields `¬ (NEXP ⊆ ACC0)`.  All assumptions are explicit — the
N-Frame counting branch (proved equal to the Williams fast-SAT route, entry 319) plus the single residue bundle naming
the three proven classical theorems. -/
theorem nframe_counting_branch_to_williams_separation
    (ACC0 : CClass) (f g : ℕ → ℕ) (speedup : Prop)
    (residues : WilliamsClassicalResidues ACC0 f g speedup) :
    NFrameCountingBranch → ¬ (NEXP ⊆ ACC0) :=
  fun branch =>
    nframe_counting_branch_derives_separation ACC0 f g speedup
      residues.uniformRealization residues.easyWitnessNWCollapse residues.nondetTimeHierarchy branch

/-- **Route ⇒ separation, directly (PROVED).**  The same conclusion from any `WilliamsFastSatRoute` (equivalently the
N-Frame counting branch, entry 319), exhibiting the fast-SAT route ⇒ `¬ (NEXP ⊆ ACC0)` form. -/
theorem williams_separation_from_residues
    (ACC0 : CClass) (f g : ℕ → ℕ) (speedup : Prop)
    (residues : WilliamsClassicalResidues ACC0 f g speedup)
    (route : WilliamsFastSatRoute) :
    ¬ (NEXP ⊆ ACC0) :=
  nframe_counting_branch_to_williams_separation ACC0 f g speedup residues
    (nframe_counting_branch_eq_williams.mpr route)

/-!
**The Williams/N-Frame route, packaged.**  `nframe_counting_branch_to_williams_separation` is the whole route in one
theorem: the N-Frame counting branch (char-0 integer counts, CRT residue readout, `< 2ⁿ` fast-SAT compression,
complement-safe lazy hierarchy — entry 319) plus a single explicit residue bundle (`WilliamsClassicalResidues`: uniform
realization, easy-witness/NW collapse, nondeterministic time hierarchy) ⇒ `¬ (NEXP ⊆ ACC0)`.  The residue surface is
fully exposed; each residue is a *proven* classical theorem (Williams 2011) being formalized.  Not faked, not a new
separation, and not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CountingBranchSeparation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingBranchSeparation.nframe_counting_branch_to_williams_separation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingBranchSeparation.williams_separation_from_residues
