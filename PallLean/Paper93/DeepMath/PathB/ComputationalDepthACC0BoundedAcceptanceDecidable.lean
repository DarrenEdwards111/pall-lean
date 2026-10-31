import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM

/-!
# Bounded acceptance is decidable — the lazy diagonal's boundary complement, realized (proved)

The realization socket is down to the lazy-diagonal decider machine (entry 298).  Its hard case is the **boundary
complement**: the lazy diagonal flips `enum i` once per block, `D(boundary) = ¬ enum i (start)`.  For a *nondeterministic*
machine this is not free — except, as Cook's lazy diagonalization exploits, the start input is tiny relative to the
boundary, so the bounded computation can be *exhaustively* explored and complemented.  This file proves the foundation:
**bounded acceptance in the concrete model is decidable** (a finite reachable-config search), so its complement is
computable — exactly *why* "one boundary complement is affordable."

**The mechanism.**  `concreteStep M` has *finite branching* (`M` is a finite list of rules), so the configs reachable
in `k` steps form a finite list `reachExactly M k c` with `reachIn (toNTM M) k c d ↔ d ∈ reachExactly M k c`.  Then
`acceptsWithin (toNTM M) x t` is a bounded search — `∃ k ≤ t, ∃ c ∈ reachExactly M k (0,0,x), c.1 = 1` — hence decidable
(`decAccept`).  So `¬ acceptsWithin (toNTM M) x t` is decidable too: the boundary complement is a finite, computable
operation.

## What is proved (clean axioms, no `sorry`)

* **`succs`, `mem_succs`** — the (finite) one-step successors: `d ∈ succs M c ↔ concreteStep M c d`.
* **`reachExactly`, `mem_reachExactly`** — the finite reachable-config list: `d ∈ reachExactly M k c ↔ reachIn (toNTM M)
  k c d`.
* **`acceptsWithin_iff_decAccept`** — bounded acceptance is the decidable finite search `decAccept M x t`.
* **`instDecidableAcceptsWithin`** — `Decidable (acceptsWithin (toNTM M) x t)`: bounded acceptance is decidable.
* **`boundary_complement_decidable`** — `Decidable (¬ acceptsWithin (toNTM M) x t)`: the lazy diagonal's boundary
  complement is computable.

## Honest scope

This proves the **boundary complement is computable** — bounded concrete acceptance is a finite reachable-config search,
hence decidable, hence complementable.  This is the crux of *why* lazy diagonalization's single boundary complement is
affordable (the exhaustive exploration of the small bounded computation), now machine-checked over the transition-table
model.  It is the foundation of the lazy-diagonal decider's boundary case; the full decider still needs the per-block
bookkeeping assembly (decode the block index, route copy-vs-boundary, run the universal machine on the copy input — the
copy case is the universal simulation of entries 296/297, the boundary case rests on this decidability) and the clocking
(entry 298, the exhaustive search fits the bigger bound since the start input is small).  Those are physical engineering,
proven-classical, not open obstructions (`NEXP ⊄ ACC⁰` is Williams 2011).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BoundedAcceptanceDecidable

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig concreteStep applyTrans readSym toNTM)

/-- The (finite) one-step successors of `c` under `M`: rules whose left-hand side matches, applied. -/
def succs (M : TMachine) (c : CConfig) : List CConfig :=
  (M.filter (fun t => decide (t.1 = (c.1, readSym c)))).map (applyTrans c)

/-- **The successors enumerate `concreteStep` (proved): `d ∈ succs M c ↔ concreteStep M c d`.** -/
theorem mem_succs (M : TMachine) (c d : CConfig) : d ∈ succs M c ↔ concreteStep M c d := by
  unfold succs concreteStep
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ⟨htM, hpred⟩, hd⟩
    exact ⟨t, htM, hpred, hd.symm⟩
  · rintro ⟨t, htM, hpred, hd⟩
    exact ⟨t, ⟨htM, hpred⟩, hd.symm⟩

/-- The finite list of configs reachable in exactly `k` steps from `c`. -/
def reachExactly (M : TMachine) : ℕ → CConfig → List CConfig
  | 0, c => [c]
  | (k + 1), c => (succs M c).flatMap (fun e => reachExactly M k e)

/-- **The reachable list enumerates `reachIn` (proved): `d ∈ reachExactly M k c ↔ reachIn (toNTM M) k c d`.** -/
theorem mem_reachExactly (M : TMachine) (k : ℕ) (c d : CConfig) :
    d ∈ reachExactly M k c ↔ reachIn (toNTM M) k c d := by
  induction k generalizing c with
  | zero =>
    simp only [reachExactly, List.mem_singleton]
    exact eq_comm
  | succ k ih =>
    simp only [reachExactly, reachIn, List.mem_flatMap]
    constructor
    · rintro ⟨e, he, hd⟩
      exact ⟨e, (mem_succs M c e).mp he, (ih e).mp hd⟩
    · rintro ⟨e, hs, hr⟩
      exact ⟨e, (mem_succs M c e).mpr hs, (ih e).mpr hr⟩

/-- The decidable bounded-acceptance search: some `k ≤ t` reaches an accepting (state `1`) config. -/
def decAccept (M : TMachine) (x : List Bool) (t : ℕ) : Bool :=
  (List.range (t + 1)).any (fun k => (reachExactly M k (0, 0, x)).any (fun c => decide (c.1 = 1)))

/-- **Bounded acceptance is the finite search (proved): `acceptsWithin (toNTM M) x t ↔ decAccept M x t = true`.** -/
theorem acceptsWithin_iff_decAccept (M : TMachine) (x : List Bool) (t : ℕ) :
    acceptsWithin (toNTM M) x t ↔ decAccept M x t = true := by
  unfold acceptsWithin decAccept
  constructor
  · rintro ⟨k, hk, c, hr, ha⟩
    rw [List.any_eq_true]
    refine ⟨k, by rw [List.mem_range]; omega, ?_⟩
    rw [List.any_eq_true]
    exact ⟨c, (mem_reachExactly M k _ c).mpr hr, by simpa using ha⟩
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨k, hk, hc⟩ := h
    rw [List.mem_range] at hk
    rw [List.any_eq_true] at hc
    obtain ⟨c, hcmem, hc1⟩ := hc
    exact ⟨k, by omega, c, (mem_reachExactly M k _ c).mp hcmem, by simpa using hc1⟩

/-- **Bounded acceptance is decidable (PROVED).**  A finite reachable-config search decides it. -/
instance instDecidableAcceptsWithin (M : TMachine) (x : List Bool) (t : ℕ) :
    Decidable (acceptsWithin (toNTM M) x t) :=
  decidable_of_iff _ (acceptsWithin_iff_decAccept M x t).symm

/-- **The lazy diagonal's boundary complement is computable (PROVED).**  `¬ acceptsWithin (toNTM M) x t` is decidable:
complementing a bounded nondeterministic computation is a finite, computable operation — exactly why Cook's lazy
diagonalization can afford its single boundary complement (the start input is small, the search is bounded). -/
def boundary_complement_decidable (M : TMachine) (x : List Bool) (t : ℕ) :
    Decidable (¬ acceptsWithin (toNTM M) x t) :=
  inferInstance

/-!
**The boundary complement, realized.**  Bounded concrete acceptance is a finite reachable-config search
(`reachExactly` enumerates `reachIn`), hence **decidable** (`instDecidableAcceptsWithin`), hence its complement is
**computable** (`boundary_complement_decidable`).  This is the crux of why lazy diagonalization's one boundary complement
is affordable — the exhaustive exploration of the small bounded computation — now machine-checked.  It is the foundation
of the lazy-diagonal decider's boundary case; the full decider needs the per-block bookkeeping (decode index, route
copy-vs-boundary — copy via the universal simulation of 296/297, boundary via this decidability) and the clocking (298).
Those are physical engineering, proven-classical, not open obstructions.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0BoundedAcceptanceDecidable

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedAcceptanceDecidable.mem_succs
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedAcceptanceDecidable.mem_reachExactly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedAcceptanceDecidable.acceptsWithin_iff_decAccept
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedAcceptanceDecidable.boundary_complement_decidable
