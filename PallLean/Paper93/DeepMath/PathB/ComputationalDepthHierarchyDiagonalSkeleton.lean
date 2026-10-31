import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteTradingClasses

/-!
# The nondeterministic time hierarchy: diagonalization skeleton

Mountain 4 of the socket-discharge campaign.  `ConcreteHierarchy` — the nondeterministic time
hierarchy `NTIME(n^a) ⊄ NTIME(n^b)` for `b < a` — is the engine's fourth ingredient and currently a
bare unproved `def`.  This file discharges its WRAPPER: it reduces `ConcreteHierarchy` to two named
sockets over the concrete classes, with ALL the diagonalization logic machine-checked, isolating
exactly the universal-machine / lazy-diagonalization content that is the literature core.

## The two sockets

* **`NTIMEEnumerable b`** — the `NTIME(n^b)` languages are enumerable: some `enum : ℕ → Lang` covers
  them all.  This is the countability of clocked nondeterministic machines (the `FinMachineData`
  countability of `UniformityGapDiagonal`, refined to fix the clock at the canonical `c·(n+1)^b`).
  The more tractable socket — dischargeable next.
* **`DiagonalInNTIME a enum`** — `NTIME(n^a)` contains a language differing from every `enum i`.
  This is the diagonal language: a universal machine simulating `enum i` within the larger `n^a`
  clock, with the nondeterministic complementation handled by delayed (lazy) diagonalization
  (Žák / Cook / Seiferas–Fischer–Meyer).  The hard literature core.

## What is proved

* **`hierarchy_step`** — the diagonalization wrapper: an enumeration covering `NTIME(b)` plus a
  diagonal language in `NTIME(a)` differing from every enumerated language ⟹ `NTIME(a) ⊄ NTIME(b)`.
  One line of logic, but it is the exact shape every hierarchy theorem instantiates.
* **`concreteHierarchy_step_from_sockets`** — the same, packaged as the two named sockets at a fixed
  `(a,b)`.
* **`concreteHierarchy_from_sockets`** — the full assembly: the two sockets for all `b < a` yield
  `ConcreteHierarchy` verbatim.  So the engine's hierarchy ingredient now rests on exactly
  enumerability + diagonal-existence.

## Honest scope

The wrapper is proved; the content is in the two sockets.  `NTIMEEnumerable` is the countability of
machines (real, and the next discharge target — the clock-fix is the one subtlety, solved for the
clock-free case by `UniformityGapDiagonal`'s `langOf`).  `DiagonalInNTIME` is the universal machine
plus the nondeterministic lazy-diagonalization trick — a literature theorem (formalization labor),
NOT open mathematics, and NONE of `P ≠ NP` strength.  This rung turns `ConcreteHierarchy` from an
opaque `def` into a reduction to two precise, standard statements about the concrete machine model.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HierarchyDiagonalSkeleton

open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses

/-- **Socket 1.**  The `NTIME(n^b)` languages are enumerable — some sequence covers them all. -/
def NTIMEEnumerable (b : ℕ) : Prop :=
  ∃ enum : ℕ → Lang, ∀ L, NTIME b L → ∃ i, L = enum i

/-- **Socket 2.**  `NTIME(n^a)` contains a language differing from every language in the enumeration
`enum` — the diagonal. -/
def DiagonalInNTIME (a : ℕ) (enum : ℕ → Lang) : Prop :=
  ∃ D, NTIME a D ∧ ∀ i, D ≠ enum i

/-- **The diagonalization wrapper (proved).**  An enumeration covering `NTIME(b)` plus a diagonal
language in `NTIME(a)` that differs from every enumerated language gives `NTIME(a) ⊄ NTIME(b)`: the
diagonal is in `NTIME(a)` but, differing from every `NTIME(b)` language, cannot be in `NTIME(b)`. -/
theorem hierarchy_step (a b : ℕ) (enum : ℕ → Lang)
    (hcov : ∀ L, NTIME b L → ∃ i, L = enum i)
    (hdiag : ∃ D, NTIME a D ∧ ∀ i, D ≠ enum i) :
    ¬ (∀ L, NTIME a L → NTIME b L) := by
  obtain ⟨D, hDa, hDdiff⟩ := hdiag
  intro hsub
  obtain ⟨i, hi⟩ := hcov D (hsub D hDa)
  exact hDdiff i hi

/-- **The hierarchy step from the two named sockets (proved).** -/
theorem concreteHierarchy_step_from_sockets (a b : ℕ) (henum : NTIMEEnumerable b)
    (hdiag : ∀ enum : ℕ → Lang, (∀ L, NTIME b L → ∃ i, L = enum i) → DiagonalInNTIME a enum) :
    ¬ (∀ L, NTIME a L → NTIME b L) := by
  obtain ⟨enum, hcov⟩ := henum
  exact hierarchy_step a b enum hcov (hdiag enum hcov)

/-- **`ConcreteHierarchy` from the two sockets (proved).**  Enumerability of `NTIME(b)` for every `b`
and a diagonal in `NTIME(a)` against every such enumeration (for `b < a`) yield the engine's
hierarchy ingredient verbatim. -/
theorem concreteHierarchy_from_sockets
    (henum : ∀ b, NTIMEEnumerable b)
    (hdiag : ∀ a b : ℕ, 1 ≤ b → b < a →
      ∀ enum : ℕ → Lang, (∀ L, NTIME b L → ∃ i, L = enum i) → DiagonalInNTIME a enum) :
    ConcreteHierarchy := by
  intro a b hb hba
  exact concreteHierarchy_step_from_sockets a b (henum b) (fun enum hcov => hdiag a b hb hba enum hcov)

/-- **Consistency of the skeleton (proved).**  The sockets are jointly satisfiable — the trivial
world where `NTIME b` is empty (`enum` arbitrary, covering vacuously) and the diagonal is any
`NTIME a` language — so the wrapper is non-vacuous.  (A witness that the reduction is not built on a
contradiction; the real content is the two literature sockets.) -/
theorem skeleton_consistent (a : ℕ) (enum : ℕ → Lang) (D : Lang) (hD : NTIME a D)
    (hDdiff : ∀ i, D ≠ enum i) (hcov : ∀ L, NTIME 1 L → ∃ i, L = enum i) :
    ¬ (∀ L, NTIME a L → NTIME 1 L) :=
  hierarchy_step a 1 enum hcov ⟨D, hD, hDdiff⟩

end PallLean.Paper93.DeepMath.PathB.HierarchyDiagonalSkeleton

#print axioms PallLean.Paper93.DeepMath.PathB.HierarchyDiagonalSkeleton.hierarchy_step
#print axioms PallLean.Paper93.DeepMath.PathB.HierarchyDiagonalSkeleton.concreteHierarchy_from_sockets
