import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNTIMEEnumerable

/-!
# The canonical nondeterministic time hierarchy — reduced to a single socket

With enumerability discharged for the canonical class (`ntimecanon_enumerable`), the hierarchy's
two sockets collapse to one.  This file wires the discharge into a canonical hierarchy statement
that rests on ONLY the diagonal socket — the universal machine plus lazy diagonalisation — with the
enumerability handled inline (the canonical parameters `(k, data, c)` ARE the enumeration).

## What is proved

* **`hierarchyCanon_from_diagonal`** — a diagonal language in `NTIME(a)` differing from every
  canonical-clock language `canonLang b k data c` gives `NTIME(a) ⊄ NTIMEcanon(b)`.  No separate
  enumerability hypothesis: `NTIMEcanon b D` unfolds to "`D = canonLang b k data c` for some
  `(k,data,c)`", so differing from all of them directly refutes membership.
* **`concreteHierarchyCanon`** — for all `b < a`, the diagonal socket yields the canonical hierarchy.
  The engine's hierarchy ingredient, over the canonical class, rests on exactly one open statement.

## The single remaining socket

`DiagonalAgainstCanon a b` — `NTIME(a)` contains a language differing from every canonical-clock
`NTIME(b)` language.  This is the universal machine (simulating `canonLang b k data c` on its own
index within the larger `n^a` clock) plus delayed/lazy diagonalisation for the nondeterministic
complementation (Žák / Cook / Seiferas–Fischer–Meyer).  It is the one irreducible piece of the
hierarchy mountain — real formalisation labor (a universal machine over `ComposableMachine`), NOT
open mathematics, and NOT of `P ≠ NP` strength.

## Honest scope — connecting to the engine

The canonical hierarchy is `NTIME(a) ⊄ NTIMEcanon(b)`.  Because `NTIMEcanon(b) ⊆ NTIME(b)`, this does
NOT by itself give the engine's `NTIME(a) ⊄ NTIME(b)` — the arbitrary-clock class is strictly larger
(and, per the enumerability finding, not even countable).  Connecting to the live engine requires
the recommended definitional refinement: redefine the engine's `NTIME`/`DTS`/`Σ₂` with the clock
attached to the machine (i.e. AS `NTIMEcanon`).  That refinement is clock-agnostic downstream — the
engine and every audit are indifferent to which `T ≤ canonical` is used — after which this canonical
hierarchy IS the engine's hierarchy ingredient, resting on the single diagonal socket.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HierarchyCanonical

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal
open PallLean.Paper93.DeepMath.PathB.NTIMEEnumerable

/-- **The single remaining hierarchy socket.**  `NTIME(a)` contains a language differing from every
canonical-clock `NTIME(b)` language — the diagonal, i.e. the universal machine plus lazy
diagonalisation. -/
def DiagonalAgainstCanon (a b : ℕ) : Prop :=
  ∃ D, NTIME a D ∧ ∀ (k : ℕ) (data : FinMachineData k) (c : ℕ), D ≠ canonLang b k data c

/-- **The canonical hierarchy from the diagonal socket (proved).**  A diagonal in `NTIME(a)`
differing from every canonical-clock language gives `NTIME(a) ⊄ NTIMEcanon(b)`.  Enumerability is
discharged inline — the canonical parameters are the enumeration. -/
theorem hierarchyCanon_from_diagonal (a b : ℕ) (hdiag : DiagonalAgainstCanon a b) :
    ¬ (∀ L, NTIME a L → NTIMEcanon b L) := by
  obtain ⟨D, hDa, hDdiff⟩ := hdiag
  intro hsub
  obtain ⟨k, data, c, hk⟩ := hsub D hDa
  exact hDdiff k data c hk

/-- **The canonical hierarchy, all rungs (proved).**  For every `b < a`, the diagonal socket yields
`NTIME(a) ⊄ NTIMEcanon(b)`.  The hierarchy ingredient over the canonical class rests on exactly one
open statement (`DiagonalAgainstCanon`). -/
theorem concreteHierarchyCanon
    (hdiag : ∀ a b : ℕ, 1 ≤ b → b < a → DiagonalAgainstCanon a b) :
    ∀ a b : ℕ, 1 ≤ b → b < a → ¬ (∀ L, NTIME a L → NTIMEcanon b L) :=
  fun a b hb hba => hierarchyCanon_from_diagonal a b (hdiag a b hb hba)

/-- **Consistency check (proved).**  The diagonal socket is not vacuous as a hypothesis: any
`NTIME(a)` language `D` that happens to differ from every canonical language witnesses it, and the
wrapper fires.  (A witness that the reduction is sound; the real content is the universal machine.) -/
theorem hierarchyCanon_consistent (a b : ℕ) (D : Lang) (hDa : NTIME a D)
    (hDdiff : ∀ (k : ℕ) (data : FinMachineData k) (c : ℕ), D ≠ canonLang b k data c) :
    ¬ (∀ L, NTIME a L → NTIMEcanon b L) :=
  hierarchyCanon_from_diagonal a b ⟨D, hDa, hDdiff⟩

end PallLean.Paper93.DeepMath.PathB.HierarchyCanonical

#print axioms PallLean.Paper93.DeepMath.PathB.HierarchyCanonical.hierarchyCanon_from_diagonal
#print axioms PallLean.Paper93.DeepMath.PathB.HierarchyCanonical.concreteHierarchyCanon
