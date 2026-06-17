import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NondetTimeHierarchy

/-!
# A witness model for the hierarchy sockets — `NPEnumerable` + `DiagonalInNexp` discharged end-to-end (proved)

Entry 200 reduced the hierarchy `NexpNeqNp` to two model sockets: `NPEnumerable` (`NP` is the range of a machine
enumeration) and `DiagonalInNexp` (the diagonal language lies in `NEXP`).  This file shows those sockets are
**non-vacuous and the diagonalization discharge fires end-to-end**, by exhibiting an explicit model where both hold and
the conclusion is a *genuine, true* inequality.

The witness model: take `NP := Set.range enum` for any enumeration `enum : ℕ → Lang`, and `NEXP := Set.univ` (all
languages).  Then `NPEnumerable NP` holds trivially (`⟨enum, rfl⟩`), and `DiagonalInNexp Set.univ NP` holds trivially
(every diagonal lies in `Set.univ`).  The entry-200 discharge then yields `Set.univ ≠ Set.range enum` — a *genuinely
true* statement: the diagonal language `diag enum` lies in `Set.univ` but escapes `Set.range enum`
(`diag_not_mem_range`), so no enumeration exhausts all languages.  This is the diagonalization *biting* in a concrete
model.

## What is proved (clean axioms, no `sorry`)

* **`npEnumerable_range`** — `NPEnumerable (Set.range enum)` for any `enum` (`⟨enum, rfl⟩`).
* **`diagonalInNexp_univ`** — `DiagonalInNexp Set.univ (Set.range enum)` (every diagonal is in `Set.univ`).
* **`witness_nexpNeqNp`** — the end-to-end discharge: `NexpNeqNp Set.univ (Set.range enum)`, i.e.
  `Set.univ ≠ Set.range enum`, via the entry-200 `nexpNeqNp_discharge` — the diagonalization yields a genuine
  inequality.

## Honest scope

This is a **witness/consistency model**, not a claim about the real `NEXP`/`NP`.  It discharges both entry-200 model
sockets in an explicit model (`NP` an enumeration, `NEXP` all languages) and runs the diagonalization discharge to a
*true* conclusion (`Set.univ ≠ Set.range enum`, a real consequence of `diag_not_mem_range`), demonstrating the
diagonalization kernel is non-vacuous and the socket interface is satisfiable.  It does **not** prove the actual
`NEXP ≠ NP` (which needs the genuine model facts — that `NP` *is* the clocked-machine enumeration and that `NEXP`
*contains the diagonal via lazy diagonalization* — not the trivial `Set.univ`).  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0HierarchyWitness

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass Lang)
open PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonCollapse (NexpNeqNp)
open PallLean.Paper93.DeepMath.PathB.ACC0NondetTimeHierarchy (NPEnumerable DiagonalInNexp diag nexpNeqNp_discharge)

/-- **`NPEnumerable` for a range (PROVED).**  Any `NP` modelled as the range of an enumeration is, tautologically,
enumerable. -/
theorem npEnumerable_range (enum : ℕ → Lang) : NPEnumerable (Set.range enum) := ⟨enum, rfl⟩

/-- **`DiagonalInNexp` for the full-universe `NEXP` (PROVED).**  Taking `NEXP := Set.univ`, every diagonal language lies
in `NEXP` trivially. -/
theorem diagonalInNexp_univ (enum : ℕ → Lang) : DiagonalInNexp Set.univ (Set.range enum) :=
  fun e _ => Set.mem_univ (diag e)

/-- **The end-to-end discharge (PROVED): a genuine inequality.**  In the witness model `NP := Set.range enum`,
`NEXP := Set.univ`, both sockets hold and the entry-200 `nexpNeqNp_discharge` yields `Set.univ ≠ Set.range enum` — true
because the diagonal language escapes the enumeration (`diag_not_mem_range`).  The diagonalization kernel bites. -/
theorem witness_nexpNeqNp (enum : ℕ → Lang) : NexpNeqNp (Set.univ) (Set.range enum) :=
  nexpNeqNp_discharge Set.univ (Set.range enum) (npEnumerable_range enum) (diagonalInNexp_univ enum)

end PallLean.Paper93.DeepMath.PathB.ACC0HierarchyWitness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0HierarchyWitness.npEnumerable_range
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0HierarchyWitness.witness_nexpNeqNp
