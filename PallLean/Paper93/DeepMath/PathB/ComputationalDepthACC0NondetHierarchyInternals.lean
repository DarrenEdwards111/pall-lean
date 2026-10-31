import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LazyHierarchyEscape

/-!
# Entry 326 — the nondeterministic time-hierarchy residue, internal structure (proved)

The Williams route rests on three named classical residues (entry 320's `WilliamsClassicalResidues`).  This file opens
the **nondeterministic time hierarchy** residue (`ConcreteHierarchy f g := ¬ (NTIME f ⊆ NTIME g)`) and proves its
genuine internal structure: the `NTIME`-class characterisation, the criterion for a language to lie *outside* `NTIME g`,
and the **diagonalisation assembly** reducing the hierarchy to a separating diagonal language.

**The structure.**  `NTIME g` is exactly the languages of `g`-clocked machines: `L ∈ NTIME g ↔ ∃ M, L = langOf M g`
(`mem_NTIME_iff`).  Hence a language lies outside `NTIME g` iff it differs from *every* clocked machine's language
(`not_mem_NTIME_of_no_machine`).  So the hierarchy `¬ (NTIME f ⊆ NTIME g)` follows from a **diagonal** language `D` that
(i) is in `NTIME f` (placement) and (ii) differs from every `g`-clocked machine (diagonalisation) —
`concreteHierarchy_of_diagonal`.

The diagonalisation (ii) is the *complement-safe lazy diagonal* of entry 294 (`lazy_diag_not_mem_range`), re-exported
here as the proved mechanism: a lazily-defined language escapes the entire enumeration of the smaller class without
relying on closure under complement (which `NTIME` lacks).

## What is proved (clean axioms, no `sorry`)

* **`langOf`** — the language a machine `M` decides under the `g`-clock: `langOf M g x := acceptsWithin M x (g |x|)`.
* **`mem_NTIME_iff`** (PROVED) — `L ∈ NTIME g ↔ ∃ M, L = langOf M g`: the `NTIME`-class characterisation.
* **`not_mem_NTIME_of_no_machine`** (PROVED) — `(∀ M, D ≠ langOf M g) → D ∉ NTIME g`: the outside-`NTIME g` criterion.
* **`concreteHierarchy_of_diagonal`** (PROVED) — `D ∈ NTIME f` + `D` differs from every `g`-clocked machine ⟹
  `ConcreteHierarchy f g`: the diagonalisation assembly, reducing the hierarchy residue to placement + diagonalisation.
* **`lazy_diag_escape`** (re-export, PROVED at 294) — the complement-safe lazy diagonalisation: the proved mechanism for
  the diagonalisation residue.

## Honest scope

This proves the **internal assembly** of the time-hierarchy residue: the `NTIME`-class characterisation and the
diagonalisation reduction are theorems (`mem_NTIME_iff`, `concreteHierarchy_of_diagonal`), so `ConcreteHierarchy f g` is
reduced to two precise machine residues — the **placement** (`D ∈ NTIME f`, the clocked universal simulation, entries
296–311) and the **diagonalisation** (`D` differs from every `g`-clocked machine, the proved lazy diagonal of entry
294).  It does **not** discharge the placement (that needs the concrete enumerable machine model; `NTM` here has an
arbitrary `Config` type, so it is not enumerable at this abstraction).  This is the honest decomposition of the
hierarchy socket, parallel to the rest of the arc.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NondetHierarchyInternals

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM

/-- **The language a machine `M` decides under the `g`-clock.**  `langOf M g x := acceptsWithin M x (g |x|)`. -/
def langOf (M : NTM) (g : ℕ → ℕ) : Lang := fun x => acceptsWithin M x (g x.length)

/-- **The `NTIME`-class characterisation (PROVED).**  `L ∈ NTIME g` iff `L` is the language of some `g`-clocked
machine. -/
theorem mem_NTIME_iff (g : ℕ → ℕ) (L : Lang) : L ∈ NTIME g ↔ ∃ M : NTM, L = langOf M g := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, funext fun x => propext (hM x)⟩
  · rintro ⟨M, rfl⟩
    exact ⟨M, fun _ => Iff.rfl⟩

/-- **The outside-`NTIME g` criterion (PROVED).**  A language differing from *every* `g`-clocked machine's language is
not in `NTIME g`. -/
theorem not_mem_NTIME_of_no_machine (g : ℕ → ℕ) (D : Lang) (h : ∀ M : NTM, D ≠ langOf M g) :
    D ∉ NTIME g := by
  intro hD
  obtain ⟨M, hM⟩ := (mem_NTIME_iff g D).mp hD
  exact h M hM

/-- **The diagonalisation assembly (PROVED) — the internal of the hierarchy residue.**  A diagonal language `D` that is
in `NTIME f` (placement) and differs from every `g`-clocked machine (diagonalisation) witnesses
`ConcreteHierarchy f g = ¬ (NTIME f ⊆ NTIME g)`. -/
theorem concreteHierarchy_of_diagonal (f g : ℕ → ℕ) (D : Lang)
    (hf : D ∈ NTIME f) (hdiag : ∀ M : NTM, D ≠ langOf M g) :
    ConcreteHierarchy f g := by
  intro hsub
  exact not_mem_NTIME_of_no_machine g D hdiag (hsub hf)

/-- **The complement-safe lazy diagonalisation (re-export of the entry-294 proof).**  A lazily-defined `D` (copying
`enum i` shifted on each block, complementing only at the boundary) escapes the entire enumeration `enum` — the proved
mechanism behind the diagonalisation residue, valid without closure under complement. -/
theorem lazy_diag_escape
    (enum : ℕ → (ℕ → Bool)) (D : ℕ → Bool) (block len : ℕ → ℕ)
    (hlazy : ∀ i k, k < len i → D (block i + k) = enum i (block i + k + 1))
    (hbdy : ∀ i, D (block i + len i) = ! enum i (block i)) :
    D ∉ Set.range enum :=
  ACC0LazyHierarchyEscape.lazy_diag_not_mem_range enum D block len hlazy hbdy

/-!
**The hierarchy residue, internally.**  `NTIME g` is the languages of `g`-clocked machines (`mem_NTIME_iff`); a language
outside it differs from every such machine (`not_mem_NTIME_of_no_machine`); and a diagonal language that is in `NTIME f`
and differs from every `g`-clocked machine witnesses `¬ (NTIME f ⊆ NTIME g)` (`concreteHierarchy_of_diagonal`).  So the
hierarchy socket reduces to two precise residues — placement (`D ∈ NTIME f`, the clocked simulation of 296–311) and
diagonalisation (the proved complement-safe lazy diagonal of 294, `lazy_diag_escape`).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0NondetHierarchyInternals

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NondetHierarchyInternals.mem_NTIME_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NondetHierarchyInternals.not_mem_NTIME_of_no_machine
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NondetHierarchyInternals.concreteHierarchy_of_diagonal
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NondetHierarchyInternals.lazy_diag_escape
