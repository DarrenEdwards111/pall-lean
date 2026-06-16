import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM

/-!
# The time-hierarchy diagonalisation — the Cantor argument proved, simulation/enumeration socketed

The nondeterministic time hierarchy (`…ACC0NTM.ConcreteHierarchy`) is the deep socket the Williams reduction rests on.
Its proof is a diagonalisation: a language `D` that disagrees, at each machine's own encoding, with every machine of
the *smaller* class; `D` is then in the smaller class's complement yet decidable in the *bigger* time bound, so the
bigger class is not contained in the smaller.

This file proves the **logical heart** — the Cantor diagonal disagreement — fully, and isolates the two genuinely
computational facts as precise sockets:

* `enum_covers` — the smaller class `NTIME g` is *enumerable* (covered by a list `enum : ℕ → Lang`).  [needs a
  string encoding of machines]
* `diag_in_big` — the diagonal language is decidable within the *bigger* bound, `diagLang ∈ NTIME f`.  [needs a
  time-bounded universal simulator]

Given those, the hierarchy `¬ (NTIME f ⊆ NTIME g)` follows by the diagonal argument, here machine-checked.

## What is proved (clean axioms, no `sorry`)

* **`diagLang`** — the diagonal language `D w := ¬ enum (idx w) w` (`idx : List Bool ≃ ℕ` indexes inputs by machine).
* **`diag_not_mem_range`** — the Cantor core: `diagLang ∉ Set.range enum` (`D` differs from `enum k` at `idx⁻¹ k`).
* **`time_hierarchy_from_sockets`** — given `enum_covers` and `diag_in_big`, `ConcreteHierarchy f g` holds.

## Honest scope

The diagonal *argument* is proved; this is the genuine logical content of Cook's nondeterministic time hierarchy made
machine-checked.  The two computational ingredients — enumerability of `NTIME g` and decidability of the diagonal
within `NTIME f` — are sockets requiring a verified string-encoded machine model and a time-bounded universal
simulator (a major project on top of `…ACC0NTM`).  This does **not** prove the hierarchy outright.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TimeHierarchyDiagonal

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTIME ConcreteHierarchy)

/-- A bijection indexing inputs by `ℕ` (machine indices); `List Bool` is countably infinite. -/
noncomputable def idxEquiv : List Bool ≃ ℕ :=
  haveI : Denumerable (List Bool) := Denumerable.ofEncodableOfInfinite (List Bool)
  Denumerable.eqv (List Bool)

/-- The **diagonal language**: `D w` disagrees with the `idx w`-th enumerated language at input `w`. -/
def diagLang (enum : ℕ → Lang) (idx : List Bool ≃ ℕ) : Lang :=
  fun w => ¬ enum (idx w) w

/-- **The Cantor diagonal core (proved): `diagLang ∉ Set.range enum`.**  If `diagLang = enum k`, then at the input
`idx⁻¹ k` we get `enum k (idx⁻¹ k) = ¬ enum k (idx⁻¹ k)` — a proposition equal to its own negation, absurd. -/
theorem diag_not_mem_range (enum : ℕ → Lang) (idx : List Bool ≃ ℕ) :
    diagLang enum idx ∉ Set.range enum := by
  rintro ⟨k, hk⟩
  have h := congrFun hk (idx.symm k)
  simp only [diagLang, Equiv.apply_symm_apply] at h
  exact iff_not_self (iff_of_eq h)

/-- **The time hierarchy from its two computational sockets (proved diagonal argument).**  If the smaller class
`NTIME g` is enumerable (`enum_covers`) and the diagonal language is decidable within the bigger bound
(`diag_in_big : diagLang ∈ NTIME f`), then `NTIME f ⊄ NTIME g`.  The diagonal language would otherwise be enumerated,
contradicting `diag_not_mem_range`. -/
theorem time_hierarchy_from_sockets (f g : ℕ → ℕ) (enum : ℕ → Lang) (idx : List Bool ≃ ℕ)
    (enum_covers : NTIME g ⊆ Set.range enum)
    (diag_in_big : diagLang enum idx ∈ NTIME f) :
    ConcreteHierarchy f g := by
  intro hsub
  exact diag_not_mem_range enum idx (enum_covers (hsub diag_in_big))

end PallLean.Paper93.DeepMath.PathB.ACC0TimeHierarchyDiagonal

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimeHierarchyDiagonal.diag_not_mem_range
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimeHierarchyDiagonal.time_hierarchy_from_sockets
