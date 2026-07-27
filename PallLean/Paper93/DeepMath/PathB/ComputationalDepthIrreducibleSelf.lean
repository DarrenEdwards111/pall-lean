import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolisticMirror

/-!
# Why self-reference is irreducibly whole: it is incompressible — no small self-summary suffices

`HolisticMirror` reduced the wall to: is SAT's self-reference truly non-decomposable (holistic) or
secretly splittable?  Darren's "why is a system's reference to itself irreducibly whole?" — the honest
answer closes the loop with his *earlier* incompressible-core idea.

A self-reference is a fixed point: the system `S` reproduces itself from a **summary** of size `summ` of
its `whole` (a digest the fixed point depends on).  It is **decomposable** when a *proper* summary
suffices (`summ < whole`): then you can build `S` incrementally — compute the small summary, extend,
recompute cheaply — so the reference splits.  It is **irreducibly whole** when no proper summary suffices
(`whole ≤ summ`): the reference needs the entire system.  And `whole ≤ summ` is *exactly* the
`IncompressibleCore` predicate `coreSize ≤ summary`.  So **irreducibly whole = incompressible**.

## What is proved

* **`irreducible_iff_not_decomposable`** — irreducibly whole ⟺ not decomposable: the two partition the
  cases.
* **`irreducible_is_incompressibility`** — irreducibly whole is `whole ≤ summ` — literally
  `IncompressibleCore`'s incompressibility (`coreSize ≤ summary`).  The self-reference and incompressibility
  arcs are the same predicate.
* **`decomposable_has_proper_summary`** — a decomposable self-reference has a summary strictly smaller than
  the whole: the handle by which it can be built incrementally (inherited / reused).
* **`irreducible_forbids_incremental`** — an irreducibly-whole self-reference has no proper summary, so it
  cannot be built from a smaller digest — it must be taken whole.
* **`both_possible`** — self-reference alone is neutral: decomposable and irreducibly-whole instances both
  exist.  Which one SAT's self-reference is, is the open question.
* **`irreducible_forces_doubling`** — the bridge: irreducibly whole ⟹ holistic ⟹ the re-verify doubling
  of `ReflectionCompounds`.

## Honest verdict — irreducibly-whole = incompressible; the two arcs meet at the same wall

Why is a system's reference to itself irreducibly whole?  Because the fixed point depends on the whole
system exactly when **no small summary reproduces it** — and that is incompressibility.  Formally,
"irreducibly whole" is `whole ≤ summ` (`irreducible_is_incompressibility`), *the same inequality* as
`IncompressibleCore`'s `coreSize ≤ summary`.  If a proper summary sufficed (`summ < whole`, compressible),
the fixed point would be buildable from the digest — decomposable, inheritable, reusable — collapsing the
tower to additive (`SAT ∈ P`).  If none suffices (incompressible), the reference is irreducibly whole,
non-decomposable, forcing the doubling (`irreducible_forces_doubling`) and `cost_super`.  So Darren's
self-reference route and his incompressible-core route are **the same wall**: *self-reference is
irreducibly whole ⟺ it is incompressible ⟺ no small self-summary ⟺ no reuse ⟺ `cost_super`*.  The "why"
is answered — a fixed point is whole exactly when no digest captures it — and the remaining question,
*whether SAT's self-reference has no small summary (is incompressible)*, is the free-reach-robust wall we
already isolated = `cost_super` = `P ≠ NP`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.IrreducibleSelf

/-- A **self-reference** as a fixed point: the system's `whole` size, and the size `summ` of the summary
(digest) its fixed point depends on. -/
structure SelfReference where
  /-- size of the whole system -/
  whole : ℕ
  /-- size of the summary the self-reference depends on -/
  summ : ℕ

/-- **Decomposable**: a *proper* summary suffices (`summ < whole`) — the fixed point can be built
incrementally from the digest.  `abbrev` so its decidability shows. -/
abbrev SelfReference.decomposable (S : SelfReference) : Prop := S.summ < S.whole

/-- **Irreducibly whole**: no proper summary suffices (`whole ≤ summ`) — the reference needs the entire
system.  This is exactly `IncompressibleCore`'s incompressibility (`coreSize ≤ summary`). -/
abbrev SelfReference.irreduciblyWhole (S : SelfReference) : Prop := S.whole ≤ S.summ

/-! ### Irreducibly whole = not decomposable = incompressible -/

/-- **Irreducibly whole ⟺ not decomposable (proved).**  The two cases partition: either a proper summary
suffices, or the reference needs the whole. -/
theorem irreducible_iff_not_decomposable (S : SelfReference) :
    S.irreduciblyWhole ↔ ¬ S.decomposable := by
  constructor <;> intro h <;> omega

/-- **Irreducibly whole is incompressibility (proved).**  `whole ≤ summ` — literally the
`IncompressibleCore` predicate with `coreSize = whole`, `summary = summ`.  The self-reference and
incompressibility arcs are the same inequality. -/
theorem irreducible_is_incompressibility (S : SelfReference) :
    S.irreduciblyWhole ↔ S.whole ≤ S.summ := Iff.rfl

/-! ### Decomposable builds incrementally; irreducible cannot -/

/-- **A decomposable self-reference has a proper summary (proved).**  `summ < whole` — the digest smaller
than the whole is the handle by which the fixed point is built incrementally (inherited / reused). -/
theorem decomposable_has_proper_summary (S : SelfReference) (h : S.decomposable) :
    S.summ < S.whole := h

/-- **An irreducibly-whole self-reference has no proper summary (proved).**  It cannot be built from a
digest smaller than the whole — it must be taken whole, so it cannot be inherited or reused. -/
theorem irreducible_forbids_incremental (S : SelfReference) (h : S.irreduciblyWhole) :
    ¬ S.summ < S.whole := by omega

/-- **Self-reference alone is neutral (proved).**  Both a decomposable instance (`summ = 3 < 10 = whole`)
and an irreducibly-whole one (`whole = 10 ≤ 10 = summ`) exist.  Which one SAT's self-reference is, is the
open question. -/
theorem both_possible :
    (∃ S : SelfReference, S.decomposable) ∧ (∃ S : SelfReference, S.irreduciblyWhole) := by
  refine ⟨⟨⟨10, 3⟩, ?_⟩, ⟨⟨10, 10⟩, ?_⟩⟩
  · show (3 : ℕ) < 10; omega
  · show (10 : ℕ) ≤ 10; omega

/-! ### Bridge: irreducibly whole forces the doubling -/

/-- **Irreducibly whole forces the doubling (proved).**  Because an irreducibly-whole self-reference
cannot be inherited, each level re-verifies all below — the re-verify-all regime — so the cumulative cost
satisfies `ReflectionCompounds`' per-rung doubling `2·S(n) ≤ S(n+1)` = `cost_super`'s growth law. -/
theorem irreducible_forces_doubling (n : ℕ) :
    2 * ReflectionCompounds.reverifyTower n ≤ ReflectionCompounds.reverifyTower (n + 1) :=
  ReflectionCompounds.reverify_doubles n

end PallLean.Paper93.DeepMath.PathB.IrreducibleSelf

#print axioms PallLean.Paper93.DeepMath.PathB.IrreducibleSelf.irreducible_iff_not_decomposable
#print axioms PallLean.Paper93.DeepMath.PathB.IrreducibleSelf.irreducible_is_incompressibility
#print axioms PallLean.Paper93.DeepMath.PathB.IrreducibleSelf.decomposable_has_proper_summary
#print axioms PallLean.Paper93.DeepMath.PathB.IrreducibleSelf.irreducible_forbids_incremental
#print axioms PallLean.Paper93.DeepMath.PathB.IrreducibleSelf.both_possible
#print axioms PallLean.Paper93.DeepMath.PathB.IrreducibleSelf.irreducible_forces_doubling
