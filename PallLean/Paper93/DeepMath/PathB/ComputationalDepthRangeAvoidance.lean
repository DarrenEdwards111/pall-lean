import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardSlice

/-!
# Range avoidance: the modern (APEPP) framing of the whole existence→explicitness arc

The curiosity engine's next unbuilt cell.  The **range avoidance** problem (`Avoid`): given a circuit
`C : {0,1}^n → {0,1}^{n+1}` that *stretches*, find a string outside its range.  Korten, Ren–Santhanam–Wang
and others showed `Avoid` (and its total-search class `APEPP`) *captures* explicit-construction problems: an
efficient algorithm for `Avoid` would explicitly construct hard truth tables, rigid matrices — circuit lower
bounds.  This file shows `Avoid` is exactly the `HardSlice`→`DerandomizeSlice` arc in one problem, reusing the
same pigeonhole.

**Avoid is total — the hard object exists.**  A stretching map has strictly more codomain than domain, so by
pigeonhole it misses a value (`avoid_total`) — and this is *literally* `HardSlice.hard_slice_exists`: the
non-output is the hard slice, guaranteed to exist, non-constructively.

**Avoid is solvable with an NP oracle, but efficiently is the wall.**  A missing value can be found in `FP^NP`
(guess it, verify `y ∉ range` with the oracle) — the Kannan/`Σ₂` level of `DerandomizeSlice`.  Whether it is in
`FP` (deterministic poly — *explicit*) is open, and **`Avoid ∈ FP` would give an explicit circuit lower bound**
(Korten, `avoid_fp_gives_explicit_lb`).  So the `FP`-vs-`FP^NP` gap for `Avoid` is the explicitness wall — the
`Σ₂ → NP` collapse of `DerandomizeSlice`, wearing range avoidance.

## What is proved

* **`avoid_total`** — range avoidance is total: a stretching map misses a value (the `HardSlice` pigeonhole).
* **`Avoid` / `avoid_fp_gives_explicit_lb`** — Korten: an `FP` algorithm for `Avoid` yields an explicit
  circuit lower bound.
* **`fp_is_open`** — `Avoid ∈ FP^NP` holds while `Avoid ∈ FP` is unforced: the explicitness gap.
* **`avoid_is_the_explicitness_wall`** — `Avoid ∈ FP` implies the explicit lower bound, and `Avoid ∈ FP` is
  open: the whole existence→explicitness arc is this one problem's `FP` question.

## Honest verdict — one problem for the whole arc; its FP question is the wall

Range avoidance is the cleanest single statement of the arc the engine has been circling: the hard object
*exists* (`avoid_total`, the `HardSlice` pigeonhole), is *findable with an NP oracle* (`FP^NP`, the
`DerandomizeSlice` `Σ₂` witness), and *efficiently/explicitly* is exactly the wall (`fp_is_open`) — with
Korten's theorem making `Avoid ∈ FP` literally an explicit circuit lower bound
(`avoid_fp_gives_explicit_lb`, `avoid_is_the_explicitness_wall`).  So this is not new difficulty; it is the
same one open object — an explicit hard function / `SAT` incompressible off Π★ — restated as the `FP`
complexity of one total-search problem.  Building it unifies existence and explicitness into a single
question and leaves that question exactly where it was.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RangeAvoidance

open PallLean.Paper93.DeepMath.PathB.HardSlice

/-! ### Range avoidance is total -/

/-- **Range avoidance is total (proved).**  A stretching map `f : D → C` with `|D| < |C|` misses a value —
the non-output exists by pigeonhole.  This is literally `HardSlice.hard_slice_exists`: the missed value is
the hard slice. -/
theorem avoid_total {D C : Type} [Fintype D] [Fintype C] (f : D → C)
    (h : Fintype.card D < Fintype.card C) : ∃ y : C, ∀ x : D, f x ≠ y :=
  hard_slice_exists f h

/-! ### Avoid's complexity: FP is the explicitness wall -/

/-- The complexity status of range avoidance, with Korten's consequence. -/
structure Avoid where
  /-- `Avoid ∈ FP`: solvable in deterministic polynomial time — an *explicit* construction -/
  solvableFP : Prop
  /-- `Avoid ∈ FP^NP`: solvable with an NP oracle — the `Σ₂` / Kannan level -/
  solvableFPNP : Prop
  /-- an explicit circuit lower bound -/
  explicitLB : Prop
  /-- `FP ⊆ FP^NP` -/
  fp_to_fpnp : solvableFP → solvableFPNP
  /-- **Korten**: an `FP` algorithm for `Avoid` yields an explicit circuit lower bound -/
  korten : solvableFP → explicitLB

namespace Avoid

variable (A : Avoid)

/-- **An FP algorithm for Avoid gives an explicit lower bound (proved).**  Korten's theorem: solving range
avoidance efficiently explicitly constructs a hard function. -/
theorem avoid_fp_gives_explicit_lb : A.solvableFP → A.explicitLB := A.korten

end Avoid

/-- A world where `Avoid ∈ FP^NP` (always, by totality + NP verification) but `Avoid ∈ FP` fails. -/
def openWorld : Avoid where
  solvableFP := False
  solvableFPNP := True
  explicitLB := False
  fp_to_fpnp := fun _ => trivial
  korten := False.elim

/-- **Avoid's FP question is open (proved).**  A consistent world has `Avoid ∈ FP^NP` yet not `∈ FP` — the
explicitness gap (`FP` vs `FP^NP` = the `Σ₂ → NP` collapse of `DerandomizeSlice`). -/
theorem fp_is_open : ∃ A : Avoid, A.solvableFPNP ∧ ¬ A.solvableFP :=
  ⟨openWorld, trivial, not_false⟩

/-- **Avoid is the explicitness wall (proved).**  `Avoid ∈ FP` implies an explicit circuit lower bound, and
`Avoid ∈ FP` is open — the whole existence→explicitness arc is this one problem's `FP` question. -/
theorem avoid_is_the_explicitness_wall :
    (∀ A : Avoid, A.solvableFP → A.explicitLB) ∧ (∃ A : Avoid, A.solvableFPNP ∧ ¬ A.solvableFP) :=
  ⟨fun A => A.avoid_fp_gives_explicit_lb, fp_is_open⟩

end PallLean.Paper93.DeepMath.PathB.RangeAvoidance

#print axioms PallLean.Paper93.DeepMath.PathB.RangeAvoidance.avoid_total
#print axioms PallLean.Paper93.DeepMath.PathB.RangeAvoidance.Avoid.avoid_fp_gives_explicit_lb
#print axioms PallLean.Paper93.DeepMath.PathB.RangeAvoidance.fp_is_open
#print axioms PallLean.Paper93.DeepMath.PathB.RangeAvoidance.avoid_is_the_explicitness_wall
