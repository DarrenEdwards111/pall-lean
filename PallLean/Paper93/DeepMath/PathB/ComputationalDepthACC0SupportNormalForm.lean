import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Depth3Mixed

set_option maxHeartbeats 1000000

/-!
# Chipping at `ACC⁰ ⊆ mixed-bottom`: the support normal form

The depth-3 mixed fragment (`…ACC0Depth3Mixed`) *assumed* the bottom gates were observed by small statistics.  This
file derives that from the **syntax** of `ACC0Circuit`: every circuit reads a finite set of variables (`support`),
its value depends only on them (`eval_depends_on_support`, by induction on the circuit), so **any** `ACC⁰` circuit
is observed by the projection to its support (`acc0_observed_by_projection`) — a junta observer of state count
`2^{|support|}`.

Consequently any `ACC⁰` circuit reading `< n` variables is SAT-searchable below brute force
(`acc0_junta_searchable`): the depth-reduction socket is discharged for the **junta** fragment, now at the level of
actual circuit syntax rather than assumed observers.  (The many-subcircuit / mixed-bottom version composes
`acc0_observed_by_projection` with `…ACC0Depth3Mixed.depth_mixed_searchable`.)

## What is proved (clean axioms, no `sorry`)

* `support` — the variables an `ACC0Circuit` reads.
* `eval_depends_on_support` — **the value depends only on the support** (induction on the circuit).
* `acc0_observed_by_projection` — **any `ACC⁰` circuit is observed by the projection to its support** (`card
  2^{|support|}`).
* `acc0_junta_searchable` — any `ACC⁰` circuit (of any depth) reading `< n` variables is SAT-searchable in `< 2^n` cells.

## Honest scope

A genuine syntax-level chip at `ACC⁰ ⊆ mixed-bottom`: bounded-support subcircuits *are* projection-observers, proved
from the circuit semantics.  It is a gain only when the subcircuits read few variables (juntas) — a circuit reading
all `n` variables gives the trivial `2^n`.  It does **not** prove the full Yao–Beigel–Tarui reduction (that an
arbitrary `ACC⁰` circuit has a *small-support / `MOD`* bottom normal form — the deep step, still open).  Still the
cell-count model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SupportNormalForm

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiToy
open PallLean.Paper93.DeepMath.PathB.ACC0Depth3Mixed

variable {n : ℕ}

/-- The set of input variables an `ACC⁰` circuit reads. -/
def support : ACC0Circuit n → Finset (Fin n)
  | .const _ => ∅
  | .var i => {i}
  | .not c => support c
  | .and a b => support a ∪ support b
  | .or a b => support a ∪ support b
  | .mod _ S _ => S

/-- **The value depends only on the support (proved, by induction on the circuit).** -/
theorem eval_depends_on_support :
    ∀ (C : ACC0Circuit n) (x y : Fin n → Bool), (∀ i ∈ support C, x i = y i) → eval C x = eval C y := by
  intro C
  induction C with
  | const b => intro x y _; rfl
  | var i => intro x y h; exact h i (Finset.mem_singleton_self i)
  | not c ih =>
      intro x y h
      show (!(eval c x)) = (!(eval c y))
      rw [ih x y h]
  | and a b iha ihb =>
      intro x y h
      show (eval a x && eval b x) = (eval a y && eval b y)
      rw [iha x y (fun i hi => h i (Finset.mem_union_left _ hi)),
          ihb x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  | or a b iha ihb =>
      intro x y h
      show (eval a x || eval b x) = (eval a y || eval b y)
      rw [iha x y (fun i hi => h i (Finset.mem_union_left _ hi)),
          ihb x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  | mod q S t =>
      intro x y h
      show decide (modQStatOn S q x = t) = decide (modQStatOn S q y = t)
      have hstat : modQStatOn S q x = modQStatOn S q y := by
        unfold modQStatOn
        congr 1
        unfold weightOn
        exact Finset.sum_congr rfl (fun i hi => by rw [h i hi])
      rw [hstat]

/-- **Any `ACC⁰` circuit is observed by the projection to its support (proved), state count `2^{|support|}`.** -/
theorem acc0_observed_by_projection (C : ACC0Circuit n) :
    ObservedBy (eval C) (fun x => fun j : ↥(support C) => x j.val) :=
  boundedGate_observedBy (support C) (eval C) (fun x y h => eval_depends_on_support C x y h)

/-- **An `ACC⁰` junta is SAT-searchable below brute force (proved).**  Any `ACC⁰` circuit (of *any* depth) reading
`< n` variables (more generally `2^{|support|} < 2^n`) has its SAT decided by a projection-observer search over
`< 2^n` cells.  The depth-reduction socket discharged, at the level of circuit syntax, for the **junta** fragment:
the gain is real exactly when the circuit reads few of its inputs. -/
theorem acc0_junta_searchable (C : ACC0Circuit n) (hregime : 2 ^ (support C).card < 2 ^ n) :
    ∃ g : (↥(support C) → Bool) → Bool,
      (Satisfiable (eval C)
        ↔ ∃ s ∈ Finset.univ.image (fun (x : Fin n → Bool) => fun j : ↥(support C) => x j.val), g s = true)
      ∧ (Finset.univ.image (fun (x : Fin n → Bool) => fun j : ↥(support C) => x j.val)).card < 2 ^ n := by
  obtain ⟨g, hg⟩ := acc0_observed_by_projection C
  refine ⟨g, observed_sat_iff g hg, ?_⟩
  exact lt_of_le_of_lt (le_trans (observed_cellCount_le _) (le_of_eq (proj_card (support C)))) hregime

end PallLean.Paper93.DeepMath.PathB.ACC0SupportNormalForm

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SupportNormalForm.eval_depends_on_support
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SupportNormalForm.acc0_observed_by_projection
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SupportNormalForm.acc0_junta_searchable
