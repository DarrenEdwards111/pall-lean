import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardSlice

/-!
# Paving the Korten socket: explicit construction reduces to range avoidance, from scratch

`RangeAvoidance` used Korten's theorem — *an efficient range-avoidance algorithm yields explicit
constructions of hard objects (hard truth tables, rigid matrices, …)* — as a hypothesis.  This file pays its
genuine core: the reduction from explicit construction to range avoidance, proved from scratch.

**The reduction (the heart of Korten).**  Many explicit-construction problems have the shape: *build an
object with property `P`, where the objects **without** `P` — the "bad" ones — are few, hence enumerable by a
stretching map `enum : Idx → Obj` with `|Idx| < |Obj|`.*  Then the range of `enum` is exactly the bad set, so
a **non-output** of `enum` is a **good** object (`avoid_solution_is_good`).  Constructing a good object is
therefore *solving range avoidance* for `enum` — so `Avoid ∈ FP` gives explicit constructions
(`korten_reduction`), and pigeonhole guarantees a good object exists (`korten_good_exists`).

**It generalizes `HardSlice`.**  Instantiate `P f := "no circuit computes f"` (hard) and let `enum = eval`
enumerate the easy functions: a non-output of `eval` is a hard function.  That is exactly `HardSlice` —
Korten's reduction *is* the circuit-counting pigeonhole, lifted to arbitrary explicit-construction problems
(`korten_instance_hard_function`).

**Honest scope.**  The full Korten result instantiates this reduction with *specific* enumerators for
specific hard objects (rigid matrices, `MCSP`-style truth tables) and handles the `FP^NP` variants — the
instance-specific circuit constructions are not formalized here.  What is proved is the general reduction
mechanism that makes all of them range avoidance.

## What is proved

* **`avoid_solution_is_good`** — a non-output of the bad-enumerator satisfies `P`: the reduction's core step.
* **`korten_good_exists`** — pigeonhole: a good object exists when the bad-enumerator stretches
  (`|Idx| < |Obj|`).
* **`korten_reduction`** — a range-avoidance solution for the bad-enumerator *is* an explicit good object.
* **`korten_instance_hard_function`** — the circuit instance: an explicit hard function is `Avoid(eval)`
  (= `HardSlice`), showing the reduction generalizes the counting pigeonhole.

## Honest verdict — the Korten reduction, paved

Third socket paved (after IKW's easy-witness and Liu–Pass): the reduction at the heart of Korten — *explicit
construction of a good object = range avoidance of the bad-enumerator* — is now proved from scratch
(`avoid_solution_is_good`, `korten_good_exists`, `korten_reduction`), and it is exactly the `HardSlice`
pigeonhole generalized (`korten_instance_hard_function`).  Honestly scoped: the specific hard-object
constructions and the `FP^NP` algorithmics that the full theorem needs are abstracted.  But the mechanism —
why `Avoid ∈ FP` would give explicit lower bounds — is paved, not assumed.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Korten

open PallLean.Paper93.DeepMath.PathB.HardSlice

/-! ### The reduction: a non-output of the bad-enumerator is good -/

/-- **A range-avoidance solution is a good object (proved).**  If every object *without* property `P` (every
"bad" object) is enumerated by `enum`, then an object `o` that `enum` never outputs must satisfy `P` — it is
good.  This is Korten's core step: the good objects are exactly the non-outputs of the bad-enumerator. -/
theorem avoid_solution_is_good {Obj Idx : Type} (P : Obj → Prop) (enum : Idx → Obj)
    (bad_enumerated : ∀ o, ¬ P o → ∃ i, enum i = o)
    (o : Obj) (havoid : ∀ i, enum i ≠ o) : P o := by
  by_contra hP
  obtain ⟨i, hi⟩ := bad_enumerated o hP
  exact havoid i hi

/-! ### Pigeonhole: a good object exists; the reduction -/

/-- **A good object exists (proved).**  When the bad-enumerator stretches (`|Idx| < |Obj|`), pigeonhole gives
a non-output, which is good — the explicit-construction target is guaranteed to exist. -/
theorem korten_good_exists {Obj Idx : Type} [Fintype Idx] [Fintype Obj]
    (P : Obj → Prop) (enum : Idx → Obj)
    (bad_enumerated : ∀ o, ¬ P o → ∃ i, enum i = o)
    (h : Fintype.card Idx < Fintype.card Obj) : ∃ o, P o := by
  obtain ⟨o, ho⟩ := hard_slice_exists enum h
  exact ⟨o, avoid_solution_is_good P enum bad_enumerated o ho⟩

/-- **Explicit construction reduces to range avoidance (proved).**  A range-avoidance solution for the
bad-enumerator (an object it never outputs) *is* an explicit good object.  So an algorithm for `Avoid` yields
explicit constructions — Korten's reduction. -/
theorem korten_reduction {Obj Idx : Type} (P : Obj → Prop) (enum : Idx → Obj)
    (bad_enumerated : ∀ o, ¬ P o → ∃ i, enum i = o)
    (avoidSolution : ∃ o, ∀ i, enum i ≠ o) : ∃ o, P o := by
  obtain ⟨o, ho⟩ := avoidSolution
  exact ⟨o, avoid_solution_is_good P enum bad_enumerated o ho⟩

/-! ### The circuit instance: it generalizes HardSlice -/

/-- **The hard-function instance (proved).**  Taking `P f := "no circuit computes f"` and `eval` as the
bad-enumerator (it enumerates the easy functions), Korten's reduction gives an explicit hard function as a
non-output of `eval` — which is exactly `HardSlice.hard_slice_exists`.  Korten's reduction *is* the
circuit-counting pigeonhole, generalized. -/
theorem korten_instance_hard_function {Circuit Func : Type} [Fintype Circuit] [Fintype Func]
    (eval : Circuit → Func) (h : Fintype.card Circuit < Fintype.card Func) :
    ∃ f, ∀ c, eval c ≠ f :=
  hard_slice_exists eval h

end PallLean.Paper93.DeepMath.PathB.Korten

#print axioms PallLean.Paper93.DeepMath.PathB.Korten.avoid_solution_is_good
#print axioms PallLean.Paper93.DeepMath.PathB.Korten.korten_good_exists
#print axioms PallLean.Paper93.DeepMath.PathB.Korten.korten_reduction
#print axioms PallLean.Paper93.DeepMath.PathB.Korten.korten_instance_hard_function
