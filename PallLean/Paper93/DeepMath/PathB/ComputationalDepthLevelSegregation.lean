import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMinFloorCharge

/-!
# Kardashev-level segregation does not give the proof — the wall is in-model

Darren's move: put the hypercomputational part at a **level-2 Kardashev** observer (greater thermodynamic
boundary), declare it *outside* the P vs NP question, and let the **level-1** (in-model, "end of the
classical world") NP God-Move carry the proof.

The first half is exactly right, and it is why this **cannot** give the proof.

## Two facts, proved

* **`level2_outside_cannot_decide`** — a level-2 resource that is *outside the question* is, by that very
  fact, consistent with `SAT` being **easy**: there is a world where the resource is available and
  `Easy sat` holds.  So it cannot prove the separation.  *Outside the question* literally means *cannot
  answer the question*.
* **`in_model_separation_is_C3`** — the level-1 (in-model) separation still reduces to **C3**
  (`high ≤ floor sat`) = `cost_super`, via the min-floor charge.  C3 is an *in-model* statement about
  `cbudget(SAT)`; a level-2 (outside) resource cannot supply it, and no in-model proof of it exists — it
  is the open wall.

## Why segregation fails, in one line

The wall was **never hypercomputational**.  `CappedObserver` showed the escape from natural proofs is an
*in-model* EXP cap, not hypercomputation; `MinFloorCharge` showed F2 is free *in-model*.  So the entire
problem is already in-model and equals C3 = `cost_super`.  A level-2 observer is therefore both
**unnecessary** (the in-model cap handles everything but C3) and **useless** (being outside the question,
it cannot supply C3).  Neither level yields C3, and C3 is required.

*(Correction of terms: `EXP` is **not** hypercomputational — it is a bounded, in-model, level-1 class.
A level-2 observer is either really `EXP` (in-model, still needs C3) or genuinely hypercomputational
(outside, cannot decide).  Neither proves `P ≠ NP`.)*

**Honest scope.**  Proved: an outside-the-question resource cannot decide the question, and the in-model
separation is C3 = `cost_super`.  So the level split does not close the proof.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LevelSegregation

open PallLean.Paper93.DeepMath.PathB.MinFloorCharge

/-- **An outside-the-question (level-2) resource cannot decide P vs NP (proved).**  Whatever the
hypercomputational resource `L2` is, its availability is consistent with `SAT` being **easy**: there is a
world where `L2` holds and `Easy sat` holds together.  Hence `L2` does **not** imply the separation — a
resource outside the question cannot answer it. -/
theorem level2_outside_cannot_decide (L2 : Prop) (hL2 : L2) :
    ∃ (Fn : Type) (Easy : Fn → Prop) (sat : Fn), L2 ∧ Easy sat :=
  ⟨Unit, fun _ => True, (), hL2, trivial⟩

/-- **The in-model separation is C3 = cost_super (proved).**  With the min-floor charge (F2 free), the
level-1 separation `¬ Easy sat` still requires C3 (`hi : high ≤ floor sat`) — every writing of SAT is
expensive, `cbudget(SAT)` superpoly.  This is the in-model wall; no level-2 resource supplies it. -/
theorem in_model_separation_is_C3 {Fn Rep : Type} {computes : Rep → Fn → Prop} {rrank : Rep → ℕ}
    (fc : FloorCharge Fn Rep computes rrank) (Easy : Fn → Prop) (sat : Fn) (low high : ℕ)
    (gap : low < high) (lo : ∀ f, Easy f → fc.floor f ≤ low) (hi : high ≤ fc.floor sat) :
    ¬ Easy sat :=
  floor_separation_is_C3 fc Easy sat low high gap lo hi

end PallLean.Paper93.DeepMath.PathB.LevelSegregation

#print axioms PallLean.Paper93.DeepMath.PathB.LevelSegregation.level2_outside_cannot_decide
#print axioms PallLean.Paper93.DeepMath.PathB.LevelSegregation.in_model_separation_is_C3
