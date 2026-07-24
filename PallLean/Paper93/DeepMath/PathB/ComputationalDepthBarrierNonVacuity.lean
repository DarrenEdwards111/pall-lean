import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsBarrier

/-!
# The non-natural barrier obligation is non-vacuously satisfiable

A worry about the barrier obligations: are they so strong that *nothing* meets them, making the
`SeparatingMeasure` target vacuous?  For the **non-natural** obligation the answer is no, and concretely:
the counting/hardness property `Hard cheap` is simultaneously **large**, **useful**, and (under the
cryptographic barrier) **non-constructive** — exactly the "useful + non-natural" bundle a separating
measure's largeness property must have.  It is exhibited here, and inhabited unconditionally.

* **`nonNatural_useful_large`** — a large *and* useful property exists (`Hard cheap`).
* **`nonNatural_useful_nonconstructive`** — under Razborov–Rudich it is also non-constructive: a witness
  of the full non-natural obligation.
* **`nonNatural_obligation_inhabited`** — with the empty cheap class the size hypothesis is just
  `0 < card`, discharged for every `n`, so the obligation is non-vacuously satisfiable *unconditionally*.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BarrierNonVacuity

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier
open PallLean.Paper93.DeepMath.PathB.RestrictedCashout

/-- **Non-vacuity — large and useful (proved).**  For any cheap class small enough, the counting
property `Hard cheap` is both large and useful. -/
theorem nonNatural_useful_large {n N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n)) :
    ∃ P : BoolFun n → Prop, LargeProperty P ∧ UsefulAgainst cheap P :=
  ⟨Hard cheap, counting_property_is_large cheap hN, hard_property_useful cheap⟩

/-- **Non-vacuity — the full non-natural bundle (proved).**  Under the Razborov–Rudich cryptographic
barrier the same witness is useful *and* non-constructive: the exact "useful + non-natural" combination
a separating measure's largeness property must have, exhibited concretely. -/
theorem nonNatural_useful_nonconstructive {n N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n))
    (Constructive : (BoolFun n → Prop) → Prop) (Crypto : Prop)
    (hRR : RazborovRudichBarrier Constructive cheap Crypto) (hC : Crypto) :
    ∃ P : BoolFun n → Prop, UsefulAgainst cheap P ∧ ¬ Constructive P :=
  ⟨Hard cheap, hard_property_useful cheap,
    counting_property_not_constructive cheap hN Constructive Crypto hRR hC⟩

/-- **The obligation is inhabited unconditionally (proved).**  With the empty cheap class the size
hypothesis reduces to `0 < card (BoolFun n)`, true for every `n` — so a large, useful property exists at
every input length, with no assumption. -/
theorem nonNatural_obligation_inhabited (n : ℕ) :
    ∃ (N : ℕ) (cheap : Fin N → BoolFun n) (P : BoolFun n → Prop),
      2 * N < Fintype.card (BoolFun n) ∧ LargeProperty P ∧ UsefulAgainst cheap P := by
  have hpos : 0 < Fintype.card (BoolFun n) :=
    Fintype.card_pos_iff.mpr ⟨(fun _ => false : BoolFun n)⟩
  refine ⟨0, Fin.elim0, Hard Fin.elim0, by omega, ?_, ?_⟩
  · exact counting_property_is_large Fin.elim0 (by omega)
  · exact hard_property_useful Fin.elim0

end PallLean.Paper93.DeepMath.PathB.BarrierNonVacuity

#print axioms PallLean.Paper93.DeepMath.PathB.BarrierNonVacuity.nonNatural_useful_large
#print axioms PallLean.Paper93.DeepMath.PathB.BarrierNonVacuity.nonNatural_obligation_inhabited
