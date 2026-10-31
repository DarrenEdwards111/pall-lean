import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsBarrier

/-!
# The existence kernel behind `easyWitness`: hard functions exist for free (counting)

`EasyWitnessWiring` left `easyWitness : DerandPIT → NEXP⊆P/poly → HardF` as a socket for the IKW
easy-witness step.  This file discharges its **existential** content unconditionally: a hard function
*exists* purely by counting — the same counting bound (`counting_property_is_large`) that powers the
natural-proofs barrier.  So the real burden of the easy-witness method is **not** existence but
**constructivity**: producing an *explicit* hard function computable in the right resource bound.

* **`exists_hard_function` (proved)** — whenever the cheap class is small enough
  (`2N < #(BoolFun n)`), there is a function `f : BoolFun n` hard for it (`Hard cheap f`).  A hard
  function exists, unconditionally, from the counting bound.
* **`easyWitness_existence_unconditional` (proved)** — hence the *existence* form of the easy-witness
  socket, `DerandPIT → NEXP⊆P/poly → (∃ f, Hard cheap f)`, holds with no hypotheses at all: the hard
  function is there regardless.

**Honest scope.**  This removes the *existence* sub-socket from `easyWitness` and pinpoints exactly
what stays open: the easy-witness / IKW step must produce an **explicit, efficiently-describable** hard
function *from* a derandomized `PIT` and `NEXP ⊆ P/poly` — the constructive content, which is the deep
`NEXP`-strength part and is **not** proved here.  Counting gives abundance; making it constructive is
the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HardExists

open PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier
open PallLean.Paper93.DeepMath.PathB.RestrictedCashout

/-- **A hard function exists, unconditionally (proved).**  If the cheap decider class is small
(`2N < #(BoolFun n)`), the counting bound makes the hardness property large — in particular nonempty —
so some `f : BoolFun n` is hard for every cheap decider. -/
theorem exists_hard_function {n N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n)) :
    ∃ f : BoolFun n, Hard cheap f := by
  classical
  have hlarge := counting_property_is_large cheap hN
  unfold LargeProperty at hlarge
  have hpos : 0 < (Finset.univ.filter (fun f => Hard cheap f)).card := by
    rcases Nat.eq_zero_or_pos (Finset.univ.filter (fun f => Hard cheap f)).card with h0 | hp
    · rw [h0] at hlarge; omega
    · exact hp
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hpos
  exact ⟨f, (Finset.mem_filter.mp hf).2⟩

/-- **The existence form of `easyWitness` is unconditional (proved).**  With `HardF := ∃ f, Hard cheap
f`, the easy-witness implication `DerandPIT → NEXP⊆P/poly → HardF` holds ignoring both inputs — the
hard function is present by counting alone.  So the genuine open content of the easy-witness step is
constructivity, not existence. -/
theorem easyWitness_existence_unconditional {n N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n)) (DerandPIT NEXPinPpoly : Prop) :
    DerandPIT → NEXPinPpoly → (∃ f : BoolFun n, Hard cheap f) :=
  fun _ _ => exists_hard_function cheap hN

end PallLean.Paper93.DeepMath.PathB.HardExists

#print axioms PallLean.Paper93.DeepMath.PathB.HardExists.exists_hard_function
#print axioms PallLean.Paper93.DeepMath.PathB.HardExists.easyWitness_existence_unconditional
