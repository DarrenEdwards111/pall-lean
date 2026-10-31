import Mathlib.Data.Nat.Basic

/-!
# The conservation-law spec for `Q` — a hardness charge no rewrite can drain

`PiStarSpec` left one gap: the rank measure must be **representation-independent** — the same for every
way of writing a function ((I1) / F2).  This file formalizes exactly that, as a **conserved charge**.

The picture: functions can be written many ways (`Rep`); each writing has a representation-dependent
rank `rrank : Rep → ℕ` (the SPDP rank).  A **charge** `Q : Fn → ℕ` lives on the *function itself* — so it
is representation-independent **by type**.  The content is the **conservation law** relating it to every
writing.

## The spec (structure `ConservedCharge`)

* `Q : Fn → ℕ` — the charge, on functions.
* **(C1) conservation** — `∀ f r, computes r f → Q f ≤ rrank r`: the charge is a lower bound valid for
  **every** representation.  No rewrite can drain the rank below `Q` — this is the conservation law.
* **(C3) full on SAT** — `high ≤ Q sat`.
* **(C4) empty on easy** — `∀ f, Easy f → Q f ≤ low`.
* **(C5) gap** — `low < high`.

## What the spec delivers (proved)

* **`charge_bounds_every_rep`** — the heart, and exactly (I1)/F2: *every* representation of SAT has rank
  `≥ high`.  No clever writing lowers SAT below the charge.  Representation-independence, delivered.
* **`charge_separates`** — `¬ Easy sat`: SAT is not easy.  The charge separates.
* **`charge_forces_non_natural`** — under the natural-proofs barrier + crypto, `Q` is not efficiently
  computable.  The charge cannot be natural (forced, as for `Π★`).

## Honest scope

The canonical conserved charge is the **true representation-floor** `Q f = ` the minimum `rrank` over all
writings of `f` — that is representation-independent by construction (it is `cbudget`).  The entire
difficulty is proving **(C3)** for it: that the floor of SAT is high, i.e. *no* writing of SAT is cheap.
That is `charge_bounds_every_rep` read as a demand, and it is `P ≠ NP`.  This file **specifies** the
charge and proves the spec ⟹ the separation; it does **not** construct a `Q` satisfying (C1)+(C3), which
is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ConservedChargeSpec

/-- A **conserved charge**: a representation-independent hardness measure `Q` on functions, lower-bounding
the rank of every writing (the conservation law C1), full on SAT, empty on easy functions, with a gap. -/
structure ConservedCharge (Fn Rep : Type) (computes : Rep → Fn → Prop)
    (rrank : Rep → ℕ) (Easy : Fn → Prop) (sat : Fn) where
  /-- the charge, on the function itself (representation-independent by type). -/
  Q : Fn → ℕ
  /-- the empty threshold. -/
  low : ℕ
  /-- the full threshold. -/
  high : ℕ
  /-- a genuine gap. -/
  gap : low < high
  /-- **conservation (C1)**: the charge lower-bounds the rank of *every* representation — no rewrite
  drains it below `Q`. -/
  conserved : ∀ f r, computes r f → Q f ≤ rrank r
  /-- **(C3)** the charge is full on SAT. -/
  high_on_sat : high ≤ Q sat
  /-- **(C4)** the charge is empty on easy functions. -/
  low_on_easy : ∀ f, Easy f → Q f ≤ low

variable {Fn Rep : Type} {computes : Rep → Fn → Prop} {rrank : Rep → ℕ}
  {Easy : Fn → Prop} {sat : Fn}

/-- **The conservation law IS representation-independence — (I1)/F2 delivered (proved).**  Every
representation of SAT has rank `≥ high`: no clever writing can lower SAT below the charge.  This is
exactly the floor-clearing / normal-form-invariance step the whole map reduced to. -/
theorem charge_bounds_every_rep (cc : ConservedCharge Fn Rep computes rrank Easy sat)
    (r : Rep) (hr : computes r sat) : cc.high ≤ rrank r :=
  le_trans cc.high_on_sat (cc.conserved sat r hr)

/-- **The charge separates (proved).**  A conserved charge that is full on SAT and empty on easy
functions forces `SAT` not to be easy: `high ≤ Q sat` and `Easy sat → Q sat ≤ low < high` collide. -/
theorem charge_separates (cc : ConservedCharge Fn Rep computes rrank Easy sat) : ¬ Easy sat := by
  intro h
  have hlo := cc.low_on_easy sat h
  have hhi := cc.high_on_sat
  have hg := cc.gap
  omega

/-- The natural-proofs barrier for a charge: an efficiently computable charge is a natural property and
cannot exist under a crypto assumption. -/
def ChargeBarrier (Fn Rep : Type) (computes : Rep → Fn → Prop) (rrank : Rep → ℕ)
    (Easy : Fn → Prop) (sat : Fn) (Efficient : (Fn → ℕ) → Prop) (Crypto : Prop) : Prop :=
  ∀ cc : ConservedCharge Fn Rep computes rrank Easy sat, Efficient cc.Q → Crypto → False

/-- **The charge is forced non-natural (proved).**  Under the barrier and crypto, no conserved charge is
efficiently computable.  Like `Π★`, a working `Q` must be non-natural. -/
theorem charge_forces_non_natural {Efficient : (Fn → ℕ) → Prop} {Crypto : Prop}
    (barrier : ChargeBarrier Fn Rep computes rrank Easy sat Efficient Crypto) (hC : Crypto)
    (cc : ConservedCharge Fn Rep computes rrank Easy sat) : ¬ Efficient cc.Q :=
  fun he => barrier cc he hC

end PallLean.Paper93.DeepMath.PathB.ConservedChargeSpec

#print axioms PallLean.Paper93.DeepMath.PathB.ConservedChargeSpec.charge_bounds_every_rep
#print axioms PallLean.Paper93.DeepMath.PathB.ConservedChargeSpec.charge_separates
#print axioms PallLean.Paper93.DeepMath.PathB.ConservedChargeSpec.charge_forces_non_natural
