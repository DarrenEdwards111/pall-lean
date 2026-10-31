import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConservedChargeSpec

/-!
# Capping the Lagrangian at the min-floor makes F2 free — the whole problem is C3

The synthesis: cap the N-Frame Noether charge at `EXP` (avoid `L_H`) and use it for F2.  The EXP-capped
conserved charge is the **min-floor** — `floor f = ` the minimum rank over all representations of `f`,
i.e. `cbudget`.  Its conservation law (C1) — *representation-independence*, the (I1) step that trapped
the `p-vs-np1` paper — is **free**, because the minimum over representations is representation-independent
by definition.  There is no normal-form invariance to prove.

So building a separating charge from the min-floor needs only:

* **C4** — low on easy functions (the P-side upper bound: a P-decidable function has a cheap
  representation, so its floor is low — the *easy* direction);
* **C3** — high on SAT (`high ≤ floor sat`), i.e. **every** representation of SAT is expensive:
  `cbudget(SAT)` is superpolynomial — which is `cost_super`.

## What is proved

* **`floor_gives_conserved_charge`** — the min-floor's conservation law plugs straight into
  `ConservedCharge.conserved`; F2/(I1) is discharged for free, leaving only C3 and C4.
* **`floor_separation_is_C3`** — with C4 and C3, the min-floor charge separates: `¬ Easy sat`.
* **`C3_means_every_rep_expensive`** — C3 unpacked: `high ≤ floor sat` means **every** representation of
  SAT has rank `≥ high`.  This is exactly `cost_super` — no writing of SAT is cheap.

## Honest scope

Darren's move is correct and it is a genuine simplification: the EXP cap avoids hypercomputation, and the
min-floor delivers F2/(I1)/representation-independence for nothing — pruning the branch that stalled the
paper.  But it does **not** cross the wall: the whole problem collapses to **C3 = `cost_super`**, the same
one inequality the entire map converges on.  F2 was never the hard part; C3 is, and it is untouched.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MinFloorCharge

open PallLean.Paper93.DeepMath.PathB.ConservedChargeSpec

variable {Fn Rep : Type} {computes : Rep → Fn → Prop} {rrank : Rep → ℕ}

/-- The **min-floor charge**: `floor f` is the minimum rank over all representations of `f` (`= cbudget`).
Representation-independent by construction — a lower bound valid for every writing (`is_lower`, the
conservation law C1) that is actually achieved (`is_achieved`, so it is the true minimum). -/
structure FloorCharge (Fn Rep : Type) (computes : Rep → Fn → Prop) (rrank : Rep → ℕ) where
  /-- the floor value on each function. -/
  floor : Fn → ℕ
  /-- **C1 for free**: the floor lower-bounds every representation's rank. -/
  is_lower : ∀ f r, computes r f → floor f ≤ rrank r
  /-- the floor is achieved by some representation — it is the true minimum (`cbudget`). -/
  is_achieved : ∀ f, ∃ r, computes r f ∧ rrank r = floor f

/-- **The conservation law is free — F2/(I1) discharged (proved).**  The min-floor's `is_lower` is exactly
`ConservedCharge.conserved`.  So a separating charge from the min-floor needs only C3 (`hi`) and C4
(`lo`) — representation-independence costs nothing. -/
def floor_gives_conserved_charge (fc : FloorCharge Fn Rep computes rrank)
    (Easy : Fn → Prop) (sat : Fn) (low high : ℕ) (gap : low < high)
    (hi : high ≤ fc.floor sat) (lo : ∀ f, Easy f → fc.floor f ≤ low) :
    ConservedCharge Fn Rep computes rrank Easy sat where
  Q := fc.floor
  low := low
  high := high
  gap := gap
  conserved := fc.is_lower
  high_on_sat := hi
  low_on_easy := lo

/-- **The min-floor charge separates, given C3 and C4 (proved).**  With the easy P-side bound (C4, `lo`)
and the SAT floor bound (C3, `hi`), the min-floor charge forces `¬ Easy sat`. -/
theorem floor_separation_is_C3 (fc : FloorCharge Fn Rep computes rrank)
    (Easy : Fn → Prop) (sat : Fn) (low high : ℕ) (gap : low < high)
    (lo : ∀ f, Easy f → fc.floor f ≤ low) (hi : high ≤ fc.floor sat) : ¬ Easy sat :=
  charge_separates (floor_gives_conserved_charge fc Easy sat low high gap hi lo)

/-- **C3 IS the circuit lower bound (proved).**  `high ≤ floor sat` means **every** representation of SAT
has rank `≥ high` — no writing of SAT is cheap, i.e. `cbudget(SAT) ≥ high`.  This is `cost_super`, and it
is the entire remaining task once the min-floor makes F2 free. -/
theorem C3_means_every_rep_expensive (fc : FloorCharge Fn Rep computes rrank) (sat : Fn) (high : ℕ)
    (hi : high ≤ fc.floor sat) (r : Rep) (hr : computes r sat) : high ≤ rrank r :=
  le_trans hi (fc.is_lower sat r hr)

end PallLean.Paper93.DeepMath.PathB.MinFloorCharge

#print axioms PallLean.Paper93.DeepMath.PathB.MinFloorCharge.floor_gives_conserved_charge
#print axioms PallLean.Paper93.DeepMath.PathB.MinFloorCharge.floor_separation_is_C3
#print axioms PallLean.Paper93.DeepMath.PathB.MinFloorCharge.C3_means_every_rep_expensive
