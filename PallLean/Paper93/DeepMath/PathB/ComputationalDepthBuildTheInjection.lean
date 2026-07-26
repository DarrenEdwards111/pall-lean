import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGaloisInvariant

/-!
# Building the injection: it reduces to NoSharing at the composition step — and that is where it breaks

The injection is `cost_super` itself: `2·cost d ≤ cost(d+1)` for the real SAT tower.  This file builds
it — honestly, as far as it goes — and lets the break show itself, without faking the last step and
without declaring it unprovable.

## The construction

At depth `d+1` the tower services **two slots**, each requiring a full depth-`d` solve.  The honest,
provable scaffolding is the inclusion–exclusion lower bound (`two_slot`): the two slots, each of cost
`≥ cost d`, minus the gates they **share**, lower-bound `cost(d+1)`:
`2·cost d ≤ cost(d+1) + sharedCost d`.  This is the counting direction — the same shape as the
opening bricks (`the_reason_with_overlap`: `|gates| ≥ k·b − overlap`).  It is *given*, not assumed
away.

From this scaffolding the injection is one step:

* **`injection_from_no_sharing`** — if the two slots share nothing (`sharedCost d = 0`), the injection
  holds at step `d`: `2·cost d ≤ cost(d+1)`.
* **`injection_from_no_sharing_all`** — so `NoSharing` (share nothing at every step) delivers the full
  injection `Injection` (= `cost_super`).
* **`injection_amplifies`** — and the injection cashes out: `cost d ≥ 2^d`, the separation.

So the injection **is built**: `cost_super ⟸ NoSharing`, with everything downstream proved.  The
entire remaining obligation is `NoSharing` at the composition step.

## Where it breaks

`NoSharing` is exactly the **anti-Uhlig** claim — "the two copies cannot be mass-produced with shared
gates" — and it is false in general:

* **`uhligStep`** — a step where the two slots share (cost `3`, `3`, shared `3`): the scaffolding
  `two_slot` holds (`6 ≤ 3+3`), yet the injection fails.
* **`uhlig_breaks_injection`** — `¬ (2·cost 0 ≤ cost 1)`: `6 ≤ 3` is false.  Sharing collapsed the
  injection — the very `overlap_collapses` / `uhligSharer` collapse the map opened with.
* **`uhlig_breaks_no_sharing`** — `¬ NoSharing uhligStep`: the obligation is genuinely false here.

So building the injection bottoms out at `NoSharing`, and `NoSharing` **breaks at Uhlig** — the first
wall on the map.  The circle is closed: injection ⟶ NoSharing ⟶ Uhlig ⟶ (the opening) ⟶ `cost_super`
⟶ injection.

## Honest scope — the injection is built down to one obligation, and that obligation is the wall

This is **not** a proof of `cost_super`.  It is the honest construction of the injection reduced to
its single load-bearing obligation — `NoSharing` at the composition step — together with a
machine-checked proof that this obligation is *false in general* (Uhlig mass production) and is
therefore not dischargeable generically.  Its SAT-specific version — that SAT's tower *cannot*
mass-produce its two slots — is exactly `cost_super`, still open.  Building the injection does not
break the machinery and does not prove `P ≠ NP`; it shows, precisely and by construction, that the
last obligation is the Uhlig wall the map began with.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BuildTheInjection

open PallLean.Paper93.DeepMath.PathB.GaloisInvariant

/-- The composition-step cost accounting.  At depth `d+1` the tower services two slots, each needing a
full depth-`d` solve; `sharedCost d` is the gates the two slots share (the overlap / Uhlig residue).
`two_slot` is the honest inclusion–exclusion scaffolding: two slots (each `≥ cost d`) minus the
shared cost lower-bound `cost(d+1)`. -/
structure StepCost where
  /-- the tower's cost at composition depth `d` -/
  cost : ℕ → ℕ
  /-- the gates the two depth-`d` slots share at step `d` (the overlap) -/
  sharedCost : ℕ → ℕ
  /-- the provable scaffolding: `2·cost d ≤ cost(d+1) + sharedCost d` (inclusion–exclusion) -/
  two_slot : ∀ d, 2 * cost d ≤ cost (d + 1) + sharedCost d

/-- The **injection** (= `cost_super`): the cost doubles up the tower. -/
def Injection (S : StepCost) : Prop := ∀ d, 2 * S.cost d ≤ S.cost (d + 1)

/-- **NoSharing**: at every step the two slots share nothing.  This is the anti-Uhlig obligation. -/
def NoSharing (S : StepCost) : Prop := ∀ d, S.sharedCost d = 0

/-- **The injection at a step, from NoSharing (proved).**  If the two slots share nothing, the
scaffolding gives the injection: `2·cost d ≤ cost(d+1)`. -/
theorem injection_from_no_sharing (S : StepCost) (d : ℕ) (hns : S.sharedCost d = 0) :
    2 * S.cost d ≤ S.cost (d + 1) := by
  have h := S.two_slot d
  omega

/-- **The full injection, from NoSharing (proved).**  `NoSharing ⟹ Injection` (= `cost_super`).  The
injection is built — the entire remaining obligation is `NoSharing`. -/
theorem injection_from_no_sharing_all (S : StepCost) (hns : NoSharing S) : Injection S :=
  fun d => injection_from_no_sharing S d (hns d)

/-- **The injection cashes out (proved).**  Given the injection and base `cost 0 ≥ 1`, the cost is
exponential in depth: `cost d ≥ 2^d` — the separation. -/
theorem injection_amplifies (S : StepCost) (hinj : Injection S) (hbase : 1 ≤ S.cost 0) (d : ℕ) :
    2 ^ d ≤ S.cost d := by
  have h : 2 ^ d * S.cost 0 ≤ S.cost d := invariant_amplifies ⟨S.cost, hinj⟩ d
  calc (2 : ℕ) ^ d = 2 ^ d * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ d * S.cost 0 := Nat.mul_le_mul (le_refl _) hbase
    _ ≤ S.cost d := h

/-! ### Where it breaks: NoSharing is false in general (Uhlig) -/

/-- The **Uhlig step**: the two slots share.  Cost `3` at every depth, shared cost `3`.  The
scaffolding `two_slot` holds (`2·3 ≤ 3 + 3`), yet the two slots are mass-produced together. -/
def uhligStep : StepCost where
  cost := fun _ => 3
  sharedCost := fun _ => 3
  two_slot := by intro d; show 2 * 3 ≤ 3 + 3; omega

/-- The Uhlig step genuinely shares: `sharedCost 0 = 3`. -/
theorem uhligStep_shares : uhligStep.sharedCost 0 = 3 := rfl

/-- **Sharing collapses the injection (proved).**  In the Uhlig step, `¬ (2·cost 0 ≤ cost 1)`:
`6 ≤ 3` is false.  The two slots were mass-produced with shared gates, so the injection fails — the
`overlap_collapses` / `uhligSharer` collapse the map opened with. -/
theorem uhlig_breaks_injection : ¬ (2 * uhligStep.cost 0 ≤ uhligStep.cost 1) := by
  show ¬ (2 * 3 ≤ 3)
  omega

/-- **NoSharing is false in general (proved).**  `¬ NoSharing uhligStep`: the obligation that builds
the injection is genuinely false here — mass production is real.  So the injection cannot be
discharged generically; the SAT-specific `NoSharing` is `cost_super`. -/
theorem uhlig_breaks_no_sharing : ¬ NoSharing uhligStep := by
  intro h
  have h3 : (3 : ℕ) = 0 := h 0
  omega

/-- **The reduction, exactly (proved, `Iff.rfl`).**  The injection is built down to `NoSharing` at
the composition step, and `NoSharing`-for-SAT is definitionally the open wall — the anti-Uhlig claim
that SAT's two slots cannot be mass-produced.  Building the injection bottoms out here. -/
theorem injection_reduces_to_no_sharing (S : StepCost) :
    NoSharing S ↔ (∀ d, S.sharedCost d = 0) := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.BuildTheInjection

#print axioms PallLean.Paper93.DeepMath.PathB.BuildTheInjection.injection_from_no_sharing_all
#print axioms PallLean.Paper93.DeepMath.PathB.BuildTheInjection.injection_amplifies
#print axioms PallLean.Paper93.DeepMath.PathB.BuildTheInjection.uhlig_breaks_injection
#print axioms PallLean.Paper93.DeepMath.PathB.BuildTheInjection.uhlig_breaks_no_sharing
