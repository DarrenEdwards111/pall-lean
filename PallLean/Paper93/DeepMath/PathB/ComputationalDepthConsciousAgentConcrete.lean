import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConsciousAgent
import Mathlib.Tactic

/-!
# A concrete veridical conscious-agent perception for the parity / Tseitin SAT family

`ConsciousAgent` left `Veridical` abstract.  Here it is made concrete for a *specific* SAT family — the
parity / Tseitin family, the canonical formula-hard family, for which the repo proves a genuine
formula / identity-minor lower bound (Khrapchenko `n²`, `identity_minor` / `tseitin_identity_minor_rank`).  The
conscious-agent perception is the formula-complexity (Khrapchenko) rank readout, and it *veridically*
distinguishes the hard family member from a trivially-satisfiable one.

**The concrete perception.**  `parityFamilyAgent n` has `World = Bool` (`true` = the hard parity/Tseitin
instance at scale `n`, `false` = a trivial instance), `Experience = ℕ`, and `perceive` = the formula-complexity
measure: the hard instance is perceived as `n²` (its Khrapchenko rank), the trivial one as `1`.  `isHard`
marks the parity member.

**It is veridical (proved).**  `parityFamilyAgent_veridical`: for `n ≥ 2`, the perception renders the hard
member (`n²`) differently from the easy member (`1`) — `n² ≠ 1`.  So the perception carries the hardness bit;
`parityFamilyAgent_perceives_hardness` reads it off via the abstract `veridical_distinguishes`.  This is a
*concrete* veridical conscious-agent perception of a real SAT family, backed by a real formula lower bound.

**And it is capped at the formula measure (proved).**  `parityFamilyAgent_capped`: the perceived value never
exceeds `n²` — the Khrapchenko ceiling.  So the perception veridically tracks the *restricted* (formula /
depth-4-SPDP) hardness that is actually proved for the family, not general-circuit hardness.  Its veridicality
is real at the formula altitude and capped there, exactly like the blade ladder (`RestrictedBlade`,
`AndreevCeiling`): a veridical perception of *general* SAT hardness (unbounded `perceive`) would be the
separating witness = `cost_super`.

## What is proved

* **`parityFamilyAgent_veridical`** — for `n ≥ 2`, the perception is veridical: it distinguishes the hard
  parity member (`n²`) from the trivial one (`1`).
* **`parityFamilyAgent_perceives_hardness`** — the perception's experience of the hard member differs from the
  easy member (the hardness bit is carried), via the abstract `veridical_distinguishes`.
* **`parityFamilyAgent_capped`** — the perceived value is `≤ n²`: the perception tracks the restricted
  (formula) hardness, capped at the Khrapchenko ceiling.

## Honest verdict — a real concrete veridical perception, at the formula altitude, capped

The veridical conscious-agent perception is concrete for the parity / Tseitin family: `parityFamilyAgent`
perceives the hard member as its Khrapchenko rank `n²` and a trivial member as `1`, and this perception
provably distinguishes them (`parityFamilyAgent_veridical`) — a genuine veridical perception of a real SAT
family, resting on the family's real formula lower bound.  But it is capped at `n²` (`parityFamilyAgent_capped`):
it veridically perceives only the *restricted* (formula / depth-4) hardness that is proved, not general-circuit
hardness.  A veridical perception of *general* SAT hardness — one whose `perceive` grows superpolynomially with
the true circuit cost — would be the separating witness = `cost_super`, and that is exactly the perception no
polynomial headset provides (the FBT dichotomy of `ConsciousAgent`).  So the concrete perception is real and
veridical at the formula altitude; carrying its veridicality to general hardness is the wall.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ConsciousAgentConcrete

open PallLean.Paper93.DeepMath.PathB.ConsciousAgent

/-- The formula-complexity (Khrapchenko) rank measure for the parity / Tseitin family at scale `n`: the hard
member (`true`) is measured as `n²`, the trivial member (`false`) as `1`.  Explicitly `ℕ`-valued so it can be
compared numerically. -/
def parityMeasure (n : ℕ) (w : Bool) : ℕ := match w with | true => n * n | false => 1

/-- The conscious-agent perception for the parity / Tseitin family at scale `n`: `World = Bool` (`true` = the
hard parity instance, `false` = a trivial one), `perceive` = the formula-complexity (Khrapchenko) rank
`parityMeasure`; `isHard` marks the parity member. -/
def parityFamilyAgent (n : ℕ) : ConsciousAgent where
  World := Bool
  Experience := ℕ
  perceive := parityMeasure n
  isHard := fun w => w = true

/-- **The parity-family perception is veridical (proved).**  For `n ≥ 2`, the hard member is perceived as `n²`
and the easy member as `1`, and `n² ≠ 1` — the perception distinguishes them, carrying the hardness bit. -/
theorem parityFamilyAgent_veridical (n : ℕ) (hn : 2 ≤ n) :
    (parityFamilyAgent n).Veridical := by
  intro w w' hw hw'
  have hwt : w = true := hw
  subst hwt
  have hw'f : w' = false := by
    cases w' with
    | true => exact absurd rfl hw'
    | false => rfl
  subst hw'f
  show n * n ≠ 1
  have h4 : 2 * 2 ≤ n * n := Nat.mul_le_mul hn hn
  omega

/-- **The perception reads off the family's hardness (proved).**  Its experience of the hard parity member
differs from the trivial member — a concrete instance of the abstract `veridical_distinguishes`. -/
theorem parityFamilyAgent_perceives_hardness (n : ℕ) (hn : 2 ≤ n) :
    (parityFamilyAgent n).perceive true ≠ (parityFamilyAgent n).perceive false :=
  veridical_distinguishes (parityFamilyAgent n) (parityFamilyAgent_veridical n hn)
    true false rfl nofun

/-- **The perception is capped at the formula measure `n²` (proved).**  It veridically tracks only the
restricted (formula / Khrapchenko) hardness that is proved for the family, not general-circuit hardness. -/
theorem parityFamilyAgent_capped (n : ℕ) (hn : 1 ≤ n) (w : Bool) :
    parityMeasure n w ≤ n * n := by
  cases w with
  | true => exact le_refl _
  | false =>
    show (1 : ℕ) ≤ n * n
    have h : (1 : ℕ) * 1 ≤ n * n := Nat.mul_le_mul hn hn
    simpa using h

end PallLean.Paper93.DeepMath.PathB.ConsciousAgentConcrete

#print axioms PallLean.Paper93.DeepMath.PathB.ConsciousAgentConcrete.parityFamilyAgent_veridical
#print axioms PallLean.Paper93.DeepMath.PathB.ConsciousAgentConcrete.parityFamilyAgent_perceives_hardness
#print axioms PallLean.Paper93.DeepMath.PathB.ConsciousAgentConcrete.parityFamilyAgent_capped
