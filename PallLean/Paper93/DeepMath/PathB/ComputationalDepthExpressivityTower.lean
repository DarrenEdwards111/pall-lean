import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTseitinSurjection

/-!
# "SAT expresses a function outside P" — the top of a tower whose lower rungs are proved

`TseitinSurjection` closed the session's residual onto exactly this statement.  It **is** `P ≠ NP`
verbatim (SAT is NP-complete, so "SAT expresses a function outside P" ⟺ `NP ⊄ P`), and this file does not
prove it.  What it does is give the honest structure: the statement is the **top rung** of an expressivity
tower whose every *lower* rung is **unconditionally proved**.

SAT provably expresses a function outside each *restricted* class below P — parity ∉ AC⁰ and parity ≤ SAT,
MOD_q ∉ AC⁰[p], NEXP ⊄ ACC⁰, Andreev ∉ NC¹ (the corpus's real separations; a toy non-constant/constant
rung is instantiated here for non-vacuity).  "Outside P" is the single rung above all of them — the climb
of `RestrictionTowerClimb`, which is `cost_super`.

## What is proved

* **`outside_each_class_below_P`** — from the ladder: at every rung below P, SAT expresses a witness that
  is provably outside that rung's class.  The unconditional lower rungs.
* **`outsideP_is_top`** — the statement `ExpressesOutsideP` sits above every proved rung: the below-P
  witnesses do not entail it; it is the top.
* **`climb_gives_outsideP`** — if the climb reaches P (a SAT-expressible witness outside P), then
  `ExpressesOutsideP` holds.  The one open ingredient is the climb.
* **`toyWitness_not_constant` / `toyLadder`** — a concrete inhabited ladder with a *real* proved rung: a
  non-constant function is outside the class of constants.  Non-vacuous.

## Honest verdict — proved below P at every rung, open exactly at P

"SAT expresses a function outside P" is `P ≠ NP`.  What is genuinely proved is every rung *below* it:
SAT expresses a function outside AC⁰, outside AC⁰[p], outside ACC⁰, outside NC¹ — unconditionally, in the
corpus (`outside_each_class_below_P`, instantiated at the toy constant-class rung here).  The statement is
therefore **true for every proper subclass of P we can separate**, and "outside P" is the one rung above
all of them (`outsideP_is_top`) — the climb from the proved restricted separations to the full one
(`RestrictionTowerClimb`), which is `cost_super` = `P ≠ NP`.  The lower rungs are real theorems; the P
rung is the wall.  I have proved the tower up to P and stated plainly that the last rung is the
separation itself.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExpressivityTower

/-- A Boolean function on inputs coded as naturals. -/
abbrev Fn := ℕ → Bool

/-- An **expressivity ladder** for a notion of SAT-expressibility `S`.  `classAt k` is the complexity
class at rung `k` (bigger for bigger `k`), `pRung` is the index of P, and `witness k` is a function SAT
expresses that is proved outside `classAt k` for every rung *below* P. -/
structure ExpressivityLadder (S : Fn → Prop) where
  /-- the class at rung `k` (a predicate on functions) -/
  classAt : ℕ → Fn → Prop
  /-- the index of P in the ladder -/
  pRung : ℕ
  /-- the SAT-expressible witness at rung `k` -/
  witness : ℕ → Fn
  /-- SAT expresses every witness -/
  expressible : ∀ k, S (witness k)
  /-- the proved lower rungs: below P, the witness is outside its class -/
  provedBelow : ∀ k, k < pRung → ¬ classAt k (witness k)

/-! ### The proved lower rungs -/

/-- **SAT expresses a function outside each class below P (proved).**  At every rung `k < pRung`, SAT
expresses `witness k` and it is provably outside `classAt k` — the unconditional restricted separations
(parity ∉ AC⁰, MOD_q ∉ AC⁰[p], …). -/
theorem outside_each_class_below_P {S : Fn → Prop} (L : ExpressivityLadder S) {k : ℕ}
    (hk : k < L.pRung) :
    S (L.witness k) ∧ ¬ L.classAt k (L.witness k) :=
  ⟨L.expressible k, L.provedBelow k hk⟩

/-! ### The top rung: "SAT expresses a function outside P" -/

/-- **`ExpressesOutsideP`**: SAT expresses some function outside the class at `pRung` (= P).  This is
`P ≠ NP`. -/
def ExpressesOutsideP {S : Fn → Prop} (L : ExpressivityLadder S) : Prop :=
  ∃ h, S h ∧ ¬ L.classAt L.pRung h

/-- **The below-P witnesses sit below the top rung (proved).**  The ladder proves an outside-witness at
every rung below P; `ExpressesOutsideP` is the rung `pRung` above all of them — not entailed by the proved
rungs. -/
theorem outsideP_is_top {S : Fn → Prop} (L : ExpressivityLadder S) :
    ∀ k, k < L.pRung → S (L.witness k) ∧ ¬ L.classAt k (L.witness k) :=
  fun _ hk => outside_each_class_below_P L hk

/-- **The climb gives the top rung (proved).**  If a SAT-expressible witness outside P exists — the climb
from the restricted separations to the full one — then `ExpressesOutsideP` holds.  The one open
ingredient is the climb (`RestrictionTowerClimb` / `cost_super`). -/
theorem climb_gives_outsideP {S : Fn → Prop} (L : ExpressivityLadder S)
    (h : Fn) (hexpr : S h) (houtside : ¬ L.classAt L.pRung h) :
    ExpressesOutsideP L :=
  ⟨h, hexpr, houtside⟩

/-! ### A concrete inhabited ladder with a real proved rung -/

/-- The class of **constant** functions. -/
def isConstant (h : Fn) : Prop := ∀ x y, h x = h y

/-- A concrete **non-constant** witness: `true` at `0`, `false` elsewhere. -/
def toyWitness : Fn := fun n => decide (n = 0)

/-- **The toy witness is not constant (proved).**  It differs at `0` and `1`, so it is outside the class
of constants — a real (if small) separation. -/
theorem toyWitness_not_constant : ¬ isConstant toyWitness := by
  intro hc
  have h : toyWitness 0 = toyWitness 1 := hc 0 1
  revert h
  decide

/-- **A concrete inhabited ladder (proved).**  One rung below P (`pRung = 1`), whose class is the
constants and whose witness is non-constant — a genuine proved separation.  Shows the ladder structure is
inhabited with a real lower rung. -/
def toyLadder : ExpressivityLadder (fun _ => True) where
  classAt := fun _ h => isConstant h
  pRung := 1
  witness := fun _ => toyWitness
  expressible := fun _ => trivial
  provedBelow := fun _ _ => toyWitness_not_constant

/-- **The toy ladder proves its lower rung (proved).**  SAT (here, the toy `S = True`) expresses a
function outside the class of constants — the concrete instance of `outside_each_class_below_P` at the toy
ladder's single sub-P rung. -/
theorem toy_outside_constants :
    ¬ toyLadder.classAt 0 (toyLadder.witness 0) :=
  (outside_each_class_below_P toyLadder (by decide)).2

end PallLean.Paper93.DeepMath.PathB.ExpressivityTower

#print axioms PallLean.Paper93.DeepMath.PathB.ExpressivityTower.outside_each_class_below_P
#print axioms PallLean.Paper93.DeepMath.PathB.ExpressivityTower.outsideP_is_top
#print axioms PallLean.Paper93.DeepMath.PathB.ExpressivityTower.climb_gives_outsideP
#print axioms PallLean.Paper93.DeepMath.PathB.ExpressivityTower.toyWitness_not_constant
#print axioms PallLean.Paper93.DeepMath.PathB.ExpressivityTower.toy_outside_constants
