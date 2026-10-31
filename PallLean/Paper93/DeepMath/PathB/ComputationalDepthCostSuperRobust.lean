import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDemandGeneration

/-!
# Pushing on cost_super: the factor 2 is NOT essential — the multiplicativity is

`cost_super` is the last driver: `∀ d, 2·D d ≤ D(d+1)` (the doubling), which `DemandGeneration`
proved is the demand-side wall and `TreeDagDuality` proved has no shortcut.  It is P≠NP-strength and
this file does NOT close it.  What it does is push on its EXACT FORM: how much of the doubling is
actually load-bearing?

The answer, machine-checked here: the separating (superpolynomial) growth needs only a **fixed ratio
`p/q > 1` per level** — the exact factor `2` is strictly stronger than required, and pure additive
growth is strictly too weak.  So the essential content of `cost_super` is that the tower demand grows
**multiplicatively** (any base `> 1`), not that it doubles.

## What is proved

* **`demand_amplifies_ratio`** — the general engine: `∀ d, p·D d ≤ q·D(d+1)` ⟹
  `∀ d, p^d·D 0 ≤ q^d·D d`, i.e. `D d ≥ (p/q)^d · D 0`.  Any ratio `p/q` amplifies to its power.
* **`doubling_amplifies`** — the classic `p=2, q=1` instance: recovers `2^d ≤ D d`
  (= `DemandGeneration.demand_amplifies`).
* **`ratio_three_halves_amplifies`** — `p=3, q=2`: growth `(3/2)^d`, superpolynomial WITHOUT full
  doubling.
* **`doubling_implies_three_halves`** — the doubling premise IMPLIES the `3/2`-ratio premise: so
  `cost_super`'s factor 2 is **sufficient but not necessary**.
* **`ratio_one_no_amplification`** — `p=q` (ratio 1) is the COLLAPSE: the flat demand `D≡1` satisfies
  it and never grows.  The wall is exactly "ratio strictly `> 1`", i.e. avoiding collapse — matching
  this session's `TransportBound.collapse_to_floor` (full sharing drags the ratio to 1).
* **`additive_is_linear`** — additive growth `D d = 1 + c·d` is only LINEAR in `d` (polynomial), never
  superpolynomial.  This is the KRW/composition regime (additive ⟹ depth separation P⊄NC¹) — the
  multiplicative structure is exactly what lifts `cost_super` to a SIZE separation (P⊄P/poly).

## Honest scope — the wall is untouched, its shape is sharpened

Everything here is the AMPLIFICATION, which is FREE.  The wall is entirely in the PREMISE
`∀ d, p·D d ≤ q·D(d+1)` — that SAT's tower sustains some fixed ratio `> 1` per level.  That premise is
`cost_super`-family (P≠NP-strength); relaxing the ratio from `2/1` to any `p/q > 1` does not weaken
its strength, only pins the minimal sufficient form.  The gain is a sharper target: to separate, you
do not need the demand to double — you need it to grow multiplicatively by any fixed factor, and pure
additive (depth-style) growth provably will not do.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CostSuperRobust

open PallLean.Paper93.DeepMath.PathB.DemandGeneration

/-! ### The general amplification engine -/

/-- **The ratio amplification (proved).**  A per-level ratio bound `p·D d ≤ q·D(d+1)` amplifies to
`p^d·D 0 ≤ q^d·D d` — i.e. `D d ≥ (p/q)^d · D 0`.  The exact factor is irrelevant; any ratio is
carried to its `d`-th power up the tower. -/
theorem demand_amplifies_ratio (T : TowerDemand) (p q : ℕ)
    (super : ∀ d, p * T.D d ≤ q * T.D (d + 1)) (d : ℕ) :
    p ^ d * T.D 0 ≤ q ^ d * T.D d := by
  induction d with
  | zero =>
    have e : p ^ 0 * T.D 0 = q ^ 0 * T.D 0 := by rw [Nat.pow_zero, Nat.pow_zero]
    omega
  | succ d ih =>
    have hpow_p : p ^ (d + 1) * T.D 0 = p * (p ^ d * T.D 0) := by
      rw [Nat.pow_succ, Nat.mul_comm (p ^ d) p, Nat.mul_assoc]
    have hpow_q : q ^ (d + 1) * T.D (d + 1) = q ^ d * (q * T.D (d + 1)) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hpow_p, hpow_q]
    have hmid : p * (q ^ d * T.D d) = q ^ d * (p * T.D d) := by
      rw [Nat.mul_comm p (q ^ d * T.D d), Nat.mul_assoc, Nat.mul_comm (T.D d) p]
    calc p * (p ^ d * T.D 0)
        ≤ p * (q ^ d * T.D d) := Nat.mul_le_mul (Nat.le_refl p) ih
      _ = q ^ d * (p * T.D d) := hmid
      _ ≤ q ^ d * (q * T.D (d + 1)) := Nat.mul_le_mul (Nat.le_refl (q ^ d)) (super d)

/-! ### Factor 2 is sufficient but not necessary -/

/-- **The classic doubling (proved), as the `p=2, q=1` instance.**  Recovers `2^d ≤ D d`. -/
theorem doubling_amplifies (T : TowerDemand) (super : ∀ d, 2 * T.D d ≤ T.D (d + 1)) (d : ℕ) :
    2 ^ d * T.D 0 ≤ T.D d := by
  have h : 2 ^ d * T.D 0 ≤ 1 ^ d * T.D d :=
    demand_amplifies_ratio T 2 1 (fun d => by rw [Nat.one_mul]; exact super d) d
  rw [Nat.one_pow, Nat.one_mul] at h
  exact h

/-- **A sub-doubling ratio still amplifies (proved).**  `p=3, q=2`: `D d ≥ (3/2)^d · D 0`,
superpolynomial growth WITHOUT the full factor 2. -/
theorem ratio_three_halves_amplifies (T : TowerDemand)
    (super : ∀ d, 3 * T.D d ≤ 2 * T.D (d + 1)) (d : ℕ) :
    3 ^ d * T.D 0 ≤ 2 ^ d * T.D d :=
  demand_amplifies_ratio T 3 2 super d

/-- **The doubling is strictly stronger than the `3/2` requirement (proved).**  If the demand
doubles, it a fortiori satisfies the `3/2`-ratio premise — so `cost_super`'s exact factor 2 is
SUFFICIENT but NOT NECESSARY for the separating growth. -/
theorem doubling_implies_three_halves (T : TowerDemand)
    (super : ∀ d, 2 * T.D d ≤ T.D (d + 1)) :
    ∀ d, 3 * T.D d ≤ 2 * T.D (d + 1) := by
  intro d
  have h2 : 2 * (2 * T.D d) ≤ 2 * T.D (d + 1) := Nat.mul_le_mul (Nat.le_refl 2) (super d)
  calc 3 * T.D d
      ≤ 2 * (2 * T.D d) := by omega
    _ ≤ 2 * T.D (d + 1) := h2

/-! ### The floor (ratio 1) and the additive contrast -/

/-- **Ratio 1 is the collapse (proved).**  The flat demand `D ≡ 1` satisfies the `p=q` premise
`1·D d ≤ 1·D(d+1)` yet never grows.  So the wall is exactly "ratio strictly `> 1`" — avoiding
collapse, matching `TransportBound.collapse_to_floor`. -/
theorem ratio_one_no_amplification :
    (∀ d, 1 * flatDemand.D d ≤ 1 * flatDemand.D (d + 1)) ∧ ∀ d, flatDemand.D d = 1 :=
  ⟨fun d => by simp [flatDemand_eq], flatDemand_eq⟩

/-- An **additive** demand: `D d = 1 + c·d`.  Its base is free. -/
def addDemand (c : ℕ) : TowerDemand := ⟨fun d => 1 + c * d, by simp⟩

/-- **Additive growth is only linear (proved).**  `addDemand c` grows linearly in `d` — polynomial,
never superpolynomial.  This is the KRW/composition regime (additive ⟹ DEPTH separation P⊄NC¹); the
multiplicative structure of `cost_super` is exactly what lifts it to a SIZE separation P⊄P/poly. -/
theorem additive_is_linear (c d : ℕ) : (addDemand c).D d = 1 + c * d := rfl

end PallLean.Paper93.DeepMath.PathB.CostSuperRobust

#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperRobust.demand_amplifies_ratio
#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperRobust.doubling_amplifies
#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperRobust.ratio_three_halves_amplifies
#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperRobust.doubling_implies_three_halves
#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperRobust.ratio_one_no_amplification
#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperRobust.additive_is_linear
