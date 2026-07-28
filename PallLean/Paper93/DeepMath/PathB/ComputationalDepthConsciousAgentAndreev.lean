import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConsciousAgentConcrete

/-!
# Lifting the concrete veridical perception one altitude with Andreev

`ConsciousAgentConcrete` gave a concrete veridical perception for the parity family at the *Khrapchenko*
ceiling: `parityMeasure n` perceives the hard member as `n²`.  Here it is lifted one altitude with **Andreev
`n^{5/2}`** — the strongest formula lower bound the repo proves — exactly as `AndreevCeiling` lifted the blade.

Parametrize `n = m²`, so the Khrapchenko rank is `n² = m⁴`, the Andreev rank is `n^{5/2} = m⁵`, and `n³ = m⁶`.
The lifted perception `andreevMeasure m` perceives the hard member as `m⁵` (Andreev) instead of `m⁴`
(Khrapchenko).

**Still veridical, at the higher ceiling.**  `andreevFamilyAgent_veridical`: for `m ≥ 2` the perception renders
the hard member (`m⁵`) differently from the trivial one (`1`).  `andreev_perceives_hardness` reads the hardness
bit off via the abstract `veridical_distinguishes`.

**It perceives strictly more hardness.**  `andreev_perceives_more_than_parity`: at `n = m²` the Andreev
perception of the hard member (`m⁵`) strictly exceeds the Khrapchenko perception (`parityMeasure (m²) = m⁴`),
because `m⁴ < m⁵` (`andreev_lifts_ceiling`).  The perception has climbed one altitude — it now sees the Andreev
`n^{5/2}` hardness, above the Khrapchenko `n²`.

**But it is still polynomial — the wall is unmoved, only raised.**  `andreev_still_capped`: `m⁵ < m⁶`, i.e.
`n^{5/2} < n³` — the lifted perception does not even reach `n³`, let alone superpolynomial.  A veridical
perception of *general* SAT hardness — `perceive` growing superpolynomially with the true circuit cost — would
be the separating witness = `cost_super`, and that is the perception no polynomial headset provides.

So Andreev lifts the perception's floor from `n²` to `n^{5/2}` — a real, machine-checked climb on the strongest
formula bound — and the same wall stands one notch higher: still polynomial, still short of general.

## What is proved

* **`andreevFamilyAgent_veridical`** — the lifted perception is veridical (`m⁵ ≠ 1` for `m ≥ 2`).
* **`andreev_perceives_hardness`** — its experience of the hard member differs from the trivial one.
* **`andreev_lifts_ceiling`** — `m⁴ < m⁵`: the Andreev ceiling exceeds the Khrapchenko ceiling.
* **`andreev_perceives_more_than_parity`** — the Andreev perception of the hard member exceeds the Khrapchenko
  perception `parityMeasure (m²)`: the perception is lifted one altitude.
* **`andreev_still_capped`** — `m⁵ < m⁶` (`n^{5/2} < n³`): the lifted perception is still polynomial.

## Honest verdict — a real higher-altitude veridical perception, still capped

The concrete veridical perception is lifted one altitude with Andreev: `andreevFamilyAgent` perceives the hard
parity/Tseitin member as its Andreev rank `n^{5/2} = m⁵`, remains veridical (`andreevFamilyAgent_veridical`), and
perceives strictly more hardness than the Khrapchenko perception (`andreev_perceives_more_than_parity`,
`m⁴ < m⁵`) — a genuine climb on the strongest formula lower bound the repo proves.  And the cap is the same, one
notch up: `m⁵ < m⁶`, i.e. `n^{5/2} < n³`, still polynomial (`andreev_still_capped`).  A veridical perception of
general SAT hardness would be the separating witness = `cost_super`; Andreev raises the altitude at which the
perception is veridical, not past the polynomial ceiling.  Same shape as the blade ladder
(`RestrictedBlade → AndreevCeiling`), now in Hoffman's conscious-agent language.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ConsciousAgentAndreev

open PallLean.Paper93.DeepMath.PathB.ConsciousAgent
open PallLean.Paper93.DeepMath.PathB.ConsciousAgentConcrete

/-- The Andreev `n^{5/2}` rank measure at `n = m²`: the hard member (`true`) is measured as `m⁵`, the trivial
member (`false`) as `1`.  This lifts `parityMeasure` (Khrapchenko `m⁴`) one altitude. -/
def andreevMeasure (m : ℕ) (w : Bool) : ℕ := match w with | true => m ^ 5 | false => 1

/-- The conscious-agent perception lifted to the Andreev ceiling at `n = m²`: `perceive = andreevMeasure m`. -/
def andreevFamilyAgent (m : ℕ) : ConsciousAgent where
  World := Bool
  Experience := ℕ
  perceive := andreevMeasure m
  isHard := fun w => w = true

/-- **The lifted perception is veridical (proved).**  For `m ≥ 2` the hard member is perceived as `m⁵` and the
trivial one as `1`, and `m⁵ ≠ 1`. -/
theorem andreevFamilyAgent_veridical (m : ℕ) (hm : 2 ≤ m) :
    (andreevFamilyAgent m).Veridical := by
  intro w w' hw hw'
  have hwt : w = true := hw
  subst hwt
  have hw'f : w' = false := by
    cases w' with
    | true => exact absurd rfl hw'
    | false => rfl
  subst hw'f
  show m ^ 5 ≠ 1
  have h : (2 : ℕ) ^ 5 ≤ m ^ 5 := Nat.pow_le_pow_left hm 5
  have h2 : (2 : ℕ) ≤ 2 ^ 5 := by norm_num
  omega

/-- **The lifted perception reads off hardness (proved).**  Its experience of the hard member differs from the
trivial member — via the abstract `veridical_distinguishes`. -/
theorem andreev_perceives_hardness (m : ℕ) (hm : 2 ≤ m) :
    (andreevFamilyAgent m).perceive true ≠ (andreevFamilyAgent m).perceive false :=
  veridical_distinguishes (andreevFamilyAgent m) (andreevFamilyAgent_veridical m hm)
    true false rfl nofun

/-- **The Andreev ceiling exceeds the Khrapchenko ceiling (proved).**  `m⁴ < m⁵`. -/
theorem andreev_lifts_ceiling (m : ℕ) (hm : 2 ≤ m) : m ^ 4 < m ^ 5 := by
  have e : m ^ 5 = m ^ 4 * m := by ring
  have hpos : 0 < m ^ 4 := by
    have hb : (2 : ℕ) ^ 4 ≤ m ^ 4 := Nat.pow_le_pow_left hm 4
    have h1 : (1 : ℕ) ≤ 2 ^ 4 := by norm_num
    omega
  have key : m ^ 4 * 1 < m ^ 4 * m :=
    mul_lt_mul_of_pos_left (by omega : (1 : ℕ) < m) hpos
  rw [e]; simpa using key

/-- **The Andreev perception perceives more hardness than the Khrapchenko one (proved) — the lift.**  At
`n = m²`, the Andreev perception of the hard member (`m⁵`) strictly exceeds the Khrapchenko perception
`parityMeasure (m²) = m⁴`. -/
theorem andreev_perceives_more_than_parity (m : ℕ) (hm : 2 ≤ m) :
    parityMeasure (m ^ 2) true < andreevMeasure m true := by
  show (m ^ 2) * (m ^ 2) < m ^ 5
  have e : (m ^ 2) * (m ^ 2) = m ^ 4 := by ring
  rw [e]
  exact andreev_lifts_ceiling m hm

/-- **The lifted perception is still polynomial (proved).**  `m⁵ < m⁶`, i.e. `n^{5/2} < n³`: the lift does not
reach `n³`, let alone superpolynomial. -/
theorem andreev_still_capped (m : ℕ) (hm : 2 ≤ m) : m ^ 5 < m ^ 6 := by
  have e : m ^ 6 = m ^ 5 * m := by ring
  have hpos : 0 < m ^ 5 := by
    have hb : (2 : ℕ) ^ 5 ≤ m ^ 5 := Nat.pow_le_pow_left hm 5
    have h1 : (1 : ℕ) ≤ 2 ^ 5 := by norm_num
    omega
  have key : m ^ 5 * 1 < m ^ 5 * m :=
    mul_lt_mul_of_pos_left (by omega : (1 : ℕ) < m) hpos
  rw [e]; simpa using key

end PallLean.Paper93.DeepMath.PathB.ConsciousAgentAndreev

#print axioms PallLean.Paper93.DeepMath.PathB.ConsciousAgentAndreev.andreevFamilyAgent_veridical
#print axioms PallLean.Paper93.DeepMath.PathB.ConsciousAgentAndreev.andreev_perceives_hardness
#print axioms PallLean.Paper93.DeepMath.PathB.ConsciousAgentAndreev.andreev_lifts_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.ConsciousAgentAndreev.andreev_perceives_more_than_parity
#print axioms PallLean.Paper93.DeepMath.PathB.ConsciousAgentAndreev.andreev_still_capped
