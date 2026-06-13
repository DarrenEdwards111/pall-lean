import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGoldreichMajorityCandidate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAC0pInverterHardness

/-!
# The unified inverter frontier: the simultaneous‑resistance wall, made formal

The restricted `InversionHardness` results live in different settings; the global wall is *one* explicit family
resisting *every* inverter class at once.  This file makes that wall a **formal statement**, and proves the
genuinely new content: the **binding tension** between the two hard resistance notions —
*low‑degree algebraic* and *`AC⁰[p]`* — is real, because the natural witnesses are **provably incompatible**.

On a common carrier `F2Lang` (an `F₂`‑valued language on the Boolean cube, indexed by support):

* `ResistsLowDegree H t` — no nonzero ANF degree‑`< t` function annihilates the length‑`(2t-1)` slice of `H`.
* `ResistsAC0p H p` — no constant‑depth, poly‑size `AC⁰[p]` family computes `H` (via the support↔Bool bridge).

## Proved (clean axioms, no `sorry`)

* `majority_resists_lowDegree` — `majorityF2` resists the low‑degree class (`AI(Maj)=⌈n/2⌉`).
* `parity_resists_AC0p` / `modq_resists_AC0p` — `parityF2` / `modqF2` resist `AC⁰[p]` (Razborov–Smolensky).
* `parity_not_resists_lowDegree` — **the complementarity (new):** the `AC⁰[p]`‑resisting `parityF2` is *affine*
  (`AI ≤ 1`), so it has an explicit degree‑`1` annihilator `1 ⊕ parity` and **fails** low‑degree resistance.
  Proved via the `F₂` involution (`anf (T ↦ |T|) = δ_{|S|=1}`).
* `SimultaneousAlgAC0pResistance` — the named open target: `∃ H, ResistsLowDegree H t ∧ ResistsAC0p H p`.

## The wall, formally

`majorityF2` gives `ResistsLowDegree` but its `AC⁰[p]` hardness is *unproved*; `parityF2`/`modqF2` give
`ResistsAC0p` but **provably fail** `ResistsLowDegree` (`parity_not_resists_lowDegree`).  So **neither known
witness satisfies both conjuncts** — and `SimultaneousAlgAC0pResistance` (one family with both) is open.  The
other two classes (bounded‑crossing, bounded‑locality) are *automatic* for any `2^n`‑rich family — proved
generically in `…RestrictedInversionHardness` (`boundedCrossing_/boundedLocality_not_correct_inverter`) — so
they are *not* the binding constraint.  The binding constraint is exactly `ResistsLowDegree ∧ ResistsAC0p` over
a single family, and pushing it to all of `P` is the global `InversionHardness` wall (`P ≠ NP`‑strength).  This
file turns "no single predicate resists everything" from prose into a theorem about the natural witnesses.
-/

namespace PallLean.Paper93.DeepMath.PathB.UnifiedInverterFrontier

open Finset
open PallLean.Paper93.DeepMath.PathB.MajorityAI
open PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer7

/-- An `F₂`‑valued language on the Boolean cube, indexed by support (the algebraic‑native carrier). -/
abbrev F2Lang := (n : ℕ) → Finset (Fin n) → ZMod 2

/-- Bridge to a `BoolLang`: evaluate the `F₂` language on the support of the Boolean input. -/
def toBoolLang (H : F2Lang) : BoolLang := fun n x => decide (H n (toSupp x) = 1)

/-- **Resists the low‑degree algebraic class:** no nonzero ANF degree‑`< t` function annihilates the
length‑`(2t-1)` slice. -/
def ResistsLowDegree (H : F2Lang) (t : ℕ) : Prop :=
  ∀ g : Finset (Fin (2 * t - 1)) → ZMod 2, g ≠ 0 → DegreeLt g t →
    ∃ T, g T * H (2 * t - 1) T ≠ 0

/-- **Resists the `AC⁰[p]` class:** no constant‑depth, poly‑size `AC⁰[p]` family computes `H`. -/
def ResistsAC0p (H : F2Lang) (p : ℕ) : Prop :=
  ∀ F : Layer7.AC0pFamily p, IsPolyBounded F.sizeBound → ¬ F.Computes (toBoolLang H)

/-! ### Small bridging lemmas -/

theorem zmod2_natCast_eq_one_iff (c : ℕ) : (c : ZMod 2) = 1 ↔ Odd c := by
  rw [← ZMod.natCast_mod c 2, Nat.odd_iff]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> decide

theorem zmod2_if_eq_one_iff (P : Prop) [Decidable P] :
    ((if P then (1 : ZMod 2) else 0) = 1) ↔ P := by
  by_cases h : P
  · simp [h]
  · simp only [if_neg h]
    constructor
    · intro hh; exact absurd hh (by decide)
    · intro hh; exact absurd hh h

/-- The subset‑sum transform is additive. -/
theorem anf_add {n : ℕ} (a b : Finset (Fin n) → ZMod 2) (S : Finset (Fin n)) :
    anf (a + b) S = anf a S + anf b S := by
  simp only [anf, Pi.add_apply, Finset.sum_add_distrib]

/-- The ANF of the cardinality‑parity function is the singleton indicator (degree `1`): proved by the `F₂`
involution, since `|T| (mod 2) = ∑_{U⊆T} [|U|=1]`. -/
theorem anf_natCard {n : ℕ} (S : Finset (Fin n)) :
    anf (fun T => (T.card : ZMod 2)) S = if S.card = 1 then 1 else 0 := by
  have key : (fun T : Finset (Fin n) => (T.card : ZMod 2))
      = anf (fun U => if U.card = 1 then (1 : ZMod 2) else 0) := by
    funext T
    show (T.card : ZMod 2) = ∑ U ∈ T.powerset, (if U.card = 1 then (1 : ZMod 2) else 0)
    rw [Finset.sum_boole, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
        Nat.choose_one_right]
  rw [key, anf_involutive]

/-- The constant `1` has ANF supported at `∅`: its transform vanishes on nonempty sets. -/
theorem anf_const_one_high {n : ℕ} (S : Finset (Fin n)) (hS : 1 ≤ S.card) :
    anf (fun _ => (1 : ZMod 2)) S = 0 := by
  show (∑ _T ∈ S.powerset, (1 : ZMod 2)) = 0
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [Nat.cast_pow, h2, zero_pow (by omega)]

/-! ### Witness predicates -/

/-- Majority as an `F₂` language (threshold `⌈n/2⌉`). -/
def majorityF2 : F2Lang := fun n T => Maj ((n + 1) / 2) T

/-- `MOD_q` as an `F₂` language. -/
def modqF2 (q : ℕ) : F2Lang := fun _ T => if T.card % q = 0 then 1 else 0

/-- Parity (`MOD_2`) as an `F₂` language: the cardinality parity. -/
def parityF2 : F2Lang := fun _ T => (T.card : ZMod 2)

/-! ### The two binding resistances, witnessed -/

/-- **Majority resists the low‑degree class** (from `AI(Maj_{2t-1}) = t`). -/
theorem majority_resists_lowDegree {t : ℕ} (ht : 1 ≤ t) : ResistsLowDegree majorityF2 t := by
  intro g hg hdeg
  obtain ⟨T, hT⟩ := (majority_algebraic_immunity_two_sided (n := 2 * t - 1) (by omega) g hg hdeg).1
  refine ⟨T, ?_⟩
  have hthr : (2 * t - 1 + 1) / 2 = t := by omega
  show g T * majorityF2 (2 * t - 1) T ≠ 0
  simp only [majorityF2]
  rw [hthr]
  exact hT

/-- **`MOD_q` resists `AC⁰[p]`** (Razborov–Smolensky), for distinct primes `p ≠ q`. -/
theorem modq_resists_AC0p (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p) :
    ResistsAC0p (modqF2 q) p := by
  intro F hpoly hComp
  apply modq_not_in_nonuniform_AC0p p q hpq F hpoly
  have hbridge : toBoolLang (modqF2 q) = modqLang q := by
    funext n x
    show decide (modqF2 q n (toSupp x) = 1) = modqLang q n x
    simp only [modqF2, modqLang, toSupp]
    rw [decide_eq_decide]
    exact zmod2_if_eq_one_iff _
  rwa [hbridge] at hComp

/-- **Parity resists `AC⁰[p]`** (Razborov–Smolensky), for `p` odd. -/
theorem parity_resists_AC0p (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) :
    ResistsAC0p parityF2 p := by
  intro F hpoly hComp
  apply parity_not_in_nonuniform_AC0p p hp2 F hpoly
  have hbridge : toBoolLang parityF2 = parityLang := by
    funext n x
    show decide ((parityF2 n (toSupp x)) = 1) = parityLang n x
    simp only [parityF2, parityLang, toSupp]
    rw [decide_eq_decide]
    exact zmod2_natCast_eq_one_iff _
  rwa [hbridge] at hComp

/-! ### The complementarity: the `AC⁰[p]` witness provably fails low‑degree resistance -/

/-- **Parity fails the low‑degree class (the complementarity, proved).**  `parityF2` is affine
(`AI ≤ 1`): the degree‑`1` function `1 ⊕ parity` is a nonzero annihilator, so for `t ≥ 2` it is **not**
low‑degree‑resistant.  Together with `parity_resists_AC0p`, this shows the `AC⁰[p]`‑resisting witness cannot
double as the algebraic witness — the two hard resistances are genuinely in tension. -/
theorem parity_not_resists_lowDegree {t : ℕ} (ht : 2 ≤ t) : ¬ ResistsLowDegree parityF2 t := by
  intro hres
  set g : Finset (Fin (2 * t - 1)) → ZMod 2 := fun T => 1 + (T.card : ZMod 2) with hg_def
  have hg0 : g ≠ 0 := by
    intro h
    have he := congrFun h ∅
    simp [hg_def] at he
  have hgeq : g = (fun _ : Finset (Fin (2 * t - 1)) => (1 : ZMod 2))
      + (fun T => (T.card : ZMod 2)) := by
    funext T; simp only [hg_def, Pi.add_apply]
  have hdeg : DegreeLt g t := by
    intro S hS
    have h2 : 2 ≤ S.card := le_trans ht hS
    show anf g S = 0
    rw [hgeq, anf_add, anf_const_one_high S (by omega), anf_natCard S, if_neg (by omega), add_zero]
  obtain ⟨T, hT⟩ := hres g hg0 hdeg
  apply hT
  show g T * parityF2 (2 * t - 1) T = 0
  simp only [hg_def, parityF2]
  exact (by decide : ∀ c : ZMod 2, (1 + c) * c = 0) _

/-! ### The named wall -/

/-- **The simultaneous‑resistance wall (named, open).**  One `F₂` family resisting *both* the low‑degree
algebraic class and the `AC⁰[p]` class.  Each conjunct is individually achievable (`majorityF2`,
`modqF2`/`parityF2`), but no known family achieves both — and `parity_not_resists_lowDegree` shows the
`AC⁰[p]` witness provably fails the other conjunct.  Achieving this conjunction over a single family, extended
to all poly‑time inverters, is the global `InversionHardness` (`P ≠ NP`‑strength). -/
def SimultaneousAlgAC0pResistance (t p : ℕ) : Prop :=
  ∃ H : F2Lang, ResistsLowDegree H t ∧ ResistsAC0p H p

end PallLean.Paper93.DeepMath.PathB.UnifiedInverterFrontier

#print axioms PallLean.Paper93.DeepMath.PathB.UnifiedInverterFrontier.majority_resists_lowDegree
#print axioms PallLean.Paper93.DeepMath.PathB.UnifiedInverterFrontier.parity_resists_AC0p
#print axioms PallLean.Paper93.DeepMath.PathB.UnifiedInverterFrontier.parity_not_resists_lowDegree
