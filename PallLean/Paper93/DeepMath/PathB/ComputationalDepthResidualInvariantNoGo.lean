import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSeparatingInvariant
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators

/-!
# The suffix-residual invariant: the last natural repair, and why it still fails `PUpper`

`ComputationalDepthNFrameConcreteInvariant` disproved *representation*-SPDP rank as a separating invariant: it
is not a function of the decided Boolean function (the appended-sheet countermodel).  The natural repair is to
define the invariant **intrinsically from the decision function itself**, via the suffix-residual behaviour

```text
  residualBehavior L prefix := fun suffix => L (prefix ++ suffix).
```

The number of distinct residual behaviours (`residualRank`) is by construction a function of `L` alone, so it is
**semantically invariant** — the appended-sheet loophole is closed *by definition*.  This is the strongest form
of the "intrinsic sufficient statistic" the roadmap asks for.

This file proves that even this repaired, causally-coupled invariant is **rejected**, because it fails the
*other* gate `PUpper`.  The equality language `eqLang` (first half equals second half) is decided by a genuine
**linear-time** `ClockedMachine` (`eqMachine`, `runtime = length / 2`, one bit-comparison per step — the work is
in `next`, not hidden in `init`), yet it has `2^n` distinct length-`n` residuals.  Since `2^n` is
super-polynomial, `Rres := residualRank ∘ decide` violates `PUpper` on a linear-time `P` machine.

## Result

`residual_invariant_fails_PUpper : SemanticInvariant Rres ∧ ¬ PUpper Rres`.

The intrinsic residual rank clears the semantic-invariance gate (unlike representation-SPDP) but crashes into
`PUpper`: a *linear-time* algorithm for equality already forces `2^n` residuals.  So raw residual/sufficient-
statistic count cannot be the all-`P` invariant.  Any viable candidate must charge *irreducible time cost*, not
information / states / residual functions — exactly the roadmap's point 5.

## Honest scope

A machine-checked no-go for the repaired intrinsic invariant, plus a concrete honest linear-time equality
decider.  It eliminates the last natural representation-free repair; it proves **no** lower bound and supplies
**no** separating invariant.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResidualInvariantNoGo

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant

/-! ## Polynomial is dominated by `2^n` (super-polynomiality of the exponential) -/

/-- `m^2 ≤ 2^m` for `m ≥ 4`, by an elementary two-step induction. -/
theorem sq_le_two_pow : ∀ m : Nat, 4 ≤ m → m ^ 2 ≤ 2 ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hmm : 4 * m ≤ m * m := Nat.mul_le_mul hm (le_refl m)
    have hsq : m ^ 2 = m * m := pow_two m
    have h1 : 2 * m + 1 ≤ m ^ 2 := by rw [hsq]; omega
    calc (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      _ ≤ m ^ 2 + m ^ 2 := by omega
      _ = 2 * m ^ 2 := by ring
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- For every polynomial `c·(n+1)^k` there is an `n` at which `2^n` exceeds it. -/
theorem exists_lt_two_pow (c k : Nat) : ∃ n, c * (n + 1) ^ k < 2 ^ n := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨c, by simpa using c.lt_two_pow_self⟩
  · set m := c * k + c + 4 with hm_def
    have hm4 : 4 ≤ m := by omega
    refine ⟨k * m, ?_⟩
    have hlin : c * (k * m + 1) < 2 ^ m := by
      have hsq : m ^ 2 ≤ 2 ^ m := sq_le_two_pow m hm4
      have hmm : m ^ 2 = m * m := pow_two m
      have hcm : c ≤ c * m := Nat.le_mul_of_pos_right c (by omega)
      have h1 : c * (k * m + 1) = c * (k * m) + c := by ring
      have h2 : m * m = c * (k * m) + c * m + 4 * m := by rw [hm_def]; ring
      omega
    calc c * (k * m + 1) ^ k ≤ (c * (k * m + 1)) ^ k := by
          rw [mul_pow]; exact Nat.mul_le_mul_right _ (Nat.le_self_pow hk.ne' c)
      _ < (2 ^ m) ^ k := Nat.pow_lt_pow_left hlin hk.ne'
      _ = 2 ^ (k * m) := by rw [← pow_mul, Nat.mul_comm]

/-- `n ↦ 2^n` is not polynomially bounded. -/
theorem two_pow_not_polyBounded : ¬ PolyBounded (fun n => 2 ^ n) := by
  rintro ⟨c, k, hb⟩
  obtain ⟨n, hn⟩ := exists_lt_two_pow c k
  exact absurd (hb n) (Nat.not_le.mpr hn)

/-! ## The suffix-residual invariant (intrinsic to the decision function) -/

/-- The **suffix-residual behaviour** of a language `L` at a prefix: the function sending each suffix to the
decision on the concatenation.  Defined from `L` alone. -/
def residualBehavior (L : List Bool → Bool) (pre : List Bool) : List Bool → Bool :=
  fun suffix => L (pre ++ suffix)

/-- The **residual rank** at length `n`: the number of distinct residual behaviours over length-`n` prefixes.
A function of `L` only — hence semantically invariant by construction. -/
noncomputable def residualRank (L : List Bool → Bool) (n : Nat) : Nat :=
  Nat.card (Set.range (fun a : Fin n → Bool => residualBehavior L (List.ofFn a)))

/-- The residual rank lifted to machines: read off the decided function. -/
noncomputable def Rres : ClockedMachine → Nat → Nat :=
  fun M n => residualRank M.decide n

/-- **Semantic invariance, by construction.**  Two machines deciding the same language have *equal* residual
rank — because it depends only on the decided function. -/
theorem Rres_eq_of_decides {M₁ M₂ : ClockedMachine} {L : List Bool → Bool}
    (h₁ : Decides M₁ L) (h₂ : Decides M₂ L) : Rres M₁ = Rres M₂ := by
  have hdec : M₁.decide = M₂.decide := by funext x; rw [h₁ x, h₂ x]
  funext n; simp only [Rres, hdec]

/-- `Rres` clears the semantic-invariance gate (the equality is stronger than the required `↔`). -/
theorem Rres_semanticInvariant : SemanticInvariant Rres := by
  intro M₁ M₂ L h₁ h₂
  rw [Rres_eq_of_decides h₁ h₂]

/-! ## The equality language and its `2^n` residuals -/

/-- Index-based "first half equals second half" test: for `k` steps, compare position `j` against `j + half`. -/
def scanEq (x : List Bool) (half : Nat) : Nat → Bool
  | 0 => true
  | (k + 1) => scanEq x half k && decide (x[k]? = x[k + half]?)

theorem scanEq_iff (x : List Bool) (half k : Nat) :
    scanEq x half k = true ↔ ∀ j, j < k → x[j]? = x[j + half]? := by
  induction k with
  | zero => simp [scanEq]
  | succ k ih =>
    simp only [scanEq, Bool.and_eq_true, ih, decide_eq_true_eq]
    constructor
    · rintro ⟨hk, hkeq⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact hk j hlt
      · subst heq; exact hkeq
    · intro hall
      exact ⟨fun j hj => hall j (Nat.lt_succ_of_lt hj), hall k (Nat.lt_succ_self k)⟩

/-- The **equality language**: even length, and the first half equals the second half (index form). -/
def eqLang (x : List Bool) : Bool :=
  decide (x.length % 2 = 0) && scanEq x (x.length / 2) (x.length / 2)

/-- On concatenations of equal-length blocks, `eqLang` decides equality of the blocks. -/
theorem eqLang_ofFn_append {n : Nat} (a b : Fin n → Bool) :
    eqLang (List.ofFn a ++ List.ofFn b) = decide (a = b) := by
  have hlenA : (List.ofFn a).length = n := by simp
  have hlenB : (List.ofFn b).length = n := by simp
  have hlen : (List.ofFn a ++ List.ofFn b).length = 2 * n := by
    rw [List.length_append, hlenA, hlenB, two_mul]
  have hred : eqLang (List.ofFn a ++ List.ofFn b)
      = scanEq (List.ofFn a ++ List.ofFn b) n n := by
    unfold eqLang
    have e1 : (List.ofFn a ++ List.ofFn b).length % 2 = 0 := by rw [hlen]; omega
    have e2 : (List.ofFn a ++ List.ofFn b).length / 2 = n := by rw [hlen]; omega
    rw [e1, e2]; simp
  rw [hred]
  have hget : ∀ j (hj : j < n),
      ((List.ofFn a ++ List.ofFn b)[j]? = (List.ofFn a ++ List.ofFn b)[j + n]?)
        ↔ a ⟨j, hj⟩ = b ⟨j, hj⟩ := by
    intro j hj
    have hjA : j < (List.ofFn a).length := by rw [hlenA]; exact hj
    have hgeB : (List.ofFn a).length ≤ j + n := by rw [hlenA]; omega
    have hXj : (List.ofFn a ++ List.ofFn b)[j]? = some (a ⟨j, hj⟩) := by
      rw [List.getElem?_append_left hjA, List.getElem?_eq_getElem hjA, List.getElem_ofFn]
    have hXjn : (List.ofFn a ++ List.ofFn b)[j + n]? = some (b ⟨j, hj⟩) := by
      rw [List.getElem?_append_right hgeB]
      have hidx : j + n - (List.ofFn a).length = j := by rw [hlenA]; omega
      have hjB : j < (List.ofFn b).length := by rw [hlenB]; exact hj
      rw [hidx, List.getElem?_eq_getElem hjB, List.getElem_ofFn]
    rw [hXj, hXjn, Option.some_inj]
  have hiff : scanEq (List.ofFn a ++ List.ofFn b) n n = true ↔ a = b := by
    rw [scanEq_iff]
    constructor
    · intro H; funext i; exact (hget i.1 i.2).mp (H i.1 i.2)
    · intro H j hj; exact (hget j hj).mpr (by rw [H])
  rcases hs : scanEq (List.ofFn a ++ List.ofFn b) n n with _ | _
  · symm; rw [decide_eq_false_iff_not]; intro hab
    exact Bool.noConfusion (hs.symm.trans (hiff.mpr hab))
  · symm; rw [decide_eq_true_eq]; exact hiff.mp hs

/-- Distinct length-`n` prefixes produce distinct residual behaviours for `eqLang`. -/
theorem residual_eqLang_injective (n : Nat) :
    Function.Injective (fun a : Fin n → Bool => residualBehavior eqLang (List.ofFn a)) := by
  intro a a' h
  have hc := congrFun h (List.ofFn a)
  simp only [residualBehavior] at hc
  rw [eqLang_ofFn_append, eqLang_ofFn_append] at hc
  have h2 : decide (a' = a) = true := by rw [← hc]; exact decide_eq_true rfl
  exact (of_decide_eq_true h2).symm

/-- **Equality has `2^n` residuals.** -/
theorem residualRank_eqLang (n : Nat) : residualRank eqLang n = 2 ^ n := by
  rw [residualRank, Nat.card_range_of_injective (residual_eqLang_injective n),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-! ## An honest linear-time equality decider -/

/-- The equality machine.  `Config = (input, half, position, running-flag)`; `init` only loads the input and
the initial (parity) flag — it does **not** compute the answer — and `next` performs exactly one bit comparison
per step over `length / 2` steps.  The work is genuinely in `next`, so this is an honest linear-time decider. -/
def eqMachine : ClockedMachine where
  Config := List Bool × Nat × Nat × Bool
  init := fun x => (x, x.length / 2, 0, decide (x.length % 2 = 0))
  next := fun c => (c.1, c.2.1, c.2.2.1 + 1, c.2.2.2 && decide (c.1[c.2.2.1]? = c.1[c.2.2.1 + c.2.1]?))
  output := fun c => c.2.2.2
  runtime := fun x => x.length / 2

/-- The state after `k` steps: position `k`, flag `= parity ∧ (first `k` comparisons agree)`. -/
theorem eqMachine_iterate (x : List Bool) (k : Nat) :
    eqMachine.next^[k] (eqMachine.init x)
      = (x, x.length / 2, k, decide (x.length % 2 = 0) && scanEq x (x.length / 2) k) := by
  induction k with
  | zero => simp [eqMachine, scanEq]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [eqMachine, scanEq, Bool.and_assoc]

/-- `eqMachine` decides `eqLang`. -/
theorem eqMachine_decides : Decides eqMachine eqLang := by
  intro x
  show eqMachine.output (eqMachine.next^[eqMachine.runtime x] (eqMachine.init x)) = eqLang x
  have hr : eqMachine.runtime x = x.length / 2 := rfl
  rw [hr, eqMachine_iterate]
  rfl

/-- `eqMachine` runs in linear time (`runtime = length / 2`). -/
theorem eqMachine_polyTime : IsPolyTime eqMachine := by
  refine ⟨1, 1, fun x => ?_⟩
  show x.length / 2 ≤ 1 * (x.length + 1) ^ 1
  calc x.length / 2 ≤ x.length := Nat.div_le_self _ _
    _ ≤ 1 * (x.length + 1) ^ 1 := by ring_nf; omega

/-! ## The no-go: intrinsic residual rank clears semantic invariance but fails `PUpper` -/

/-- The linear-time equality machine has residual rank `2^n`. -/
theorem Rres_eqMachine (n : Nat) : Rres eqMachine n = 2 ^ n := by
  have hdec : eqMachine.decide = eqLang := funext eqMachine_decides
  simp only [Rres, hdec]
  exact residualRank_eqLang n

/-- **`Rres` violates `PUpper`.**  A linear-time (`P`) machine — `eqMachine` — has super-polynomial residual
rank `2^n`. -/
theorem Rres_not_PUpper : ¬ PUpper Rres := by
  intro hP
  have h := hP eqMachine eqMachine_polyTime
  have heq : Rres eqMachine = fun n => 2 ^ n := funext Rres_eqMachine
  rw [heq] at h
  exact two_pow_not_polyBounded h

/-- **The residual-invariant no-go.**  The intrinsic suffix-residual rank is semantically invariant (the
appended-sheet loophole is closed by construction) yet fails `PUpper`: equality, decided in linear time, already
forces `2^n` residuals.  So even the repaired intrinsic sufficient-statistic rank cannot be the all-`P`
invariant. -/
theorem residual_invariant_fails_PUpper :
    SemanticInvariant Rres ∧ ¬ PUpper Rres :=
  ⟨Rres_semanticInvariant, Rres_not_PUpper⟩

end PallLean.Paper93.DeepMath.PathB.ResidualInvariantNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.ResidualInvariantNoGo.residualRank_eqLang
#print axioms PallLean.Paper93.DeepMath.PathB.ResidualInvariantNoGo.eqMachine_decides
#print axioms PallLean.Paper93.DeepMath.PathB.ResidualInvariantNoGo.residual_invariant_fails_PUpper
