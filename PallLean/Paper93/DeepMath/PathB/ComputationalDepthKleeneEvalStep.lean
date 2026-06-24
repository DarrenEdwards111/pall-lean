import Mathlib

/-!
# Kleene interpreter project — memoized DP, piece 1: the recurrence step (PROVED)

The efficient (memoized) universal simulator computes `evaln` by filling a table indexed by configuration in
order of the measure `(fuel, encode code)`, each cell using earlier cells.  The **recurrence** at the heart
of this is `evalnStep`: one unfolding of `evaln` whose recursive calls are delegated to an `oracle`.

  `evalnStep oracle k c n` — `evaln`'s body (mirroring `Code.evaln.eq_1..9`) with sub-calls via `oracle`.
    It is *not* self-recursive (it calls `oracle`), so it is trivially well-defined.
  `evalnStep_correct` — if `oracle` agrees with `Code.evaln` on every configuration of strictly smaller
    measure (`k' < k`, or `k' = k` with `encode c' < encode c`), then `evalnStep oracle k c n = evaln k c n`.

So `Code.evaln` is the fixed point of `evalnStep` filled in measure order — exactly what the memoized table
computes.  Every recursive call of `evaln` (`comp`/`pair` into subcodes at the same fuel; `prec`/`rfind'` at
lower fuel) drops the measure, which is why the agreement hypothesis suffices (`encode_lt_*`,
`Nat.lt_succ_self`).

## What is proved (clean axioms, no `sorry`)

* `evalnStep`, `evalnStep_correct` — the recurrence and its fixed-point correctness.

## Honest scope

The DP recurrence step.  Filling the table in measure order (course-of-values), realizing it as an explicit
`Code`, and the runtime bound remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneEvalStep

open Nat.Partrec

/-- One unfolding of `evaln` with recursive calls delegated to `oracle` (the DP recurrence). -/
def evalnStep (oracle : ℕ → Code → ℕ → Option ℕ) : ℕ → Code → ℕ → Option ℕ
  | 0, _, _ => Option.none
  | k + 1, Code.zero, n => do guard (n ≤ k); pure 0
  | k + 1, Code.succ, n => do guard (n ≤ k); pure (n + 1)
  | k + 1, Code.left, n => do guard (n ≤ k); pure (Nat.unpair n).1
  | k + 1, Code.right, n => do guard (n ≤ k); pure (Nat.unpair n).2
  | k + 1, Code.pair a b, n => do guard (n ≤ k); Nat.pair <$> oracle (k + 1) a n <*> oracle (k + 1) b n
  | k + 1, Code.comp a b, n => do guard (n ≤ k); let x ← oracle (k + 1) b n; oracle (k + 1) a x
  | k + 1, Code.prec a b, n => do
      guard (n ≤ k)
      n.unpaired fun aa nn => nn.casesOn (oracle (k + 1) a aa)
        (fun y => do
          let i ← oracle k (Code.prec a b) (Nat.pair aa y)
          oracle (k + 1) b (Nat.pair aa (Nat.pair y i)))
  | k + 1, Code.rfind' a, n => do
      guard (n ≤ k)
      n.unpaired fun aa m => do
        let x ← oracle (k + 1) a (Nat.pair aa m)
        if x = 0 then pure m else oracle k (Code.rfind' a) (Nat.pair aa (m + 1))

/-- **The recurrence is correct given a measure-smaller-correct oracle (proved).**  Hence `Code.evaln` is the
fixed point of `evalnStep` filled in measure order. -/
theorem evalnStep_correct (oracle : ℕ → Code → ℕ → Option ℕ) (k : ℕ) (c : Code) (n : ℕ)
    (h : ∀ k' c' n', (k' < k ∨ (k' = k ∧ Encodable.encode c' < Encodable.encode c)) →
      oracle k' c' n' = Code.evaln k' c' n') :
    evalnStep oracle k c n = Code.evaln k c n := by
  cases k with
  | zero => cases c <;> simp [evalnStep, Code.evaln]
  | succ k =>
    cases c with
    | zero => simp [evalnStep, Code.evaln.eq_2]
    | succ => simp [evalnStep, Code.evaln.eq_3]
    | left => simp [evalnStep, Code.evaln.eq_4]
    | right => simp [evalnStep, Code.evaln.eq_5]
    | pair a b =>
      have ha : oracle (k + 1) a = Code.evaln (k + 1) a :=
        funext fun x => h _ _ _ (Or.inr ⟨rfl, (Code.encode_lt_pair a b).1⟩)
      have hb : oracle (k + 1) b = Code.evaln (k + 1) b :=
        funext fun x => h _ _ _ (Or.inr ⟨rfl, (Code.encode_lt_pair a b).2⟩)
      simp [evalnStep, Code.evaln.eq_6, ha, hb]
    | comp a b =>
      have ha : oracle (k + 1) a = Code.evaln (k + 1) a :=
        funext fun x => h _ _ _ (Or.inr ⟨rfl, (Code.encode_lt_comp a b).1⟩)
      have hb : oracle (k + 1) b = Code.evaln (k + 1) b :=
        funext fun x => h _ _ _ (Or.inr ⟨rfl, (Code.encode_lt_comp a b).2⟩)
      simp [evalnStep, Code.evaln.eq_7, ha, hb]
    | prec a b =>
      have ha : oracle (k + 1) a = Code.evaln (k + 1) a :=
        funext fun x => h _ _ _ (Or.inr ⟨rfl, (Code.encode_lt_prec a b).1⟩)
      have hb : oracle (k + 1) b = Code.evaln (k + 1) b :=
        funext fun x => h _ _ _ (Or.inr ⟨rfl, (Code.encode_lt_prec a b).2⟩)
      have hp : oracle k (Code.prec a b) = Code.evaln k (Code.prec a b) :=
        funext fun x => h _ _ _ (Or.inl (Nat.lt_succ_self k))
      simp [evalnStep, Code.evaln.eq_8, ha, hb, hp]
    | rfind' a =>
      have ha : oracle (k + 1) a = Code.evaln (k + 1) a :=
        funext fun x => h _ _ _ (Or.inr ⟨rfl, Code.encode_lt_rfind' a⟩)
      have hp : oracle k (Code.rfind' a) = Code.evaln k (Code.rfind' a) :=
        funext fun x => h _ _ _ (Or.inl (Nat.lt_succ_self k))
      simp [evalnStep, Code.evaln.eq_9, ha, hp]

/-!
**DP recurrence proved.**  `Code.evaln` is the fixed point of `evalnStep` over the measure `(fuel, encode
code)`.  Filling the table in measure order (course-of-values), the explicit `Code`, and the runtime bound
remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneEvalStep

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneEvalStep.evalnStep_correct
