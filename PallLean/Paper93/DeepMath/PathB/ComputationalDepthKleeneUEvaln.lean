import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUCode

/-!
# Kleene interpreter project — step 4: the `UCode`-native evaluator (PROVED)

A pure, **non-irreducible** evaluator `UCode.evaln` on the clean mirror code, mirroring `Code.evaln`'s
recursion exactly, and proved equal to `Code.evaln` through the bridge:

  `UCode.evaln` — fuel-bounded recursive evaluator on `UCode` (the spec for the dispatch).
  `UCode.evaln_eq` — `UCode.evaln k u n = Code.evaln k u.toCode n`.

This is the roadmap's "one-step evaluator matching `evaln`": a clean, computable, inspectable evaluator that
the dispatch `Code` (step 5) realizes, with its agreement with Mathlib's (irreducible) `Code.evaln` proved
once and for all.

## What is proved (clean axioms, no `sorry`)

* `UCode.evaln` — the native evaluator.
* `UCode.evaln_eq` — agreement with `Code.evaln ∘ toCode`.

## Honest scope

Step 4: the native evaluator + its correctness against `Code.evaln`.  Realizing it as an explicit `Code`
(step 5, the dispatch) and the fuel wrap/value-bound (steps 6–7) remain.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- The `UCode`-native fuel-bounded evaluator, mirroring `Code.evaln`. -/
def UCode.evaln : ℕ → UCode → ℕ → Option ℕ
  | 0, _, _ => Option.none
  | k + 1, .zero, n => do guard (n ≤ k); pure 0
  | k + 1, .succ, n => do guard (n ≤ k); pure (n + 1)
  | k + 1, .left, n => do guard (n ≤ k); pure (Nat.unpair n).1
  | k + 1, .right, n => do guard (n ≤ k); pure (Nat.unpair n).2
  | k + 1, .pair a b, n => do
      guard (n ≤ k); Nat.pair <$> UCode.evaln (k + 1) a n <*> UCode.evaln (k + 1) b n
  | k + 1, .comp a b, n => do
      guard (n ≤ k); let x ← UCode.evaln (k + 1) b n; UCode.evaln (k + 1) a x
  | k + 1, .prec a b, n => do
      guard (n ≤ k)
      n.unpaired fun aa nn =>
        nn.casesOn (UCode.evaln (k + 1) a aa)
          (fun y => do
            let i ← UCode.evaln k (.prec a b) (Nat.pair aa y)
            UCode.evaln (k + 1) b (Nat.pair aa (Nat.pair y i)))
  | k + 1, .rfind' a, n => do
      guard (n ≤ k)
      n.unpaired fun aa m => do
        let x ← UCode.evaln (k + 1) a (Nat.pair aa m)
        if x = 0 then pure m else UCode.evaln k (.rfind' a) (Nat.pair aa (m + 1))

/-- **The native evaluator agrees with `Code.evaln` (proved).** -/
theorem UCode.evaln_eq (k : ℕ) (u : UCode) (n : ℕ) :
    UCode.evaln k u n = Code.evaln k u.toCode n := by
  induction k, u, n using UCode.evaln.induct with
  | case1 => simp [UCode.evaln, Code.evaln]
  | case2 k n => simp [UCode.evaln, UCode.toCode, Code.evaln.eq_2]
  | case3 k n => simp [UCode.evaln, UCode.toCode, Code.evaln.eq_3]
  | case4 k n => simp [UCode.evaln, UCode.toCode, Code.evaln.eq_4]
  | case5 k n => simp [UCode.evaln, UCode.toCode, Code.evaln.eq_5]
  | case6 k a b n iha ihb => simp [UCode.evaln, UCode.toCode, Code.evaln.eq_6, iha, ihb]
  | case7 k a b n ihb iha => simp [UCode.evaln, UCode.toCode, Code.evaln.eq_7, iha, ihb]
  | case8 k a b n iha ihprec ihb => simp [UCode.evaln, UCode.toCode, Code.evaln.eq_8, iha, ihprec, ihb]
  | case9 k a n iha ihrec =>
      have hkey : UCode.evaln (k + 1) a n = Code.evaln (k + 1) a.toCode n := by
        have h := iha (Nat.unpair n).1 (Nat.unpair n).2
        rwa [Nat.pair_unpair] at h
      simp [UCode.evaln, UCode.toCode, Code.evaln.eq_9, hkey, ihrec]

/-!
**Step 4 proved.**  `UCode.evaln` is a clean recursive evaluator on the mirror code, agreeing with
Mathlib's `Code.evaln` (`UCode.evaln_eq`).  It is the spec the dispatch `Code` (step 5) realizes.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.UCode.evaln_eq
