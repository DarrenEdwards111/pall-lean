import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodeOpt

/-!
# Kleene interpreter project — the `comp` encode identity + value bound (PROVED)

`comp` is the data-dependent handler: `evalnStep (comp a b) n = guard; (evaln b n) >>= (evaln a)`, where the
second call's *input* is the first's output value `vb`.  Its sub-config `(k, a, vb)` is in the table only if
`vb ≤ B`.  The **value bound** appears as the hypothesis `hB : ∀ vb, B < vb → oaf vb = none` — i.e. for
inputs beyond the table dimension the second evaluator yields `none` (which holds because `B` bounds the
fuel, so `vb > B ⇒ vb > k ⇒` the guard at `a` fails).  Under it, the encoded `comp`-result equals the
branch-free multiplicative form (with a `[vb ≤ B]` guard factor):

  `encode_comp_step` — `encodeOpt (if n≤k then ob >>= oaf else none) = [n≤k] · isPos(eb) · [eb-1 ≤ B] ·
    encodeOpt (oaf (eb-1))`, where `eb = encodeOpt ob`.

This is exactly the `comp` handler's computation (`ob = evaln b n`, `oaf = evaln a`, `eb-1 = vb` read/decoded
from the table, the `[vb≤B]` guard making the out-of-range lookup safe).

## What is proved (clean axioms, no `sorry`)

* `encode_comp_step` — the `comp` value-bounded encode identity.

## Honest scope

The `comp` value-bound core.  The `comp` handler `Code` (data-dependent assembly), `prec`/`rfind'`, the body,
the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

/-- **`comp` value-bounded encode identity (proved).** -/
theorem encode_comp_step (k n B : ℕ) (ob : Option ℕ) (oaf : ℕ → Option ℕ)
    (hB : ∀ vb, B < vb → oaf vb = none) :
    encodeOpt (if n ≤ k then ob >>= oaf else none)
      = (if n ≤ k then 1 else 0) * ((if encodeOpt ob = 0 then 0 else 1)
          * ((if encodeOpt ob - 1 ≤ B then 1 else 0) * encodeOpt (oaf (encodeOpt ob - 1)))) := by
  by_cases h : n ≤ k
  · rw [if_pos h, if_pos h, one_mul]
    cases ob with
    | none => simp [encodeOpt]
    | some vb =>
      have hb : (some vb : Option ℕ) >>= oaf = oaf vb := rfl
      rw [hb]
      simp only [show encodeOpt (some vb) = vb + 1 from rfl, Nat.add_sub_cancel]
      rw [if_neg (Nat.succ_ne_zero vb), one_mul]
      by_cases hvb : vb ≤ B
      · rw [if_pos hvb, one_mul]
      · rw [if_neg hvb, zero_mul]; simp [hB vb (by omega), encodeOpt]
  · rw [if_neg h, if_neg h, zero_mul, encodeOpt]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.encode_comp_step
