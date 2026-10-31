import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodeOpt

/-!
# Kleene interpreter project — the `prec` and `rfind'` encode identities (PROVED)

The conceptual cores of the last two handlers, as pure `Option`↔arithmetic identities.

`prec` recurses on the second unpaired component `n2`: `casesOn n2 (evaln a n1) (step)` under the guard.

  `encode_prec_step` — `encodeOpt (if n≤k then (if n2=0 then oa else os) else none) = [n≤k] · ([n2=0]·encodeOpt
    oa + [n2>0]·encodeOpt os)` — the guard + `casesOn` selector (additive: base vs step).

`rfind'` searches: `oa >>= fun x => if x=0 then pure n2 else (recurse)`, under the guard.

  `encode_rfind_step` — `encodeOpt (if n≤k then oa >>= (x ↦ if x=0 then some n2 else os) else none) = [n≤k] ·
    isPos(eoa) · ([eoa-1=0]·(n2+1) + [eoa-1≠0]·encodeOpt os)` — guard + bind + `x=0` conditional.

(`os` carries the lower-fuel recursive result, supplied by the handler `Code` via `cfgRank_lt_fuel`.)

## What is proved (clean axioms, no `sorry`)

* `encode_prec_step`, `encode_rfind_step`.

## Honest scope

The structural cores of `prec`/`rfind'`.  Their handler `Code`s (lower-fuel readers + casesOn/conditional
branching + value bounds), the body, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

/-- **`prec` encode identity (proved): guard + `casesOn`-on-`n2` selector.** -/
theorem encode_prec_step (k n n2 : ℕ) (oa os : Option ℕ) :
    encodeOpt (if n ≤ k then (if n2 = 0 then oa else os) else none)
      = (if n ≤ k then 1 else 0) * ((if n2 = 0 then 1 else 0) * encodeOpt oa
          + (if n2 = 0 then 0 else 1) * encodeOpt os) := by
  by_cases h : n ≤ k
  · rw [if_pos h, if_pos h, one_mul]
    by_cases h2 : n2 = 0
    · rw [if_pos h2, if_pos h2, if_pos h2, one_mul, zero_mul, add_zero]
    · rw [if_neg h2, if_neg h2, if_neg h2, zero_mul, one_mul, zero_add]
  · rw [if_neg h, if_neg h, zero_mul, encodeOpt]

/-- **`rfind'` encode identity (proved): guard + bind + `x=0` conditional.** -/
theorem encode_rfind_step (k n n2 : ℕ) (oa os : Option ℕ) :
    encodeOpt (if n ≤ k then (oa >>= fun x => if x = 0 then some n2 else os) else none)
      = (if n ≤ k then 1 else 0) * ((if encodeOpt oa = 0 then 0 else 1)
          * ((if encodeOpt oa - 1 = 0 then 1 else 0) * (n2 + 1)
              + (if encodeOpt oa - 1 = 0 then 0 else 1) * encodeOpt os)) := by
  by_cases h : n ≤ k
  · rw [if_pos h, if_pos h, one_mul]
    cases oa with
    | none => simp [encodeOpt]
    | some x =>
      have hb : (some x : Option ℕ) >>= (fun x => if x = 0 then some n2 else os)
          = (if x = 0 then some n2 else os) := rfl
      rw [hb]
      simp only [show encodeOpt (some x) = x + 1 from rfl, Nat.add_sub_cancel]
      rw [if_neg (Nat.succ_ne_zero x), one_mul]
      by_cases hx : x = 0
      · rw [if_pos hx, if_pos hx, if_pos hx, one_mul, zero_mul, add_zero, encodeOpt]
      · rw [if_neg hx, if_neg hx, if_neg hx, zero_mul, one_mul, zero_add]
  · rw [if_neg h, if_neg h, zero_mul, encodeOpt]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.encode_prec_step
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.encode_rfind_step
