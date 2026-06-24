import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEq

/-!
# Kleene interpreter project — modulo Code (PROVED)

For the rank decode (`n = rank % (B+1)`, etc.), modulo as a concrete `Code`.  `mod d a = a % d` via `prec`
on `a` with a wrap-around: `mod d (a+1) = if (mod d a)+1 = d then 0 else (mod d a)+1`.

  `modCode` — `modCode.eval (pair d a) = a % d` (for `0 < d`).

## What is proved (clean axioms, no `sorry`)

* `succ_mod_wrap` (the Nat fact), `mod_pairsel`, `mod_body`, `modCode`, `eval_modCode`.

## Honest scope

Modulo (rank decode).  `div`, the per-cell body, the correctness chain, the interpreter, and the runtime
remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- The successor-mod wrap identity (Nat fact). -/
theorem succ_mod_wrap (k d : ℕ) (hd : 0 < d) :
    (k + 1) % d = if k % d + 1 = d then 0 else k % d + 1 := by
  have key : (k + 1) % d = (k % d + 1) % d := by
    conv_lhs => rw [Nat.add_mod]
    rcases eq_or_ne d 1 with h | h
    · subst h; simp
    · rw [Nat.mod_eq_of_lt (by omega : 1 < d)]
  rw [key]
  rcases Nat.lt_or_ge (k % d + 1) d with hl | hge
  · rw [if_neg (by omega), Nat.mod_eq_of_lt hl]
  · have he : k % d + 1 = d := by have := Nat.mod_lt k hd; omega
    rw [if_pos he, he, Nat.mod_self]

/-- Modulo as a concrete `Code`: `prec` on `a` (input `pair d a`) with wrap. -/
def modCode : Code :=
  Code.prec (Code.const 0)
    (Code.comp (ifzCode (Code.const 0) Code.succ)
      (Code.pair (Code.comp Code.right Code.right)
        (Code.comp subCode (Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right))))))

/-- The body's payload/selector pair evaluates to `(prev, d - (prev+1))`. -/
theorem mod_pairsel (d k prev : ℕ) :
    (Code.pair (Code.comp Code.right Code.right)
      (Code.comp subCode (Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right))))).eval
        (Nat.pair d (Nat.pair k prev)) = Part.some (Nat.pair prev (d - (prev + 1))) := by
  have hpay : (Code.comp Code.right Code.right).eval (Nat.pair d (Nat.pair k prev)) = Part.some prev := by
    simp [Code.eval, Nat.unpair_pair]
  have hsel : (Code.comp subCode (Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right)))).eval
        (Nat.pair d (Nat.pair k prev)) = Part.some (d - (prev + 1)) := by
    have e : (Code.comp subCode (Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right)))).eval
          (Nat.pair d (Nat.pair k prev))
        = ((Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right))).eval
            (Nat.pair d (Nat.pair k prev))).bind subCode.eval := rfl
    rw [e, show ((Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right))).eval
          (Nat.pair d (Nat.pair k prev))) = Part.some (Nat.pair d (prev + 1))
        from by simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some, Nat.unpair_pair],
      Part.bind_some, eval_subCode]
  have e3 : (Code.pair (Code.comp Code.right Code.right)
        (Code.comp subCode (Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right))))).eval
        (Nat.pair d (Nat.pair k prev))
      = Nat.pair <$> (Code.comp Code.right Code.right).eval (Nat.pair d (Nat.pair k prev)) <*>
          (Code.comp subCode (Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right)))).eval
            (Nat.pair d (Nat.pair k prev)) := rfl
  rw [e3, hpay, hsel]; simp [Part.map_some, Seq.seq, Part.bind_some]

/-- The per-step body computes the wrap. -/
theorem mod_body (d k prev : ℕ) (hpd : prev < d) :
    (Code.comp (ifzCode (Code.const 0) Code.succ)
      (Code.pair (Code.comp Code.right Code.right)
        (Code.comp subCode (Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right)))))).eval
        (Nat.pair d (Nat.pair k prev)) = Part.some (if prev + 1 = d then 0 else prev + 1) := by
  have hb : (Code.comp (ifzCode (Code.const 0) Code.succ)
        (Code.pair (Code.comp Code.right Code.right)
          (Code.comp subCode (Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right)))))).eval
        (Nat.pair d (Nat.pair k prev))
      = (ifzCode (Code.const 0) Code.succ).eval (Nat.pair prev (d - (prev + 1))) := by
    show ((Code.pair (Code.comp Code.right Code.right)
        (Code.comp subCode (Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right Code.right))))).eval
          (Nat.pair d (Nat.pair k prev))).bind (ifzCode (Code.const 0) Code.succ).eval = _
    rw [mod_pairsel, Part.bind_some]
  rw [hb]
  by_cases h : prev + 1 = d
  · have hz : d - (prev + 1) = 0 := by omega
    rw [hz, eval_ifzCode_zero]; simp [Code.eval, h]
  · obtain ⟨t, ht⟩ : ∃ t, d - (prev + 1) = t + 1 := ⟨d - (prev + 1) - 1, by omega⟩
    rw [ht, eval_ifzCode_pos _ _ _ (by simp [Code.eval]) (by simp [Code.eval])]
    simp [Code.eval, h]

/-- **Modulo correctness (proved): `modCode.eval (pair d a) = a % d` for `0 < d`.** -/
theorem eval_modCode (d a : ℕ) (hd : 0 < d) : modCode.eval (Nat.pair d a) = Part.some (a % d) := by
  induction a with
  | zero => simp [modCode, Code.eval]
  | succ k ih =>
    rw [show modCode.eval (Nat.pair d (k + 1))
          = ((modCode.eval (Nat.pair d k)) >>= fun prev =>
              (Code.comp (ifzCode (Code.const 0) Code.succ)
                (Code.pair (Code.comp Code.right Code.right)
                  (Code.comp subCode (Code.pair Code.left
                    (Code.comp Code.succ (Code.comp Code.right Code.right)))))).eval
                (Nat.pair d (Nat.pair k prev)))
        from prec_eval_succ _ _ _ _, ih]
    simp only [Part.bind_eq_bind, Part.bind_some]
    rw [mod_body d k (k % d) (Nat.mod_lt k hd), succ_mod_wrap k d hd]

/-!
**Modulo proved.**  `div`, the per-cell body, the correctness chain, the interpreter, and the runtime
remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_modCode
