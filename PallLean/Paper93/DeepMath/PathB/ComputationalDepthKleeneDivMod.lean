import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneMod

/-!
# Kleene interpreter project — div/mod Code (PROVED)

The rank decode needs both quotient and remainder, and `div`'s wrap depends on the remainder, so we build a
combined `divmodCode`: `divmodCode.eval (pair d a) = pair (a / d) (a % d)` (for `0 < d`), via `prec` on `a`
with a paired `(q, r)` accumulator wrapping `(q, r) ↦ if r+1 = d then (q+1, 0) else (q, r+1)`.

  `divmodCode` — `divmodCode.eval (pair d a) = Nat.pair (a / d) (a % d)`.

## What is proved (clean axioms, no `sorry`)

* `succ_div_wrap` (Nat fact), `thenB_eval`/`elseB_eval`/`dm_pairsel` (body pieces), `divmodCode`,
  `divmod_body`, `eval_divmodCode`.

## Honest scope

div/mod (rank decode complete).  The per-cell body, the correctness chain, the interpreter, and the runtime
remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Successor-div wrap identity (Nat fact). -/
theorem succ_div_wrap (k d : ℕ) (hd : 0 < d) :
    (k + 1) / d = if k % d + 1 = d then k / d + 1 else k / d := by
  rw [Nat.succ_div]
  have hml := Nat.mod_lt k hd
  have hdvd : (d ∣ (k + 1)) ↔ (k % d + 1 = d) := by
    rw [Nat.dvd_iff_mod_eq_zero, succ_mod_wrap k d hd]
    constructor
    · intro h; by_contra hne; rw [if_neg hne] at h; omega
    · intro h; rw [if_pos h]
  by_cases h : k % d + 1 = d
  · rw [if_pos h, if_pos (hdvd.mpr h)]
  · rw [if_neg h, if_neg (fun hh => h (hdvd.mp hh)), Nat.add_zero]

theorem thenB_eval (q r : ℕ) :
    (Code.pair (Code.comp Code.succ Code.left) (Code.const 0)).eval (Nat.pair q r)
      = Part.some (Nat.pair (q + 1) 0) := by
  simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some, Nat.unpair_pair]

theorem elseB_eval (q r : ℕ) :
    (Code.pair Code.left (Code.comp Code.succ Code.right)).eval (Nat.pair q r)
      = Part.some (Nat.pair q (r + 1)) := by
  simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some, Nat.unpair_pair]

theorem dm_pairsel (d k q r : ℕ) :
    (Code.pair (Code.comp Code.right Code.right)
      (Code.comp subCode (Code.pair Code.left
        (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right)))))).eval
        (Nat.pair d (Nat.pair k (Nat.pair q r))) = Part.some (Nat.pair (Nat.pair q r) (d - (r + 1))) := by
  have hpay : (Code.comp Code.right Code.right).eval (Nat.pair d (Nat.pair k (Nat.pair q r)))
      = Part.some (Nat.pair q r) := by simp [Code.eval, Nat.unpair_pair]
  have hsel : (Code.comp subCode (Code.pair Code.left
        (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right))))).eval
        (Nat.pair d (Nat.pair k (Nat.pair q r))) = Part.some (d - (r + 1)) := by
    have e : (Code.comp subCode (Code.pair Code.left
          (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right))))).eval
          (Nat.pair d (Nat.pair k (Nat.pair q r)))
        = ((Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right)))).eval
            (Nat.pair d (Nat.pair k (Nat.pair q r)))).bind subCode.eval := rfl
    rw [e, show ((Code.pair Code.left (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right)))).eval
          (Nat.pair d (Nat.pair k (Nat.pair q r)))) = Part.some (Nat.pair d (r + 1))
        from by simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some, Nat.unpair_pair],
      Part.bind_some, eval_subCode]
  show Nat.pair <$> (Code.comp Code.right Code.right).eval (Nat.pair d (Nat.pair k (Nat.pair q r))) <*>
      (Code.comp subCode (Code.pair Code.left
        (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right))))).eval
        (Nat.pair d (Nat.pair k (Nat.pair q r))) = _
  rw [hpay, hsel]; simp [Part.map_some, Seq.seq, Part.bind_some]

/-- Combined div/mod: `prec` on `a` with a `(q, r)` accumulator. -/
def divmodCode : Code :=
  Code.prec (Code.const (Nat.pair 0 0))
    (Code.comp
      (ifzCode (Code.pair (Code.comp Code.succ Code.left) (Code.const 0))
        (Code.pair Code.left (Code.comp Code.succ Code.right)))
      (Code.pair (Code.comp Code.right Code.right)
        (Code.comp subCode (Code.pair Code.left
          (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right)))))))

theorem divmod_body (d k q r : ℕ) (hrd : r < d) :
    (Code.comp
      (ifzCode (Code.pair (Code.comp Code.succ Code.left) (Code.const 0))
        (Code.pair Code.left (Code.comp Code.succ Code.right)))
      (Code.pair (Code.comp Code.right Code.right)
        (Code.comp subCode (Code.pair Code.left
          (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right))))))).eval
        (Nat.pair d (Nat.pair k (Nat.pair q r)))
      = Part.some (if r + 1 = d then Nat.pair (q + 1) 0 else Nat.pair q (r + 1)) := by
  have hb : (Code.comp
      (ifzCode (Code.pair (Code.comp Code.succ Code.left) (Code.const 0))
        (Code.pair Code.left (Code.comp Code.succ Code.right)))
      (Code.pair (Code.comp Code.right Code.right)
        (Code.comp subCode (Code.pair Code.left
          (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right))))))).eval
        (Nat.pair d (Nat.pair k (Nat.pair q r)))
      = (ifzCode (Code.pair (Code.comp Code.succ Code.left) (Code.const 0))
          (Code.pair Code.left (Code.comp Code.succ Code.right))).eval
          (Nat.pair (Nat.pair q r) (d - (r + 1))) := by
    show ((Code.pair (Code.comp Code.right Code.right)
        (Code.comp subCode (Code.pair Code.left
          (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right)))))).eval
          (Nat.pair d (Nat.pair k (Nat.pair q r)))).bind _ = _
    rw [dm_pairsel, Part.bind_some]
  rw [hb]
  by_cases h : r + 1 = d
  · have hz : d - (r + 1) = 0 := by omega
    rw [hz, eval_ifzCode_zero, thenB_eval, if_pos h]
  · obtain ⟨t, ht⟩ : ∃ t, d - (r + 1) = t + 1 := ⟨d - (r + 1) - 1, by omega⟩
    rw [ht, eval_ifzCode_pos _ _ _ (by rw [thenB_eval]; trivial) (by rw [elseB_eval]; trivial),
      elseB_eval, if_neg h]

/-- **div/mod correctness (proved): `divmodCode.eval (pair d a) = pair (a/d) (a%d)` for `0 < d`.** -/
theorem eval_divmodCode (d a : ℕ) (hd : 0 < d) :
    divmodCode.eval (Nat.pair d a) = Part.some (Nat.pair (a / d) (a % d)) := by
  induction a with
  | zero => simp [divmodCode, Code.eval]
  | succ k ih =>
    rw [show divmodCode.eval (Nat.pair d (k + 1))
          = ((divmodCode.eval (Nat.pair d k)) >>= fun prev =>
              (Code.comp
                (ifzCode (Code.pair (Code.comp Code.succ Code.left) (Code.const 0))
                  (Code.pair Code.left (Code.comp Code.succ Code.right)))
                (Code.pair (Code.comp Code.right Code.right)
                  (Code.comp subCode (Code.pair Code.left
                    (Code.comp Code.succ (Code.comp Code.right (Code.comp Code.right Code.right))))))).eval
                (Nat.pair d (Nat.pair k prev)))
        from prec_eval_succ _ _ _ _, ih]
    simp only [Part.bind_eq_bind, Part.bind_some]
    rw [divmod_body d k (k / d) (k % d) (Nat.mod_lt k hd), succ_div_wrap k d hd, succ_mod_wrap k d hd]
    by_cases h : k % d + 1 = d <;> simp [h]

/-!
**div/mod proved.**  Rank decode is now available.  The per-cell body, the correctness chain, the
interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_divmodCode
