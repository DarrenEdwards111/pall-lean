import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEvaln

/-! # Kleene interpreter project — `UCode.evaln` per-constructor equations (PROVED)

The `if`-form unfoldings of `UCode.evaln` at fuel `k+1` (one per constructor), with the `do guard (n≤k); …`
rewritten as `if n ≤ k then … else none`.  These are what `hbody` uses to connect each handler value to
`encodeOpt (UCode.evaln k (decodeU ec) n) = specOf` via the encode identities (`encode_pair_step`, etc.).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

theorem uevaln_zero (k' n : ℕ) : UCode.evaln (k'+1) UCode.zero n = if n ≤ k' then some 0 else none := by
  rw [UCode.evaln]; by_cases h : n ≤ k' <;> simp [h, guard]
theorem uevaln_succ (k' n : ℕ) : UCode.evaln (k'+1) UCode.succ n = if n ≤ k' then some (n+1) else none := by
  rw [UCode.evaln]; by_cases h : n ≤ k' <;> simp [h, guard]
theorem uevaln_left (k' n : ℕ) : UCode.evaln (k'+1) UCode.left n = if n ≤ k' then some (Nat.unpair n).1 else none := by
  rw [UCode.evaln]; by_cases h : n ≤ k' <;> simp [h, guard]
theorem uevaln_right (k' n : ℕ) : UCode.evaln (k'+1) UCode.right n = if n ≤ k' then some (Nat.unpair n).2 else none := by
  rw [UCode.evaln]; by_cases h : n ≤ k' <;> simp [h, guard]
theorem uevaln_pair (k' n : ℕ) (a b : UCode) : UCode.evaln (k'+1) (UCode.pair a b) n = if n ≤ k' then (Nat.pair <$> UCode.evaln (k'+1) a n <*> UCode.evaln (k'+1) b n) else none := by
  rw [UCode.evaln]; by_cases h : n ≤ k' <;> simp [h, guard]
theorem uevaln_comp (k' n : ℕ) (a b : UCode) : UCode.evaln (k'+1) (UCode.comp a b) n = if n ≤ k' then (UCode.evaln (k'+1) b n >>= fun x => UCode.evaln (k'+1) a x) else none := by
  rw [UCode.evaln]; by_cases h : n ≤ k' <;> simp [h, guard]
theorem uevaln_prec (k' n : ℕ) (a b : UCode) : UCode.evaln (k'+1) (UCode.prec a b) n = if n ≤ k' then ((Nat.unpair n).2.casesOn (UCode.evaln (k'+1) a (Nat.unpair n).1) (fun y => UCode.evaln k' (UCode.prec a b) (Nat.pair (Nat.unpair n).1 y) >>= fun i => UCode.evaln (k'+1) b (Nat.pair (Nat.unpair n).1 (Nat.pair y i)))) else none := by
  rw [UCode.evaln]; by_cases h : n ≤ k' <;> simp [h, guard, Nat.unpaired]
theorem uevaln_rfind (k' n : ℕ) (a : UCode) : UCode.evaln (k'+1) (UCode.rfind' a) n = if n ≤ k' then (UCode.evaln (k'+1) a (Nat.pair (Nat.unpair n).1 (Nat.unpair n).2) >>= fun x => if x = 0 then some (Nat.unpair n).2 else UCode.evaln k' (UCode.rfind' a) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else none := by
  rw [UCode.evaln]; by_cases h : n ≤ k' <;> simp [h, guard, Nat.unpaired]

/-- **Guard fails above fuel (proved): `UCode.evaln (k'+1) c n = none` when `n > k'`.**  (The value bound for
`comp`/`prec`/`rfind'`: an out-of-range input yields `none`.) -/
theorem uevaln_none_of_gt (k' n : ℕ) (c : UCode) (h : k' < n) : UCode.evaln (k'+1) c n = none := by
  have hn : ¬ n ≤ k' := by omega
  cases c <;> simp only [uevaln_zero, uevaln_succ, uevaln_left, uevaln_right, uevaln_pair, uevaln_comp,
    uevaln_prec, uevaln_rfind, if_neg hn]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
