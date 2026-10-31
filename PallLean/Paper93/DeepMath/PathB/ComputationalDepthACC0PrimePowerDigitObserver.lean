import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimePowerGate

/-!
# Candidate #4 — the Witt-vector / `p`-adic digit observer `x = a₀ + p·a₁ + p²·a₂ + …`

The observer-candidate analysis refuted the characteristic-`p` field family (`…ACC0PrimePowerObserverCandidates`) and
examined the ring (`ZMod p^e`), valuation (`v_p`) and layered residue tower (`…ACC0PrimePowerTowerObserver`).  This file
analyses the last candidate: the **base-`p` digit (Witt) observer**

```
   x = a₀ + p·a₁ + p²·a₂ + … ,        aᵢ := digit p i x := (x / pⁱ) mod p ,
```

which records `x` by its `p`-adic digits rather than its residues.  Two honest facts pin down what it buys:

* **The digit observer decides `MOD_{p^e}`.**  `p^e ∣ x ↔` the lowest `e` digits `a₀, …, a_{e-1}` all vanish:
  `p^e ∣ x ↔ ∀ i < e, digit p i x = 0`.  (Proved by induction on `e`, peeling one digit at a time — *not* simplified to
  the residue statement.)

* **The field observer is exactly the lowest digit.**  `digit p 0 x = x mod p` — the characteristic-`p` field observer
  sees *only* `a₀`.  So the digit decomposition makes the field obstruction transparent: `MOD_{p^e}` needs all `e` low
  digits `a₀ … a_{e-1}`, the field sees one (`a₀`), and `0` and `p` already share `a₀ = 0` while `MOD_{p^e}` separates
  them (`field_digit_insufficient`).

## What is proved (clean axioms, no `sorry`)

* **`lowest_digit_eq_mod_p`** — `digit p 0 s = s mod p` (the field observer = the lowest digit).
* **`digit_observer_decides`** — `p^e ∣ s ↔ ∀ i < e, digit p i s = 0` (the digit observer decides `MOD_{p^e}`;
  full digit-peeling induction).
* **`field_digit_insufficient`** — `0` and `p` share the lowest digit (`a₀ = 0`) yet `MOD_{p^e}` separates them
  (`e ≥ 2`): the lowest digit alone is insufficient.

## Honest scope

The digit observer is information-*equivalent* to the ring `ZMod (p^e)` and the residue tower (the digits `a₀ … a_{e-1}`
and the residue `x mod p^e` determine each other), so it does **not** escape the low-degree wall.  Its value is the same
as the tower's: it exposes *structure* — here the explicit Witt/digit decomposition — and localises the field
obstruction to the lowest digit (`MOD_{p^e}` needs depth `e` digits; the field sees only `a₀`).  No quasipolynomial
low-degree sparse representation is claimed — that remains the open `ACC⁰[composite]` crux.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerDigitObserver

/-- The `i`-th base-`p` digit of `s` (the `p`-adic / Witt component): `aᵢ = (s / pⁱ) mod p`. -/
def digit (p i s : ℕ) : ℕ := (s / p ^ i) % p

/-- **The field observer is the lowest digit (proved): `digit p 0 s = s mod p`.**  A characteristic-`p` field observer
sees only `a₀`; the digit decomposition exposes that the field is the bottom of the `p`-adic tower. -/
theorem lowest_digit_eq_mod_p (p s : ℕ) : digit p 0 s = s % p := by simp [digit]

/-- **The digit observer decides `MOD_{p^e}` (proved): `p^e ∣ s ↔ ∀ i < e, digit p i s = 0`.**  Divisibility by `p^e`
is exactly the vanishing of the lowest `e` base-`p` digits `a₀ … a_{e-1}`.  Proved by induction on `e`, peeling one
digit (one factor of `p`) at a time — the genuine digit recursion, not the residue shortcut. -/
theorem digit_observer_decides (p e s : ℕ) (hp : 0 < p) :
    p ^ e ∣ s ↔ ∀ i, i < e → digit p i s = 0 := by
  induction e generalizing s with
  | zero => simp [digit]
  | succ e ih =>
    constructor
    · intro h i hie
      obtain ⟨t, rfl⟩ := h
      unfold digit
      have hsplit : p ^ (e + 1) = p ^ i * p ^ (e + 1 - i) := by rw [← pow_add]; congr 1; omega
      rw [hsplit, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos hp i)]
      have hfac : p ^ (e + 1 - i) = p * p ^ (e + 1 - i - 1) := by
        conv_lhs => rw [show e + 1 - i = (e + 1 - i - 1) + 1 by omega]
        rw [pow_succ']
      rw [hfac, mul_assoc]
      exact Nat.mul_mod_right p _
    · intro h
      have h0 : s % p = 0 := by have := h 0 (by omega); simpa [digit] using this
      obtain ⟨s', rfl⟩ := Nat.dvd_of_mod_eq_zero h0
      have hs' : ∀ i, i < e → digit p i s' = 0 := by
        intro i hie
        have hi := h (i + 1) (by omega)
        unfold digit at hi ⊢
        rw [pow_succ', Nat.mul_div_mul_left _ _ hp] at hi
        exact hi
      obtain ⟨t, rfl⟩ := (ih s').mpr hs'
      exact ⟨t, by rw [pow_succ', mul_assoc]⟩

/-- **The lowest digit alone is insufficient (proved).**  `0` and `p` share the lowest digit (`digit p 0 0 = digit p 0 p
= 0`, since `p mod p = 0`) yet `MOD_{p^e}` accepts `0` and rejects `p` for `e ≥ 2`.  So the field observer — which sees
only `a₀` (`lowest_digit_eq_mod_p`) — cannot compute `MOD_{p^e}`; the higher digits `a₁ … a_{e-1}` are needed. -/
theorem field_digit_insufficient (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    digit p 0 0 = digit p 0 p ∧ p ^ e ∣ 0 ∧ ¬ p ^ e ∣ p := by
  refine ⟨by simp [digit, Nat.mod_self], dvd_zero _, ?_⟩
  intro h
  have hle := Nat.le_of_dvd hp.pos h
  have hlt : p < p ^ e := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerDigitObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerDigitObserver.lowest_digit_eq_mod_p
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerDigitObserver.digit_observer_decides
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerDigitObserver.field_digit_insufficient
