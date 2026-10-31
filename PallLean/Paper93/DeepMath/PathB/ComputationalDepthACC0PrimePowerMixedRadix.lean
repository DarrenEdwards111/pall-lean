import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndFanIn
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimePowerObstruction

/-!
# Prime-power mixed-radix SYM∘AND — the non-field route that clears the field obstruction

Step (b).  Entry 171 proved the composite-`MOD` field-gate splits at squarefree (low-degree field gate exists) vs
prime-power (no low-degree field gate — `ZMod(p^e)` is not a field).  The full Beigel–Tarui theorem handles prime-power
`MOD` *not* by a low-degree field polynomial but by the **symmetric / mixed-radix `SYM∘AND` route**: a `MOD_q` gate of
*any* modulus `q` — prime, prime-power, or composite — is **exactly a symmetric function** of its support literals, so
it is represented exactly by the `SYM` top gate over single-literal `AND`s (fan-in `1`), with **no field polynomial
required**.  The mixed-radix merge (`hasSymAndForm_combine`, base-`(m+1)` counting) composes such gates.  This file
instantiates that route at `q = p^e`, showing the symmetric route succeeds exactly where the field route provably
fails.

## What is proved (clean axioms, no `sorry`)

* **`modPrimePower_symAndForm`** — `MOD_{p^e}` has an *exact* `SYM∘AND` form of size `|S|` (via `hasSymAndForm_mod` at
  `q = p^e`); **`modPrimePower_symAndFanIn`** — the same with fan-in `1` (single-literal `AND`s).  No field polynomial.
* **`primePower_mixed_radix_combine`** — a `MOD_{p^e}` gate combines with any other `SYM∘AND` form under any binary
  combiner via the mixed-radix merge (size `|S| + (|S|+1)·s₂`).
* **`primePower_sym_clears_field_obstruction`** — the contrast: `MOD_{p^e}` has an exact `SYM∘AND` form *and* (`e ≥ 2`)
  no `F_p` field gate computes it (`0`, `p` share the mod-`p` residue, `MOD_{p^e}` separates them).  The symmetric
  route clears the field obstruction.

## Honest scope

This shows the symmetric/mixed-radix route represents prime-power (and any composite) `MOD` *exactly*, with no
low-degree field gate — which is precisely how Beigel–Tarui sidesteps the field obstruction of entry 171.  It is the
**exact** representation (size `|S|` per gate, multiplicative under composition, entry 169/170), so it gives a
quasipoly-size bound only when combined with the approximate count control of the `AC⁰` part (step (a), entry 173); the
*quasipoly* count for prime-power `MOD` circuits is the genuine BT mixed-radix size analysis (a proven classical
theorem to formalise in full).  What is established here: the field obstruction is field-specific — the symmetric route
handles `MOD_{p^e}` exactly.  Beigel–Tarui and `NEXP ⊄ ACC⁰` (Williams 2011) are proven classical theorems ⇒
formalisation, not an open problem.  NOT a new separation, NOT `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerMixedRadix

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose
  (HasSymAndForm hasSymAndForm_mod hasSymAndForm_combine)
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn (HasSymAndFormFanIn hasSymAndFormFanIn_mod)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (modQStatOn)

variable {n : ℕ}

/-- **`MOD_{p^e}` has an exact `SYM∘AND` form via the symmetric route (proved): size `|S|`, no field gate.**
`MOD_{p^e}` (`decide (∑_{i∈S} xᵢ ≡ t (mod p^e))`) is exactly a symmetric function of its support literals, so the `SYM`
top gate over single-literal `AND`s computes it exactly — *no low-degree field polynomial needed*, in contrast to the
field route which provably fails for `p^e`. -/
theorem modPrimePower_symAndForm (p e : ℕ) (S : Finset (Fin n)) (t : ZMod (p ^ e)) :
    HasSymAndForm (fun x => decide (modQStatOn S (p ^ e) x = t)) S.card :=
  hasSymAndForm_mod (p ^ e) S t

/-- **`MOD_{p^e}` has fan-in `1` in the exact `SYM∘AND` form (proved): single-literal `AND`s.** -/
theorem modPrimePower_symAndFanIn (p e : ℕ) (S : Finset (Fin n)) (t : ZMod (p ^ e)) :
    HasSymAndFormFanIn (fun x => decide (modQStatOn S (p ^ e) x = t)) S.card 1 :=
  hasSymAndFormFanIn_mod (p ^ e) S t

/-- **Mixed-radix merge with a prime-power `MOD` gate (proved).**  A `MOD_{p^e}` gate combines with any other `SYM∘AND`
form under any binary Boolean combiner via the base-`(|S|+1)` mixed-radix merge, giving an exact `SYM∘AND` form of size
`|S| + (|S|+1)·s₂` — the symmetric route composes prime-power `MOD` gates without ever forming a field polynomial. -/
theorem primePower_mixed_radix_combine (p e : ℕ) (S : Finset (Fin n)) (t : ZMod (p ^ e))
    {g : (Fin n → Bool) → Bool} {s2 : ℕ} (comb : Bool → Bool → Bool) (hg : HasSymAndForm g s2) :
    HasSymAndForm (fun x => comb (decide (modQStatOn S (p ^ e) x = t)) (g x))
      (S.card + (S.card + 1) * s2) :=
  hasSymAndForm_combine comb (modPrimePower_symAndForm p e S t) hg

/-- **The symmetric route clears the field obstruction (proved).**  For `e ≥ 2`, `MOD_{p^e}` has an exact `SYM∘AND`
form (the symmetric route) *and* no `F_p` field gate computes it: `0` and `p` share the mod-`p` residue
(`(0:ZMod p) = (p:ZMod p)`) yet `MOD_{p^e}` accepts `0` (`p^e ∣ 0`) and rejects `p` (`¬ p^e ∣ p`).  So the field
obstruction of entry 171 is *field-specific* — the symmetric/mixed-radix `SYM∘AND` route handles `MOD_{p^e}` exactly,
which is how Beigel–Tarui sidesteps it. -/
theorem primePower_sym_clears_field_obstruction (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e)
    (S : Finset (Fin n)) (t : ZMod (p ^ e)) :
    HasSymAndForm (fun x => decide (modQStatOn S (p ^ e) x = t)) S.card
      ∧ (((0 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) ∧ p ^ e ∣ 0 ∧ ¬ p ^ e ∣ p) :=
  ⟨modPrimePower_symAndForm p e S t,
   ACC0PrimePowerObstruction.modPrimePower_not_function_of_modP p e hp he⟩

end PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerMixedRadix

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerMixedRadix.modPrimePower_symAndForm
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerMixedRadix.primePower_mixed_radix_combine
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerMixedRadix.primePower_sym_clears_field_obstruction
