import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSymDegree

/-!
# The small-characteristic composite-MOD case: the arithmetisation does not exist

C13 bounded `deg P` for the outer symmetric gate by the fan-in `s` — but only when the `s+1` interpolation nodes are
distinct, i.e. `char 0` or `char > s`.  This file handles the remaining case: **small characteristic** `char = ℓ ≤ s`
with a **composite** `MOD_m` gate.

The honest resolution is a *non-existence* theorem.  Over a field of characteristic `ℓ`, the `F`-sum of `c` Boolean
products is `(c : F) = (c mod ℓ)` — it only tracks the count *modulo `ℓ`*.  A `MOD_m` gate needs the count *modulo `m`*,
and when `m ∤ ℓ` these disagree (counts `0` and `ℓ` collide in `F` but have different `MOD_m` value).  So:

  `modmGate_not_evalPoly_of_char` — if `(ℓ : F) = 0` and `m ∤ ℓ`, there is **no** univariate `P` with
        `[c ≡ 0 mod m] = eval (c : F) P` for all counts `c`.  The composite-`MOD_m` gate is not *any* polynomial of the
        characteristic-collapsed sum — not merely high-degree, it does not exist.
  `modmGate_not_evalPoly_of_ringChar` — the same in terms of `ringChar F`.

So over the small field `F_ℓ` natural to `MOD_ℓ` gates, a composite `MOD_m` (`m ∤ ℓ`) has **no** `P(∑∏)` arithmetisation
at all.  Together with C13 (`char > s ⟹ deg P ≤ s`) this fully splits the outer layer:
* `char > fan-in`: `deg P ≤ s`, the method works (`modq_BTsize_lb`);
* `char ≤ fan-in`, composite `MOD_m` (`m ∤ char`): no `P` exists — the polynomial method over `F_ℓ` cannot represent it.

## The way around, and the genuine open barrier

The escape used for `MOD_q` (C11) is a *root-of-unity* arithmetisation — `omegaFn = ω^{∑}` with `ω` of order `q` in an
extension of `F_ℓ` — which tracks the count mod `q` *without* casting into `F_ℓ`.  This works for a **prime-power**
modulus (one `ω`).  A genuine composite `m = p₁ᵉ¹⋯` needs one root of unity per prime-power factor (CRT), and the
combined object keeps *high* multilinear (N-Frame) complexity — no single low-degree polynomial of the sum captures it.
That is the standing `MOD_6`-type barrier: this file proves the naive `P(∑∏)`-over-`F_ℓ` route provably fails, isolating
exactly why one must go to roots of unity, and why composite (multi-prime) modulus stays open.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open Polynomial

variable {F : Type*} [Field F]

/-- **The composite-MOD obstruction (proved)**: over a field where `(ℓ : F) = 0` (characteristic divides `ℓ`), if
`m ∤ ℓ` then the `MOD_m` gate is *not* the evaluation of any univariate polynomial on the natural-number casts — the
characteristic-collapsed sum only sees the count mod `ℓ`, but `MOD_m` needs it mod `m`.  Counts `0` and `ℓ` collide in
`F` yet differ under `MOD_m`. -/
theorem modmGate_not_evalPoly_of_char (ℓ m : ℕ) (hℓ : (ℓ : F) = 0) (hmℓ : ¬ m ∣ ℓ) :
    ¬ ∃ P : Polynomial F, ∀ c : ℕ, (if c % m = 0 then (1 : F) else 0) = Polynomial.eval (c : F) P := by
  rintro ⟨P, hP⟩
  have h0 := hP 0
  have hℓe := hP ℓ
  simp only [Nat.zero_mod, Nat.cast_zero, if_pos] at h0
  rw [hℓ, if_neg (fun h => hmℓ (Nat.dvd_of_mod_eq_zero h))] at hℓe
  exact one_ne_zero (h0.trans hℓe.symm)

/-- **The composite-MOD obstruction, via `ringChar` (proved)**: in characteristic `ringChar F ≠ 0`, a composite `MOD_m`
gate with `m ∤ ringChar F` has no polynomial arithmetisation of the (characteristic-collapsed) sum. -/
theorem modmGate_not_evalPoly_of_ringChar (m : ℕ) (hmℓ : ¬ m ∣ ringChar F) :
    ¬ ∃ P : Polynomial F, ∀ c : ℕ, (if c % m = 0 then (1 : F) else 0) = Polynomial.eval (c : F) P :=
  modmGate_not_evalPoly_of_char (ringChar F) m
    ((ringChar.spec F (ringChar F)).mpr (dvd_refl _)) hmℓ

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.modmGate_not_evalPoly_of_char
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.modmGate_not_evalPoly_of_ringChar
