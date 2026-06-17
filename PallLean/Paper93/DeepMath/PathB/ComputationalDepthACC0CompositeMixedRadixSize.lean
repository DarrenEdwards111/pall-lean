import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTExactCompose

/-!
# Composite mixed-radix quasipoly-size — combining a constant number of forms stays quasipoly

The last residual of the BT closure (entry 177): for *composite* modulus the agreement was assembled only per prime
(`MOD_p`).  By CRT (entry 171) a squarefree composite `MOD_m = ⋀_{i} MOD_{pᵢ}` over the distinct prime factors of `m`;
and each `MOD_{pᵢ}` (or its RS approximant over `F_{pᵢ}`) has a quasipolynomial-size `SYM∘AND` form (entries 174/177).
This file proves the **mixed-radix size analysis**: combining a *constant* number `k` of `SYM∘AND` forms, each of size
`≤ Q`, via the base-`(s+1)` mixed-radix merge yields a `SYM∘AND` form of size `≤ (Q+1)^k − 1`.  For `k = ω(m)` the
number of distinct prime factors (a *constant* for a fixed modulus `m`) and `Q` quasipolynomial, `(Q+1)^k` is
quasipolynomial — so the combined composite representation stays quasipoly-size.

The size recurrence is exact: combining one new form (size `≤ Q`) with an accumulated form (size `s`) gives
`s + (s+1)·Q` (`hasSymAndForm_combine`), and `mrBound Q (k+1) + 1 = (Q+1)·(mrBound Q k + 1)`, so
`mrBound Q k = (Q+1)^k − 1`.  The point is that this is `(quasipoly)^{constant} = quasipoly`, *not* exponential —
because the number of moduli is fixed.

## What is proved (clean axioms, no `sorry`)

* **`hasSymAndForm_mono`** — `HasSymAndForm` is monotone in the size bound.
* **`mrBound` / `mrBound_eq` / `mrBound_le_pow`** — the mixed-radix size recurrence; `mrBound Q k = (Q+1)^k − 1 ≤ (Q+1)^k`.
* **`andAll` / `hasSymAndForm_andAll`** — the AND of a list of forms (each `≤ Q`) has a `SYM∘AND` form of size
  `≤ mrBound Q (length)`.
* **`mixedRadix_quasipoly_size`** — the AND of `forms` (each of size `≤ Q`) has `SYM∘AND` size `≤ (Q+1)^{forms.length}`
  — quasipolynomial for a constant number of forms and quasipolynomial `Q`.

## Honest scope

This proves the size analysis: combining a *constant* number of quasipoly-size forms via the mixed-radix merge stays
quasipoly.  Applied to a squarefree composite `MOD_m = ⋀ MOD_{pᵢ}` over its (constantly-many) prime factors, with each
per-prime `SYM∘AND` form quasipoly (entries 174/177), the composite form is quasipoly-size — discharging the *size*
content of the composite residual.  It does **not** itself perform the per-prime RS approximation of a whole composite
circuit (that is entry 177 applied over each `F_{pᵢ}`), nor handle the modulus being part of the input (`m` is fixed,
so its number of prime factors is a constant).  Beigel–Tarui and `NEXP ⊄ ACC⁰` (Williams 2011) are proven classical
theorems ⇒ formalisation, not an open problem.  NOT a new separation, NOT `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeMixedRadixSize

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose
  (HasSymAndForm hasSymAndForm_const hasSymAndForm_combine)

variable {n : ℕ}

/-- **`HasSymAndForm` is monotone in the size bound (proved).** -/
theorem hasSymAndForm_mono {f : (Fin n → Bool) → Bool} {s s' : ℕ}
    (hf : HasSymAndForm f s) (hss : s ≤ s') : HasSymAndForm f s' := by
  obtain ⟨ι, hι, mono, h, hcard, hfe⟩ := hf
  exact ⟨ι, hι, mono, h, le_trans hcard hss, hfe⟩

/-- The mixed-radix size after combining `k` forms each of size `≤ Q`: one merge step is `s ↦ Q + (Q+1)·s`. -/
def mrBound (Q : ℕ) : ℕ → ℕ
  | 0 => 0
  | (k + 1) => Q + (Q + 1) * mrBound Q k

/-- **The merge step on `mrBound + 1` is multiplication by `Q+1` (proved).** -/
theorem mrBound_succ_add_one (Q k : ℕ) : mrBound Q (k + 1) + 1 = (Q + 1) * (mrBound Q k + 1) := by
  simp only [mrBound]; ring

/-- **Closed form (proved): `mrBound Q k = (Q+1)^k − 1`.**  The mixed-radix size of combining `k` forms each `≤ Q`. -/
theorem mrBound_eq (Q k : ℕ) : mrBound Q k + 1 = (Q + 1) ^ k := by
  induction k with
  | zero => simp [mrBound]
  | succ k ih => rw [mrBound_succ_add_one, ih, pow_succ]; ring

/-- **`mrBound Q k ≤ (Q+1)^k` (proved).**  Quasipolynomial for constant `k` and quasipolynomial `Q`. -/
theorem mrBound_le_pow (Q k : ℕ) : mrBound Q k ≤ (Q + 1) ^ k := by
  have := mrBound_eq Q k; omega

/-- The `AND` of a list of Boolean functions. -/
def andAll (forms : List ((Fin n → Bool) → Bool)) : (Fin n → Bool) → Bool :=
  fun x => forms.foldr (fun f acc => f x && acc) true

/-- **The `AND` of a list of `SYM∘AND` forms is a `SYM∘AND` form of size `≤ mrBound Q (length)` (proved).**  Iterated
mixed-radix merge over the list: each form (size `≤ Q`) merged into the accumulated form. -/
theorem hasSymAndForm_andAll (Q : ℕ) :
    ∀ (forms : List ((Fin n → Bool) → Bool)),
      (∀ f ∈ forms, ∃ s, HasSymAndForm f s ∧ s ≤ Q) →
      HasSymAndForm (andAll forms) (mrBound Q forms.length)
  | [], _ => by simpa [andAll, mrBound] using hasSymAndForm_const (n := n) true
  | (f :: fs), hforms => by
      obtain ⟨sf, hsf, hsfQ⟩ := hforms f (by simp)
      have hrest := hasSymAndForm_andAll Q fs (fun g hg => hforms g (by simp [hg]))
      have hcomb := hasSymAndForm_combine (· && ·)
        (hasSymAndForm_mono hsf hsfQ) (hasSymAndForm_mono hrest (le_refl _))
      have hand : andAll (f :: fs) = fun x => (f x) && (andAll fs x) := by funext x; simp [andAll]
      rw [hand]
      simpa [mrBound, List.length_cons] using hcomb

/-- **Composite mixed-radix quasipoly size (proved): the `AND` of `forms` has `SYM∘AND` size `≤ (Q+1)^{length}`.**  For a
*constant* number of forms (e.g. the `ω(m)` distinct prime factors of a fixed squarefree modulus `m`) and a
quasipolynomial per-form size `Q`, `(Q+1)^{length}` is quasipolynomial — so the combined composite `SYM∘AND` form stays
quasipoly-size, discharging the size content of the composite residual. -/
theorem mixedRadix_quasipoly_size (Q : ℕ) (forms : List ((Fin n → Bool) → Bool))
    (hforms : ∀ f ∈ forms, ∃ s, HasSymAndForm f s ∧ s ≤ Q) :
    HasSymAndForm (andAll forms) ((Q + 1) ^ forms.length) :=
  hasSymAndForm_mono (hasSymAndForm_andAll Q forms hforms) (mrBound_le_pow Q forms.length)

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeMixedRadixSize

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMixedRadixSize.mrBound_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMixedRadixSize.hasSymAndForm_andAll
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMixedRadixSize.mixedRadix_quasipoly_size
