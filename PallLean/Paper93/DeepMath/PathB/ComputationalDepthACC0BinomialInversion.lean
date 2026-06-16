import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LevelCounts

/-!
# Binomial inversion — recovering the level-counts `N_t` from the moments `B_d`

The bridge `…ACC0LevelCounts.binomial_moment_eq_sum_levels` gives `B_d = ∑_t N_t·C(t,d)`, a unit-upper-triangular
system.  This file proves its **inversion**: the level-counts are an explicit alternating combination of the
(kernel-computable) binomial moments,

```
N_s  =  Σ_d  (-1)^{d-s} · C(d,s) · B_d .
```

The engine is the **binomial orthogonality** `Σ_d (-1)^{d-s} C(d,s) C(t,d) = δ_{s,t}`, proved from the subset-of-subset
identity `C(t,d)·C(d,s) = C(t,s)·C(t-s,d-s)` (`Nat.choose_mul`) and the alternating row-sum
`Σ_e (-1)^e C(m,e) = [m=0]` (`Int.alternating_sum_range_choose`).

## What is proved (clean axioms, no `sorry`)

* **`binom_orthogonality`** — `Σ_{d≤K} (-1)^{d-s} C(d,s) C(t,d) = if t = s then 1 else 0` (for `t ≤ K`).
* **`binomial_inversion`** — `B_d = Σ_t N_t·C(t,d)` ⇒ `N_s = Σ_d (-1)^{d-s} C(d,s) B_d` (over `ℤ`, `s ≤ K`).
* **`levelCount_eq_inversion`** — the level-count as an alternating sum of binomial moments:
  `(N_s : ℤ) = Σ_d (-1)^{d-s} C(d,s) · (∑_x C(andCount x, d))`.

## Honest scope

This closes the algebraic half of the per-level count: the `N_t` are an *explicit* alternating combination of the
binomial moments, each of which is a sparse cube-sum (`…ACC0ElementarySymmetric`, `…ACC0SparseCounting`).  The one
remaining algorithmic input is the Beigel–Tarui quasipolynomial `#monomials` bound for `ACC⁰`.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BinomialInversion

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0SymLayerReduction
open PallLean.Paper93.DeepMath.PathB.ACC0LevelCounts

/-- **Binomial orthogonality (proved): `Σ_{d≤K} (-1)^{d-s} C(d,s) C(t,d) = δ_{s,t}`.** -/
theorem binom_orthogonality {K : ℕ} (s t : ℕ) (hsK : s ≤ K) (htK : t ≤ K) :
    (∑ d ∈ Finset.range (K + 1), ((-1 : ℤ)) ^ (d - s) * (d.choose s : ℤ) * (t.choose d : ℤ))
      = if t = s then 1 else 0 := by
  have hterm : ∀ d ∈ Finset.range (K + 1),
      ((-1 : ℤ)) ^ (d - s) * (d.choose s : ℤ) * (t.choose d : ℤ)
        = (if s ≤ d then
            (t.choose s : ℤ) * (((-1 : ℤ)) ^ (d - s) * ((t - s).choose (d - s) : ℤ)) else 0) := by
    intro d _
    by_cases hsd : s ≤ d
    · rw [if_pos hsd]
      have hcd : (d.choose s : ℤ) * (t.choose d : ℤ) = (t.choose s : ℤ) * ((t - s).choose (d - s) : ℤ) := by
        rw [mul_comm]; exact_mod_cast Nat.choose_mul hsd
      rw [mul_assoc, hcd]; ring
    · rw [if_neg hsd, Nat.choose_eq_zero_of_lt (not_le.mp hsd)]; push_cast; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.mul_sum]
  have hfilt : (Finset.range (K + 1)).filter (fun d => s ≤ d) = Finset.Ico s (K + 1) := by
    ext d; simp [Finset.mem_Ico, Finset.mem_range, and_comm]
  rw [hfilt, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  have hext : (∑ e ∈ Finset.range (K + 1 - s), ((-1 : ℤ)) ^ e * ((t - s).choose e : ℤ))
      = ∑ e ∈ Finset.range ((t - s) + 1), ((-1 : ℤ)) ^ e * ((t - s).choose e : ℤ) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro e he
      simp only [Finset.mem_range] at he ⊢
      omega
    · intro e _ he
      simp only [Finset.mem_range, not_lt] at he
      rw [Nat.choose_eq_zero_of_lt he]; push_cast; ring
  rw [hext, Int.alternating_sum_range_choose]
  rcases lt_trichotomy t s with h | h | h
  · simp [Nat.choose_eq_zero_of_lt h, Nat.sub_eq_zero_of_le (le_of_lt h), Nat.ne_of_lt h]
  · subst h; simp
  · have h1 : t - s ≠ 0 := by omega
    have h2 : t ≠ s := by omega
    simp [h1, h2]

/-- **Binomial inversion (proved): `B_d = Σ_t N_t·C(t,d)` ⇒ `N_s = Σ_d (-1)^{d-s} C(d,s) B_d`.** -/
theorem binomial_inversion {K : ℕ} (N B : ℕ → ℤ)
    (hB : ∀ d, B d = ∑ t ∈ Finset.range (K + 1), N t * (t.choose d : ℤ)) (s : ℕ) (hsK : s ≤ K) :
    N s = ∑ d ∈ Finset.range (K + 1), ((-1 : ℤ)) ^ (d - s) * (d.choose s : ℤ) * B d := by
  rw [show (∑ d ∈ Finset.range (K + 1), ((-1 : ℤ)) ^ (d - s) * (d.choose s : ℤ) * B d)
        = ∑ d ∈ Finset.range (K + 1), ∑ t ∈ Finset.range (K + 1),
            ((-1 : ℤ)) ^ (d - s) * (d.choose s : ℤ) * (N t * (t.choose d : ℤ)) from ?_]
  · rw [Finset.sum_comm,
      show (∑ t ∈ Finset.range (K + 1), ∑ d ∈ Finset.range (K + 1),
              ((-1 : ℤ)) ^ (d - s) * (d.choose s : ℤ) * (N t * (t.choose d : ℤ)))
            = ∑ t ∈ Finset.range (K + 1), N t * (if t = s then 1 else 0) from ?_]
    · rw [Finset.sum_congr rfl (fun t _ => by rw [mul_ite, mul_one, mul_zero]),
        Finset.sum_ite_eq' (Finset.range (K + 1)) s N,
        if_pos (Finset.mem_range_succ_iff.mpr hsK)]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [← binom_orthogonality s t hsK (Finset.mem_range_succ_iff.mp ht), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
  · apply Finset.sum_congr rfl
    intro d _
    rw [hB d, Finset.mul_sum]

/-- **The level-count as an alternating sum of binomial moments (proved).** -/
theorem levelCount_eq_inversion {n k : ℕ} (gates : Fin k → Finset (Fin n)) (s : ℕ) (hsk : s ≤ k) :
    (levelCount gates s : ℤ)
      = ∑ d ∈ Finset.range (k + 1), ((-1 : ℤ)) ^ (d - s) * (d.choose s : ℤ)
          * (∑ x : Fin n → Bool, ((andCount gates x).choose d : ℤ)) := by
  apply binomial_inversion (N := fun t => (levelCount gates t : ℤ))
    (B := fun d => ∑ x : Fin n → Bool, ((andCount gates x).choose d : ℤ)) ?_ s hsk
  intro d
  show (∑ x : Fin n → Bool, ((andCount gates x).choose d : ℤ))
      = ∑ t ∈ Finset.range (k + 1), (levelCount gates t : ℤ) * (t.choose d : ℤ)
  rw [← Nat.cast_sum, binomial_moment_eq_sum_levels gates d]
  push_cast
  rfl

end PallLean.Paper93.DeepMath.PathB.ACC0BinomialInversion

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BinomialInversion.binom_orthogonality
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BinomialInversion.binomial_inversion
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BinomialInversion.levelCount_eq_inversion
