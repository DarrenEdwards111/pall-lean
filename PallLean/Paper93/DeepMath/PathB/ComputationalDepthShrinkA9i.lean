import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9h

/-!
# Shrinkage brick A9i: the miss-count closed form

The card-parameterised recursion `countN` (matching the `missCount` recursion)
has a falling-factorial closed form:

* **`countN_closed` (proved)** — `countN r s b = 2^r · perm r b · perm (s−b) (r−b)`.

The induction step uses `perm_pascal` and the falling-factorial identities from
A9h, with the three-way split on `r` versus `b` handled by `perm_eq_zero`.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- The card-parameterised miss recursion:
`countN r s b` = number (times `2^r`) of `r`-restrictions of an `s`-pool with
`b` marked elements, all marked ending up restricted. -/
def countN : ℕ → ℕ → ℕ → ℕ
  | 0, _, b => if b = 0 then 1 else 0
  | r + 1, s, b => 2 * (b * countN r (s - 1) (b - 1) + (s - b) * countN r (s - 1) b)

theorem perm_zero_eq (b : ℕ) : perm 0 b = if b = 0 then 1 else 0 := by
  cases b with
  | zero => rfl
  | succ b' => simp [perm]

/-- **THE MISS-COUNT CLOSED FORM (proved).** -/
theorem countN_closed : ∀ (r s b : ℕ),
    countN r s b = 2 ^ r * (perm r b * perm (s - b) (r - b)) := by
  intro r
  induction r with
  | zero =>
    intro s b
    show (if b = 0 then 1 else 0) = 2 ^ 0 * (perm 0 b * perm (s - b) (0 - b))
    rw [Nat.zero_sub, pow_zero, one_mul]
    show (if b = 0 then 1 else 0) = perm 0 b * perm (s - b) 0
    rw [← perm_zero_eq b]
    show perm 0 b = perm 0 b * 1
    rw [Nat.mul_one]
  | succ r ih =>
    intro s b
    cases b with
    | zero =>
      show 2 * (0 * countN r (s - 1) (0 - 1) + (s - 0) * countN r (s - 1) 0)
        = 2 ^ (r + 1) * (perm (r + 1) 0 * perm (s - 0) ((r + 1) - 0))
      rw [ih (s - 1) 0]
      simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero]
      show 2 * (s * (2 ^ r * (1 * perm (s - 1) r)))
        = 2 ^ (r + 1) * (1 * (s * perm (s - 1) r))
      rw [pow_succ]; ring
    | succ c =>
      show 2 * ((c + 1) * countN r (s - 1) c + (s - (c + 1)) * countN r (s - 1) (c + 1))
        = 2 ^ (r + 1) * (perm (r + 1) (c + 1) * perm (s - (c + 1)) ((r + 1) - (c + 1)))
      rw [ih (s - 1) c, ih (s - 1) (c + 1)]
      have hRC : (r + 1) - (c + 1) = r - c := by omega
      have hP : perm (r + 1) (c + 1) = (r + 1) * perm r c := rfl
      have hpas : (c + 1) * perm r c + perm r (c + 1) = (r + 1) * perm r c := by
        rw [← hP]; exact (perm_pascal (c + 1) r).symm
      rw [hRC, hP]
      by_cases hrc : c < r
      · -- r ≥ c + 1
        have hA : (s - 1) - c = s - (c + 1) := by omega
        have hB : (s - 1) - (c + 1) = (s - (c + 1)) - 1 := by omega
        have hR2 : r - (c + 1) = (r - c) - 1 := by omega
        have hexp : perm (s - (c + 1)) (r - c)
            = (s - (c + 1)) * perm ((s - (c + 1)) - 1) ((r - c) - 1) := by
          obtain ⟨d, hd⟩ : ∃ d, r - c = d + 1 := ⟨r - c - 1, by omega⟩
          rw [hd]
          show (s - (c + 1)) * perm ((s - (c + 1)) - 1) d
            = (s - (c + 1)) * perm ((s - (c + 1)) - 1) ((d + 1) - 1)
          rfl
        rw [hA, hB, hR2, hexp, ← hpas, pow_succ]
        ring
      · -- r ≤ c
        push_neg at hrc
        have hz : perm r (c + 1) = 0 := perm_eq_zero r (c + 1) (by omega)
        have hrc0 : r - c = 0 := by omega
        rw [hrc0, hz]
        have hpas' : (c + 1) * perm r c = (r + 1) * perm r c := by
          rw [hz] at hpas; omega
        show 2 * ((c + 1) * (2 ^ r * (perm r c * perm (s - (c + 1)) 0))
            + (s - (c + 1)) * (2 ^ r * (0 * perm ((s - 1) - (c + 1)) (r - (c + 1)))))
          = 2 ^ (r + 1) * ((r + 1) * perm r c * perm (s - (c + 1)) 0)
        rw [show perm (s - (c + 1)) 0 = 1 from rfl, ← hpas', pow_succ]
        ring

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.countN_closed
