import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9g

/-!
# Shrinkage brick A9h: the falling-factorial toolkit

The permutation arithmetic the miss-count closed form needs:

* `perm s t = s·(s−1)···(s−t+1)` — the falling factorial `P(s,t)`;
* **`bigN_eq_perm`** — `bigN s r = 2^r · perm s r`;
* **`perm_add`** — `perm n (a+b) = perm n a · perm (n−a) b` (the factorisation);
* **`perm_succ_right`** — `perm r (c+1) = perm r c · (r−c)`;
* **`perm_eq_zero`** — `perm r c = 0` for `r < c`;
* **`perm_pascal`** — `perm (r+1) b = b·perm r (b−1) + perm r b`.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- Falling factorial `P(s,t) = s·(s−1)···(s−t+1)`. -/
def perm : ℕ → ℕ → ℕ
  | _, 0 => 1
  | s, t + 1 => s * perm (s - 1) t

theorem bigN_eq_perm : ∀ (r s : ℕ), bigN s r = 2 ^ r * perm s r := by
  intro r
  induction r with
  | zero => intro s; rfl
  | succ r ih =>
    intro s
    show 2 * s * bigN (s - 1) r = 2 ^ (r + 1) * (s * perm (s - 1) r)
    rw [ih (s - 1), pow_succ]
    ring

/-- **The falling-factorial factorisation (proved).** -/
theorem perm_add : ∀ (a b n : ℕ), perm n (a + b) = perm n a * perm (n - a) b := by
  intro a
  induction a with
  | zero =>
    intro b n
    show perm n (0 + b) = perm n 0 * perm (n - 0) b
    rw [Nat.zero_add, Nat.sub_zero]
    show perm n b = 1 * perm n b
    rw [one_mul]
  | succ a ih =>
    intro b n
    show perm n (a + 1 + b) = perm n (a + 1) * perm (n - (a + 1)) b
    have h1 : a + 1 + b = (a + b) + 1 := by omega
    rw [h1]
    show n * perm (n - 1) (a + b) = perm n (a + 1) * perm (n - (a + 1)) b
    rw [ih b (n - 1)]
    show n * (perm (n - 1) a * perm ((n - 1) - a) b)
      = (n * perm (n - 1) a) * perm (n - (a + 1)) b
    have h3 : n - (a + 1) = (n - 1) - a := by omega
    rw [h3]
    ring

/-- **Right multiplication (proved)**: `perm r (c+1) = perm r c · (r − c)`. -/
theorem perm_succ_right : ∀ (c r : ℕ), perm r (c + 1) = perm r c * (r - c) := by
  intro c
  induction c with
  | zero =>
    intro r
    show r * perm (r - 1) 0 = 1 * (r - 0)
    rw [Nat.sub_zero]
    show r * 1 = 1 * r
    ring
  | succ c ih =>
    intro r
    show r * perm (r - 1) (c + 1) = (r * perm (r - 1) c) * (r - (c + 1))
    rw [ih (r - 1)]
    have h : (r - 1) - c = r - (c + 1) := by omega
    rw [h]
    ring

theorem perm_eq_zero_aux : ∀ (d r : ℕ), perm r (r + 1 + d) = 0 := by
  intro d
  induction d with
  | zero =>
    intro r
    show perm r (r + 1) = 0
    rw [perm_succ_right r r, Nat.sub_self, Nat.mul_zero]
  | succ d ih =>
    intro r
    have h : r + 1 + (d + 1) = (r + 1 + d) + 1 := by omega
    rw [h, perm_succ_right (r + 1 + d) r, ih r]
    ring

/-- **Vanishing (proved)**: `perm r c = 0` when `r < c`. -/
theorem perm_eq_zero (r c : ℕ) (hrc : r < c) : perm r c = 0 := by
  obtain ⟨d, hd⟩ : ∃ d, c = r + 1 + d := ⟨c - (r + 1), by omega⟩
  rw [hd]
  exact perm_eq_zero_aux d r

/-- **Pascal identity (proved)**: `perm (r+1) b = b·perm r (b−1) + perm r b`. -/
theorem perm_pascal : ∀ (b r : ℕ),
    perm (r + 1) b = b * perm r (b - 1) + perm r b := by
  intro b
  cases b with
  | zero => intro r; show (1 : ℕ) = 0 * perm r 0 + 1; ring
  | succ c =>
    intro r
    show (r + 1) * perm r c = (c + 1) * perm r c + perm r (c + 1)
    rw [perm_succ_right c r]
    by_cases hcr : c ≤ r
    · have hR : (c + 1) * perm r c + perm r c * (r - c)
          = perm r c * ((c + 1) + (r - c)) := by ring
      have h : (c + 1) + (r - c) = r + 1 := by omega
      rw [hR, h]
      ring
    · push_neg at hcr
      rw [perm_eq_zero r c hcr]
      ring

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.bigN_eq_perm
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.perm_add
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.perm_pascal
