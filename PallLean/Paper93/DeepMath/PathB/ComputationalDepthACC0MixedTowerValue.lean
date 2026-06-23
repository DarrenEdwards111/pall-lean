import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaModGate

/-!
# The mixed `MOD`/`AND` tower, value side: `rep ≡ val (mod p^{2^k})` (PROVED)

The value side of the mixed tower (`ACC0MixedTowerDegree` gave the degree side).  A value-level mixed
tower (leaf count, `MOD_p` node, `AND` node) has its Toda/product representation `mrepv` congruent to its
Boolean value `mval` modulo `p^{2^k}` at arbitrary depth:

  `mixed_tower` — for every `MixedModTower t`: `p^{2^k} ∣ (mrepv t − mval t)`.

`MOD` nodes flow as in `ACC0TodaTower` (weaken `mod p^{2^k} → mod p`, count transfers, `A^{[k]}`
re-amplifies); **`AND` nodes** use the **product congruence**: if each `rep_i ≡ val_i (mod M)` then
`∏ rep_i ≡ ∏ val_i (mod M)`, and `∏ val_i` is the `AND` of the `{0,1}` child values.  No weakening is
needed for `AND` — the product preserves the full modulus `p^{2^k}`.

Together with `ACC0MixedTowerDegree` (degree `≤ (max w (3^k(p−1)))^depth`) the mixed `MOD`/`AND` tower is
now bounded in **both** value and degree.

## What is proved (clean axioms, no `sorry`)

* `MixedModTower`, `mval`, `mrepv` — the value-level mixed tower, Boolean value, Toda/product rep.
* `dvd_sum_sub`, `dvd_prod_sub` — list sum/product divisibility transfer.
* `mixed_tower` / `mixed_tower_list` — `p^{2^k} ∣ (mrepv t − mval t)` (mutual recursion).

## Honest scope

Value side of the mixed (`MOD`-Toda + `AND`) tower.  `OR` is the De Morgan analogue; unbounded `AND`/`OR`
degree is the no-go (RS); the exact-quasipoly `2^k` choice and the `SYM∘AND` assembly remain the
Beigel–Tarui wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MixedTowerValue

open PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate (todaMod_amplifies)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate (todaAmpIter)

/-- A value-level mixed `MOD`/`AND` tower. -/
inductive MixedModTower where
  | leaf : ℤ → MixedModTower
  | modN : List MixedModTower → MixedModTower
  | andN : List MixedModTower → MixedModTower

/-- The Boolean value: `MOD` of accepting-child counts, `AND` = product of child values. -/
def mval (p : ℕ) : MixedModTower → ℤ
  | .leaf y => if (p : ℤ) ∣ y then 1 else 0
  | .modN ts => if (p : ℤ) ∣ ((ts.map (mval p)).sum) then 1 else 0
  | .andN ts => (ts.map (mval p)).prod

/-- The representation: `MOD` via Toda, `AND` via product. -/
def mrepv (p k : ℕ) : MixedModTower → ℤ
  | .leaf y => todaAmpIter k (1 - y ^ (p - 1))
  | .modN ts => todaAmpIter k (1 - ((ts.map (mrepv p k)).sum) ^ (p - 1))
  | .andN ts => (ts.map (mrepv p k)).prod

/-- **List-sum divisibility transfer (proved).** -/
theorem dvd_sum_sub {M : ℤ} (f g : MixedModTower → ℤ) :
    (l : List MixedModTower) → (∀ t ∈ l, M ∣ (f t - g t)) →
      M ∣ ((l.map f).sum - (l.map g).sum)
  | [], _ => by simp
  | a :: t, h => by
      simp only [List.map_cons, List.sum_cons]
      have h1 : M ∣ (f a - g a) := h a (by simp)
      have h2 : M ∣ ((t.map f).sum - (t.map g).sum) :=
        dvd_sum_sub f g t (fun x hx => h x (by simp [hx]))
      have he : (f a + (t.map f).sum) - (g a + (t.map g).sum)
          = (f a - g a) + ((t.map f).sum - (t.map g).sum) := by ring
      rw [he]; exact dvd_add h1 h2

/-- **List-product divisibility transfer (proved): `∏ f ≡ ∏ g (mod M)` from termwise.** -/
theorem dvd_prod_sub {M : ℤ} (f g : MixedModTower → ℤ) :
    (l : List MixedModTower) → (∀ t ∈ l, M ∣ (f t - g t)) →
      M ∣ ((l.map f).prod - (l.map g).prod)
  | [], _ => by simp
  | a :: t, h => by
      simp only [List.map_cons, List.prod_cons]
      have h1 : M ∣ (f a - g a) := h a (by simp)
      have h2 : M ∣ ((t.map f).prod - (t.map g).prod) :=
        dvd_prod_sub f g t (fun x hx => h x (by simp [hx]))
      have he : f a * (t.map f).prod - g a * (t.map g).prod
          = f a * ((t.map f).prod - (t.map g).prod) + (f a - g a) * (t.map g).prod := by ring
      rw [he]; exact dvd_add (h2.mul_left _) (h1.mul_right _)

mutual

/-- **Mixed-tower value congruence (proved): `p^{2^k} ∣ (mrepv t − mval t)`.** -/
theorem mixed_tower (p k : ℕ) [Fact p.Prime] :
    (t : MixedModTower) → (p : ℤ) ^ (2 ^ k) ∣ (mrepv p k t - mval p t)
  | .leaf y => by rw [mrepv, mval]; exact todaMod_amplifies p y k
  | .andN ts => by
      have hchild : ∀ t ∈ ts, (p : ℤ) ^ (2 ^ k) ∣ (mrepv p k t - mval p t) :=
        fun t ht => mixed_tower_list p k ts t ht
      rw [mrepv, mval]
      exact dvd_prod_sub (mrepv p k) (mval p) ts hchild
  | .modN ts => by
      have hchild : ∀ t ∈ ts, (p : ℤ) ∣ (mrepv p k t - mval p t) := fun t ht =>
        dvd_trans (dvd_pow_self (p : ℤ) (by positivity : (2 : ℕ) ^ k ≠ 0))
          (mixed_tower_list p k ts t ht)
      have hY : (p : ℤ) ∣ ((ts.map (mrepv p k)).sum - (ts.map (mval p)).sum) :=
        dvd_sum_sub (mrepv p k) (mval p) ts hchild
      have hiff : ((p : ℤ) ∣ (ts.map (mrepv p k)).sum) ↔ ((p : ℤ) ∣ (ts.map (mval p)).sum) := by
        constructor
        · intro h
          have h2 := dvd_sub h hY
          rwa [show (ts.map (mrepv p k)).sum - ((ts.map (mrepv p k)).sum - (ts.map (mval p)).sum)
            = (ts.map (mval p)).sum from by ring] at h2
        · intro h
          have h2 := dvd_add h hY
          rwa [show (ts.map (mval p)).sum + ((ts.map (mrepv p k)).sum - (ts.map (mval p)).sum)
            = (ts.map (mrepv p k)).sum from by ring] at h2
      have htoda := todaMod_amplifies p ((ts.map (mrepv p k)).sum) k
      have heq : (if (p : ℤ) ∣ (ts.map (mval p)).sum then (1 : ℤ) else 0)
          = (if (p : ℤ) ∣ (ts.map (mrepv p k)).sum then (1 : ℤ) else 0) := by
        by_cases h : (p : ℤ) ∣ (ts.map (mrepv p k)).sum
        · rw [if_pos (hiff.mp h), if_pos h]
        · rw [if_neg (fun hv => h (hiff.mpr hv)), if_neg h]
      rw [mrepv, mval, heq]
      exact htoda

/-- List companion. -/
theorem mixed_tower_list (p k : ℕ) [Fact p.Prime] :
    (ts : List MixedModTower) → ∀ t ∈ ts, (p : ℤ) ^ (2 ^ k) ∣ (mrepv p k t - mval p t)
  | [] => fun t ht => absurd ht (by simp)
  | a :: ts => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact mixed_tower p k t
      · exact mixed_tower_list p k ts t hmem

end

/-!
**Mixed-tower value congruence proved.**  `p^{2^k} ∣ (mrepv t − mval t)` for every mixed `MOD`/`AND`
tower: `MOD` flows via Toda, `AND` via the product congruence (no weakening).  With
`ACC0MixedTowerDegree` the mixed tower is bounded in both value and degree.  `OR`, the exact-quasipoly
`2^k` choice, and the `SYM∘AND` assembly remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0MixedTowerValue

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MixedTowerValue.mixed_tower
