import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaModGate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OrNode

/-!
# The full `MOD`/`AND`/`OR` tower (value): `rep ≡ val (mod p^{2^k})` (PROVED)

The value side of the full 4-node tower (`ACC0FullTowerDegree` gave the degree side).  A value-level
`MOD`/`AND`/`OR` tower has its Toda/product/De-Morgan representation `vrep` congruent to its Boolean value
`vval` modulo `p^{2^k}` at arbitrary depth:

  `full_tower` — for every `FMTower t`: `p^{2^k} ∣ (vrep t − vval t)`.

`MOD` flows via Toda (`ACC0TodaModGate`), `AND` via the product congruence (`ACC0OrNode.dvd_prod_sub_gen`),
`OR` via the De Morgan congruence (`ACC0OrNode.or_node_dvd`).  With `ACC0FullTowerDegree` (degree
`≤ K^depth`) the full `MOD`/`AND`/`OR` tower is now bounded in **both** value and degree.

## What is proved (clean axioms, no `sorry`)

* `FMTower`, `vval`, `vrep` — the value-level full tower, Boolean value, representation.
* `dvd_sum_sub_gen` — generic list-sum divisibility transfer.
* `full_tower` / `full_tower_list` — `p^{2^k} ∣ (vrep t − vval t)` (mutual recursion).

## Honest scope

Value side of the full `MOD`/`AND`/`OR` tower.  With `ACC0FullTowerDegree` both value and degree of the
full gate set are bounded.  The exact-quasipoly `2^k` choice against the global count and the `SYM∘AND`
cash-out remain the Beigel–Tarui wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullTowerValue

open PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate (todaMod_amplifies)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate (todaAmpIter)
open PallLean.Paper93.DeepMath.PathB.ACC0OrNode (dvd_prod_sub_gen or_node_dvd)

/-- A value-level full `MOD`/`AND`/`OR` tower. -/
inductive FMTower where
  | leaf : ℤ → FMTower
  | modN : List FMTower → FMTower
  | andN : List FMTower → FMTower
  | orN : List FMTower → FMTower

/-- The Boolean value. -/
def vval (p : ℕ) : FMTower → ℤ
  | .leaf y => if (p : ℤ) ∣ y then 1 else 0
  | .modN ts => if (p : ℤ) ∣ ((ts.map (vval p)).sum) then 1 else 0
  | .andN ts => (ts.map (vval p)).prod
  | .orN ts => 1 - (ts.map (fun t => 1 - vval p t)).prod

/-- The representation: `MOD` via Toda, `AND` via product, `OR` via De Morgan. -/
def vrep (p k : ℕ) : FMTower → ℤ
  | .leaf y => todaAmpIter k (1 - y ^ (p - 1))
  | .modN ts => todaAmpIter k (1 - ((ts.map (vrep p k)).sum) ^ (p - 1))
  | .andN ts => (ts.map (vrep p k)).prod
  | .orN ts => 1 - (ts.map (fun t => 1 - vrep p k t)).prod

/-- **Generic list-sum divisibility transfer (proved).** -/
theorem dvd_sum_sub_gen {α : Type*} {M : ℤ} (f g : α → ℤ) :
    (l : List α) → (∀ a ∈ l, M ∣ (f a - g a)) → M ∣ ((l.map f).sum - (l.map g).sum)
  | [], _ => by simp
  | a :: t, h => by
      simp only [List.map_cons, List.sum_cons]
      have h1 : M ∣ (f a - g a) := h a (by simp)
      have h2 : M ∣ ((t.map f).sum - (t.map g).sum) :=
        dvd_sum_sub_gen f g t (fun x hx => h x (by simp [hx]))
      have he : (f a + (t.map f).sum) - (g a + (t.map g).sum)
          = (f a - g a) + ((t.map f).sum - (t.map g).sum) := by ring
      rw [he]; exact dvd_add h1 h2

mutual

/-- **Full-tower value congruence (proved): `p^{2^k} ∣ (vrep t − vval t)`.** -/
theorem full_tower (p k : ℕ) [Fact p.Prime] :
    (t : FMTower) → (p : ℤ) ^ (2 ^ k) ∣ (vrep p k t - vval p t)
  | .leaf y => by rw [vrep, vval]; exact todaMod_amplifies p y k
  | .andN ts => by
      have hchild : ∀ t ∈ ts, (p : ℤ) ^ (2 ^ k) ∣ (vrep p k t - vval p t) :=
        fun t ht => full_tower_list p k ts t ht
      rw [vrep, vval]
      exact dvd_prod_sub_gen (vrep p k) (vval p) ts hchild
  | .orN ts => by
      have hchild : ∀ t ∈ ts, (p : ℤ) ^ (2 ^ k) ∣ (vrep p k t - vval p t) :=
        fun t ht => full_tower_list p k ts t ht
      rw [vrep, vval]
      exact or_node_dvd (vrep p k) (vval p) ts hchild
  | .modN ts => by
      have hchild : ∀ t ∈ ts, (p : ℤ) ∣ (vrep p k t - vval p t) := fun t ht =>
        dvd_trans (dvd_pow_self (p : ℤ) (by positivity : (2 : ℕ) ^ k ≠ 0))
          (full_tower_list p k ts t ht)
      have hY : (p : ℤ) ∣ ((ts.map (vrep p k)).sum - (ts.map (vval p)).sum) :=
        dvd_sum_sub_gen (vrep p k) (vval p) ts hchild
      have hiff : ((p : ℤ) ∣ (ts.map (vrep p k)).sum) ↔ ((p : ℤ) ∣ (ts.map (vval p)).sum) := by
        constructor
        · intro h
          have h2 := dvd_sub h hY
          rwa [show (ts.map (vrep p k)).sum - ((ts.map (vrep p k)).sum - (ts.map (vval p)).sum)
            = (ts.map (vval p)).sum from by ring] at h2
        · intro h
          have h2 := dvd_add h hY
          rwa [show (ts.map (vval p)).sum + ((ts.map (vrep p k)).sum - (ts.map (vval p)).sum)
            = (ts.map (vrep p k)).sum from by ring] at h2
      have htoda := todaMod_amplifies p ((ts.map (vrep p k)).sum) k
      have heq : (if (p : ℤ) ∣ (ts.map (vval p)).sum then (1 : ℤ) else 0)
          = (if (p : ℤ) ∣ (ts.map (vrep p k)).sum then (1 : ℤ) else 0) := by
        by_cases h : (p : ℤ) ∣ (ts.map (vrep p k)).sum
        · rw [if_pos (hiff.mp h), if_pos h]
        · rw [if_neg (fun hv => h (hiff.mpr hv)), if_neg h]
      rw [vrep, vval, heq]
      exact htoda

/-- List companion. -/
theorem full_tower_list (p k : ℕ) [Fact p.Prime] :
    (ts : List FMTower) → ∀ t ∈ ts, (p : ℤ) ^ (2 ^ k) ∣ (vrep p k t - vval p t)
  | [] => fun t ht => absurd ht (by simp)
  | a :: ts => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact full_tower p k t
      · exact full_tower_list p k ts t hmem

end

/-!
**Full-tower value congruence proved.**  `p^{2^k} ∣ (vrep t − vval t)` for every `MOD`/`AND`/`OR` tower:
`MOD` via Toda, `AND` via product, `OR` via De Morgan — all congruent to the Boolean output mod `p^{2^k}`.
With `ACC0FullTowerDegree` the full gate set is bounded in both value and degree.  The exact-quasipoly
`2^k` choice and `SYM∘AND` cash-out remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FullTowerValue

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullTowerValue.full_tower
