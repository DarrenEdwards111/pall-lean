import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaModGate

/-!
# The depth-`d` `MOD_p` tower: Toda represents it across arbitrary depth (PROVED)

The across-depth assembly's capstone for all-`MOD` towers.  `ACC0TodaDepth2` stacked two `MOD_p` layers;
this generalises to **arbitrary depth** via a recursive `MOD`-tower and a uniform `k`.

A `ModTower` is a leaf count or a `MOD_p` node over a list of subtowers.  Its Boolean value `val` is the
nested `MOD_p` of the accepting-child counts; its Toda representation `rep` applies `A^{[k]}` to the
Fermat indicator at each node.  With a **uniform `k`** (the same `k` at every node):

  `toda_tower` — for every `ModTower t`: `p^{2^k} ∣ (rep t − val t)` — the Toda representation equals the
  tower's Boolean output modulo `p^{2^k}`, at **any depth**.

The induction: at a node, each child's `mod p^{2^k}` representation weakens to `mod p` (`p ∣ p^{2^k}`),
the accepting count's `MOD_p` decision transfers from reps to values, and `A^{[k]}` re-amplifies — so the
amplification flows through unbounded depth.

## What is proved (clean axioms, no `sorry`)

* `ModTower`, `val`, `rep` — the recursive `MOD`-tower, its Boolean value and Toda representation.
* `dvd_list_sum_sub` — list-sum divisibility transfer.
* `toda_tower` / `toda_tower_list` — `p^{2^k} ∣ (rep t − val t)` for every tower (mutual recursion).

## Honest scope

This is the all-`MOD` tower at arbitrary depth, value-level (uniform `k`, common modulus `p^{2^k}`).  The
full Beigel–Tarui integer construction still needs: the polynomial/degree form across the tower
(`(3^k(p−1))^depth`), the `AND`/`OR` layers, and choosing `2^k` against the global count to make the
representation *exact* and quasipoly.  That remains the wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaTower

open PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate (todaMod_amplifies)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate (todaAmpIter)

/-- A `MOD_p` tower: a leaf count, or a `MOD_p` node over a list of subtowers. -/
inductive ModTower where
  | leaf : ℤ → ModTower
  | node : List ModTower → ModTower

/-- The Boolean value of a tower: nested `MOD_p` of accepting-child counts. -/
def val (p : ℕ) : ModTower → ℤ
  | .leaf y => if (p : ℤ) ∣ y then 1 else 0
  | .node ts => if (p : ℤ) ∣ ((ts.map (val p)).sum) then 1 else 0

/-- The Toda representation of a tower (uniform `k`): `A^{[k]}` of the Fermat indicator at each node. -/
def rep (p k : ℕ) : ModTower → ℤ
  | .leaf y => todaAmpIter k (1 - y ^ (p - 1))
  | .node ts => todaAmpIter k (1 - ((ts.map (rep p k)).sum) ^ (p - 1))

/-- **List-sum divisibility transfer (proved).** -/
theorem dvd_list_sum_sub {M : ℤ} (f g : ModTower → ℤ) :
    (l : List ModTower) → (∀ t ∈ l, M ∣ (f t - g t)) →
      M ∣ ((l.map f).sum - (l.map g).sum)
  | [], _ => by simp
  | a :: t, h => by
      simp only [List.map_cons, List.sum_cons]
      have h1 : M ∣ (f a - g a) := h a (by simp)
      have h2 : M ∣ ((t.map f).sum - (t.map g).sum) :=
        dvd_list_sum_sub f g t (fun x hx => h x (by simp [hx]))
      have he : (f a + (t.map f).sum) - (g a + (t.map g).sum)
          = (f a - g a) + ((t.map f).sum - (t.map g).sum) := by ring
      rw [he]; exact dvd_add h1 h2

mutual

/-- **Depth-`d` `MOD_p` tower Toda representation (proved): `p^{2^k} ∣ (rep t − val t)`.** -/
theorem toda_tower (p k : ℕ) [Fact p.Prime] :
    (t : ModTower) → (p : ℤ) ^ (2 ^ k) ∣ (rep p k t - val p t)
  | .leaf y => by
      rw [rep, val]; exact todaMod_amplifies p y k
  | .node ts => by
      have hchild : ∀ t ∈ ts, (p : ℤ) ∣ (rep p k t - val p t) := fun t ht =>
        dvd_trans (dvd_pow_self (p : ℤ) (by positivity : (2 : ℕ) ^ k ≠ 0))
          (toda_tower_list p k ts t ht)
      have hY : (p : ℤ) ∣ ((ts.map (rep p k)).sum - (ts.map (val p)).sum) :=
        dvd_list_sum_sub (rep p k) (val p) ts hchild
      have hiff : ((p : ℤ) ∣ (ts.map (rep p k)).sum) ↔ ((p : ℤ) ∣ (ts.map (val p)).sum) := by
        constructor
        · intro h
          have h2 := dvd_sub h hY
          rwa [show (ts.map (rep p k)).sum - ((ts.map (rep p k)).sum - (ts.map (val p)).sum)
            = (ts.map (val p)).sum from by ring] at h2
        · intro h
          have h2 := dvd_add h hY
          rwa [show (ts.map (val p)).sum + ((ts.map (rep p k)).sum - (ts.map (val p)).sum)
            = (ts.map (rep p k)).sum from by ring] at h2
      have htoda := todaMod_amplifies p ((ts.map (rep p k)).sum) k
      have heq : (if (p : ℤ) ∣ (ts.map (val p)).sum then (1 : ℤ) else 0)
          = (if (p : ℤ) ∣ (ts.map (rep p k)).sum then (1 : ℤ) else 0) := by
        by_cases h : (p : ℤ) ∣ (ts.map (rep p k)).sum
        · rw [if_pos (hiff.mp h), if_pos h]
        · rw [if_neg (fun hv => h (hiff.mpr hv)), if_neg h]
      rw [rep, val, heq]
      exact htoda

/-- List companion of `toda_tower`. -/
theorem toda_tower_list (p k : ℕ) [Fact p.Prime] :
    (ts : List ModTower) → ∀ t ∈ ts, (p : ℤ) ^ (2 ^ k) ∣ (rep p k t - val p t)
  | [] => fun t ht => absurd ht (by simp)
  | a :: ts => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact toda_tower p k t
      · exact toda_tower_list p k ts t hmem

end

/-!
**Depth-`d` `MOD_p` tower proved.**  `p^{2^k} ∣ (rep t − val t)` for every tower at any depth: the Toda
amplification flows through unbounded depth with a uniform `k` (inner `mod p^{2^k}` weakens to `mod p`,
the count transfers, `A^{[k]}` re-amplifies).  The polynomial/degree form, the `AND`/`OR` layers, and the
exact-quasipoly choice of `2^k` against the global count remain the Beigel–Tarui integer wall.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaTower

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaTower.toda_tower
