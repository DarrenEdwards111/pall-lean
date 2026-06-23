import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DegreeComposition

/-!
# The depth-`d` `MOD_p` tower's degree: `(3^k(p−1))^depth` (PROVED)

The degree side of the across-depth tower (`ACC0TodaTower` gave the value side).  A polynomial `MOD`-tower
`PModTower` (degree-`≤1` leaves = inputs/affine forms, `MOD_p` nodes) has its Toda representation `prep`
(`A^{[k]}` of the Fermat indicator at each node) bounded in total degree by `(3^k(p−1))^depth`:

  `prep_totalDegree_le` — `LeavesDeg1 t ⇒ (prep p k t).totalDegree ≤ (3^k·(p−1))^(pdepth t)`.

Each node multiplies the degree by `3^k·(p−1)` (Fermat `p−1`, Toda `3^k`), so a depth-`d` tower has
degree `(3^k(p−1))^d` — **polylog** for `k ≈ log log` and constant depth `d`.  Together with the value
side (`toda_tower`: exact mod `p^{2^k}`) this is the integer route's *polylog-degree, exact-mod-`p^{2^k}`*
representation of the ACC⁰[p] `MOD`-skeleton across depth.

## What is proved (clean axioms, no `sorry`)

* `PModTower`, `prep`, `pdepth`, `LeavesDeg1` — the polynomial `MOD`-tower and its degree/leaf data.
* `prep_totalDegree_le` / `prep_totalDegree_le_list` — the `(3^k(p−1))^depth` degree bound (mutual).

## Honest scope

Degree side of the all-`MOD` tower (degree-≤1 leaves).  With `ACC0TodaTower` (value side) the `MOD`-skeleton
is now bounded in *both* degree (`(3^k(p−1))^d`) and modulus (`p^{2^k}`).  The full Beigel–Tarui
construction still needs the `AND`/`OR` layers and the exact-quasipoly choice of `2^k` against the global
count.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaTowerDegree

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3 (le_foldl_max)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaDegree (todaAmpIterP todaAmpIterP_totalDegree_le)

variable {σ : Type*}

/-- A polynomial `MOD_p` tower: a leaf polynomial (a count/affine form), or a `MOD_p` node. -/
inductive PModTower (σ : Type*) where
  | leaf : MvPolynomial σ ℤ → PModTower σ
  | node : List (PModTower σ) → PModTower σ

/-- The Toda representation of a polynomial tower (uniform `k`). -/
noncomputable def prep (p k : ℕ) : PModTower σ → MvPolynomial σ ℤ
  | .leaf q => todaAmpIterP k (1 - q ^ (p - 1))
  | .node ts => todaAmpIterP k (1 - ((ts.map (prep p k)).sum) ^ (p - 1))

/-- Tower depth (max child depth `+ 1`). -/
def pdepth : PModTower σ → ℕ
  | .leaf _ => 1
  | .node ts => ts.foldl (fun m t => max m (pdepth t)) 0 + 1

/-- All leaves are degree `≤ 1` (inputs / affine forms). -/
def LeavesDeg1 : PModTower σ → Prop
  | .leaf q => q.totalDegree ≤ 1
  | .node ts => ∀ t ∈ ts, LeavesDeg1 t

/-- A list sum's total degree is `≤ D` when every summand is `≤ D`. -/
theorem list_sum_deg_le (L : List (MvPolynomial σ ℤ)) (D : ℕ)
    (h : ∀ q ∈ L, q.totalDegree ≤ D) : L.sum.totalDegree ≤ D := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.sum_cons]
    exact le_trans (totalDegree_add _ _)
      (max_le (h a (by simp)) (ih (fun q hq => h q (by simp [hq]))))

/-- `1 − r^{p−1}` has total degree `≤ (p−1)·deg r`. -/
theorem fermat_poly_deg (p : ℕ) (r : MvPolynomial σ ℤ) :
    (1 - r ^ (p - 1) : MvPolynomial σ ℤ).totalDegree ≤ (p - 1) * r.totalDegree := by
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · rw [totalDegree_one]; exact Nat.zero_le _
  · exact totalDegree_pow r (p - 1)

mutual

/-- **The tower degree bound (proved): `deg(prep t) ≤ (3^k(p−1))^(pdepth t)` for degree-≤1 leaves.** -/
theorem prep_totalDegree_le (p k : ℕ) (hk : 1 ≤ 3 ^ k * (p - 1)) :
    (t : PModTower σ) → LeavesDeg1 t →
      (prep p k t).totalDegree ≤ (3 ^ k * (p - 1)) ^ pdepth t
  | .leaf q, h => by
      rw [prep, pdepth, pow_one]
      refine le_trans (todaAmpIterP_totalDegree_le k _) ?_
      refine le_trans (Nat.mul_le_mul_left _ (fermat_poly_deg p q)) ?_
      simp only [LeavesDeg1] at h
      calc 3 ^ k * ((p - 1) * q.totalDegree)
          ≤ 3 ^ k * ((p - 1) * 1) := by
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
        _ = 3 ^ k * (p - 1) := by ring
  | .node ts, h => by
      simp only [LeavesDeg1] at h
      set fm := ts.foldl (fun m t => max m (pdepth t)) 0 with hfm
      have hbound : ∀ r ∈ (ts.map (prep p k)), r.totalDegree ≤ (3 ^ k * (p - 1)) ^ fm := by
        intro r hr
        simp only [List.mem_map] at hr
        obtain ⟨t, ht, rfl⟩ := hr
        exact le_trans (prep_totalDegree_le_list p k hk ts h t ht)
          (Nat.pow_le_pow_right hk (le_foldl_max (fun t => pdepth t) ts 0 ht))
      have hsum : ((ts.map (prep p k)).sum).totalDegree ≤ (3 ^ k * (p - 1)) ^ fm :=
        list_sum_deg_le _ _ hbound
      rw [prep, pdepth]
      refine le_trans (todaAmpIterP_totalDegree_le k _) ?_
      refine le_trans (Nat.mul_le_mul_left _ (fermat_poly_deg p _)) ?_
      calc 3 ^ k * ((p - 1) * ((ts.map (prep p k)).sum).totalDegree)
          ≤ 3 ^ k * ((p - 1) * (3 ^ k * (p - 1)) ^ fm) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsum)
        _ = (3 ^ k * (p - 1)) ^ (fm + 1) := by rw [pow_succ]; ring

/-- List companion of `prep_totalDegree_le`. -/
theorem prep_totalDegree_le_list (p k : ℕ) (hk : 1 ≤ 3 ^ k * (p - 1)) :
    (ts : List (PModTower σ)) → (∀ t ∈ ts, LeavesDeg1 t) →
      ∀ t ∈ ts, (prep p k t).totalDegree ≤ (3 ^ k * (p - 1)) ^ pdepth t
  | [], _ => fun t ht => absurd ht (by simp)
  | a :: ts, h => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact prep_totalDegree_le p k hk t (h t (by simp))
      · exact prep_totalDegree_le_list p k hk ts (fun t' ht' => h t' (by simp [ht'])) t hmem

end

/-!
**Tower degree bound proved.**  `deg(prep t) ≤ (3^k(p−1))^(pdepth t)` for degree-≤1 leaves — each `MOD`
node multiplies degree by `3^k(p−1)`, so depth `d` gives `(3^k(p−1))^d` (polylog for `k ≈ log log`,
constant `d`).  With `ACC0TodaTower` (exact mod `p^{2^k}`) the `MOD`-skeleton is bounded in both degree and
modulus.  The `AND`/`OR` layers and the exact-quasipoly `2^k` choice remain the wall.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaTowerDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaTowerDegree.prep_totalDegree_le
