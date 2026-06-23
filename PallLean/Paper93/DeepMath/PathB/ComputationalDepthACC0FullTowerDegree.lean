import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaTowerDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MixedTowerDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OrNode

/-!
# The full `MOD`/`AND`/`OR` tower (degree): `K^depth`, `K = max(w, 3^k(p−1))` (PROVED)

The complete mixed-tower degree bound, now with all three gate types.  `ACC0MixedTowerDegree` did
`MOD`+`AND`; this adds `OR` (De Morgan, via `ACC0OrNode.or_node_deg`), so a constant-depth ACC⁰[p] circuit
with `MOD` (Toda, *any* modulus), bounded-fan-in `AND`, **and** bounded-fan-in `OR` gates has total degree
`≤ (max w (3^k(p−1)))^depth`:

  `frep_totalDegree_le` — `FBounded w t ⇒ (frep p k t).totalDegree ≤ K^(fdepth t)`, `K = max(w, 3^k(p−1))`.

Every gate multiplies degree by `≤ K` (`MOD` by `3^k(p−1)`, `AND`/`OR` by fan-in `≤ w`), giving `K^depth`
— polylog for `w, 3^k(p−1) = polylog`, constant depth.  This is the realistic ACC⁰[p] degree bound for the
full gate set, via the Toda integer route.

## What is proved (clean axioms, no `sorry`)

* `FTower`, `frep`, `fdepth`, `FBounded` — the full `MOD`/`AND`/`OR` tower.
* `frep_totalDegree_le` / `_list` — the `K^depth` degree bound (mutual recursion).

## Honest scope

Degree side of the full `MOD`/`AND`/`OR` tower (`MOD` Toda + bounded `AND`/`OR`).  Unbounded `AND`/`OR` is
the exact-degree no-go (`ACC0ExactDegreeNoGo`) — needs RS.  The value side, the exact-quasipoly `2^k`
choice, and the `SYM∘AND` cash-out remain the Beigel–Tarui wall.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullTowerDegree

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3 (le_foldl_max)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaDegree (todaAmpIterP todaAmpIterP_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaTowerDegree (fermat_poly_deg list_sum_deg_le)
open PallLean.Paper93.DeepMath.PathB.ACC0MixedTowerDegree (map_deg_sum_le)
open PallLean.Paper93.DeepMath.PathB.ACC0OrNode (or_node_deg)

variable {σ : Type*}

/-- A full `MOD`/`AND`/`OR` tower. -/
inductive FTower (σ : Type*) where
  | leaf : MvPolynomial σ ℤ → FTower σ
  | modN : List (FTower σ) → FTower σ
  | andN : List (FTower σ) → FTower σ
  | orN : List (FTower σ) → FTower σ

/-- The representation: `MOD` via Toda, `AND` via product, `OR` via De Morgan. -/
noncomputable def frep (p k : ℕ) : FTower σ → MvPolynomial σ ℤ
  | .leaf q => q
  | .modN ts => todaAmpIterP k (1 - ((ts.map (frep p k)).sum) ^ (p - 1))
  | .andN ts => (ts.map (frep p k)).prod
  | .orN ts => 1 - ((ts.map (frep p k)).map (fun q => 1 - q)).prod

/-- Tower depth. -/
def fdepth : FTower σ → ℕ
  | .leaf _ => 0
  | .modN ts => ts.foldl (fun m t => max m (fdepth t)) 0 + 1
  | .andN ts => ts.foldl (fun m t => max m (fdepth t)) 0 + 1
  | .orN ts => ts.foldl (fun m t => max m (fdepth t)) 0 + 1

/-- Boundedness: leaves degree `≤ 1`, `AND`/`OR` fan-in `≤ w`. -/
def FBounded (w : ℕ) : FTower σ → Prop
  | .leaf q => q.totalDegree ≤ 1
  | .modN ts => ∀ t ∈ ts, FBounded w t
  | .andN ts => ts.length ≤ w ∧ ∀ t ∈ ts, FBounded w t
  | .orN ts => ts.length ≤ w ∧ ∀ t ∈ ts, FBounded w t

mutual

/-- **Full-tower degree bound (proved): `deg(frep t) ≤ K^(fdepth t)`, `K = max(w, 3^k(p−1))`.** -/
theorem frep_totalDegree_le (p k w : ℕ) (hpos : 1 ≤ max w (3 ^ k * (p - 1))) :
    (t : FTower σ) → FBounded w t →
      (frep p k t).totalDegree ≤ (max w (3 ^ k * (p - 1))) ^ fdepth t
  | .leaf q, h => by
      simp only [FBounded] at h; rw [frep, fdepth, pow_zero]; exact h
  | .modN ts, h => by
      simp only [FBounded] at h
      set K := max w (3 ^ k * (p - 1)) with hK
      set fm := ts.foldl (fun m t => max m (fdepth t)) 0 with hfm
      have hsum : ((ts.map (frep p k)).sum).totalDegree ≤ K ^ fm :=
        list_sum_deg_le _ _ (by
          intro r hr; simp only [List.mem_map] at hr; obtain ⟨t, ht, rfl⟩ := hr
          exact le_trans (frep_totalDegree_le_list p k w hpos ts h t ht)
            (Nat.pow_le_pow_right hpos (le_foldl_max (fun t => fdepth t) ts 0 ht)))
      have hkK : 3 ^ k * (p - 1) ≤ K := le_max_right _ _
      have hstep : (1 - ((ts.map (frep p k)).sum) ^ (p - 1)).totalDegree ≤ (p - 1) * K ^ fm :=
        le_trans (fermat_poly_deg p _) (by gcongr)
      rw [frep, fdepth]
      refine le_trans (todaAmpIterP_totalDegree_le k _) ?_
      calc 3 ^ k * (1 - ((ts.map (frep p k)).sum) ^ (p - 1)).totalDegree
          ≤ 3 ^ k * ((p - 1) * K ^ fm) := by gcongr
        _ = (3 ^ k * (p - 1)) * K ^ fm := by ring
        _ ≤ K * K ^ fm := by gcongr
        _ = K ^ (fm + 1) := by rw [pow_succ]; ring
  | .andN ts, h => by
      simp only [FBounded] at h
      obtain ⟨hlen, hch⟩ := h
      set K := max w (3 ^ k * (p - 1)) with hK
      set fm := ts.foldl (fun m t => max m (fdepth t)) 0 with hfm
      have hbd : ∀ r ∈ (ts.map (frep p k)), r.totalDegree ≤ K ^ fm := by
        intro r hr; simp only [List.mem_map] at hr; obtain ⟨t, ht, rfl⟩ := hr
        exact le_trans (frep_totalDegree_le_list p k w hpos ts hch t ht)
          (Nat.pow_le_pow_right hpos (le_foldl_max (fun t => fdepth t) ts 0 ht))
      have hwK : w ≤ K := le_max_left _ _
      rw [frep, fdepth]
      refine le_trans (totalDegree_list_prod _) ?_
      calc ((ts.map (frep p k)).map totalDegree).sum
          ≤ (ts.map (frep p k)).length * K ^ fm := map_deg_sum_le _ _ hbd
        _ = ts.length * K ^ fm := by rw [List.length_map]
        _ ≤ w * K ^ fm := by gcongr
        _ ≤ K * K ^ fm := by gcongr
        _ = K ^ (fm + 1) := by rw [pow_succ]; ring
  | .orN ts, h => by
      simp only [FBounded] at h
      obtain ⟨hlen, hch⟩ := h
      set K := max w (3 ^ k * (p - 1)) with hK
      set fm := ts.foldl (fun m t => max m (fdepth t)) 0 with hfm
      have hbd : ∀ r ∈ (ts.map (frep p k)), r.totalDegree ≤ K ^ fm := by
        intro r hr; simp only [List.mem_map] at hr; obtain ⟨t, ht, rfl⟩ := hr
        exact le_trans (frep_totalDegree_le_list p k w hpos ts hch t ht)
          (Nat.pow_le_pow_right hpos (le_foldl_max (fun t => fdepth t) ts 0 ht))
      have hwK : w ≤ K := le_max_left _ _
      rw [frep, fdepth]
      refine le_trans (or_node_deg (ts.map (frep p k))) ?_
      calc ((ts.map (frep p k)).map totalDegree).sum
          ≤ (ts.map (frep p k)).length * K ^ fm := map_deg_sum_le _ _ hbd
        _ = ts.length * K ^ fm := by rw [List.length_map]
        _ ≤ w * K ^ fm := by gcongr
        _ ≤ K * K ^ fm := by gcongr
        _ = K ^ (fm + 1) := by rw [pow_succ]; ring

/-- List companion. -/
theorem frep_totalDegree_le_list (p k w : ℕ) (hpos : 1 ≤ max w (3 ^ k * (p - 1))) :
    (ts : List (FTower σ)) → (∀ t ∈ ts, FBounded w t) →
      ∀ t ∈ ts, (frep p k t).totalDegree ≤ (max w (3 ^ k * (p - 1))) ^ fdepth t
  | [], _ => fun t ht => absurd ht (by simp)
  | a :: ts, h => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact frep_totalDegree_le p k w hpos t (h t (by simp))
      · exact frep_totalDegree_le_list p k w hpos ts (fun t' ht' => h t' (by simp [ht'])) t hmem

end

/-!
**Full-tower degree bound proved.**  `deg(frep t) ≤ (max w (3^k(p−1)))^(fdepth t)` for the full
`MOD`/`AND`/`OR` tower (`MOD` Toda any modulus, bounded `AND`/`OR`) — polylog for `w, 3^k(p−1) = polylog`,
constant depth.  The value side, the exact-quasipoly `2^k` choice, and the `SYM∘AND` cash-out remain.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FullTowerDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullTowerDegree.frep_totalDegree_le
