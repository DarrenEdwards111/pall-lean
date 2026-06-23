import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaTowerDegree

/-!
# The mixed `MOD`/`AND` tower: degree `K^depth`, `K = max(w, 3^k(p−1))` (PROVED)

The realistic ACC⁰[p] degree bound combining the two routes.  `ACC0TodaTowerDegree` bounded the pure-`MOD`
tower; `ACC0ExactBoundedAndOr` handled `AND`/`OR` but with `MOD` only at the Fermat degree `q−1` (modulus
`q ≤ w+1`).  This builds the **mixed** tower — `MOD` gates via **Toda** (degree `3^k(p−1)`, *any* modulus,
exact mod `p^{2^k}`) **and** bounded-fan-in `AND` gates (degree `≤` fan-in) — bounding its total degree by
`K^depth` with `K = max(w, 3^k(p−1))`:

  `mrep_totalDegree_le` — `MBounded w t ⇒ (mrep p k t).totalDegree ≤ K^(mdepth t)`.

So a constant-depth circuit with **unbounded-fan-in (large-modulus) `MOD`** gates and **bounded-fan-in
`AND`** gates has total degree `polylog` — strictly more than `ExactBoundedAndOr` (which caps the
modulus).  Each `MOD` node multiplies degree by `3^k(p−1)`, each `AND` node by its fan-in `≤ w`; both
`≤ K`, giving `K^depth`.  (`OR` is the De Morgan analogue `1 − ∏(1 − ·)`, same degree law as `AND`.)

## What is proved (clean axioms, no `sorry`)

* `MTower`, `mrep`, `mdepth`, `MBounded` — the mixed tower, its representation, depth, boundedness.
* `mrep_totalDegree_le` / `_list` — the `K^depth` degree bound (mutual recursion).

## Honest scope

Degree side of the mixed (`MOD`-Toda + bounded-`AND`) tower.  Unbounded `AND`/`OR` is the exact-degree
no-go (`ACC0ExactDegreeNoGo`) — needs RS approximation.  `OR`, the value side, the exactness `2^k` choice,
and the `SYM∘AND` assembly remain the Beigel–Tarui wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MixedTowerDegree

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3 (le_foldl_max)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaDegree (todaAmpIterP todaAmpIterP_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaTowerDegree (fermat_poly_deg list_sum_deg_le)

variable {σ : Type*}

/-- A mixed `MOD`/`AND` tower: a leaf (input/affine), a `MOD_p` node, or an `AND` node. -/
inductive MTower (σ : Type*) where
  | leaf : MvPolynomial σ ℤ → MTower σ
  | modN : List (MTower σ) → MTower σ
  | andN : List (MTower σ) → MTower σ

/-- The polynomial representation: `MOD` via Toda, `AND` via product. -/
noncomputable def mrep (p k : ℕ) : MTower σ → MvPolynomial σ ℤ
  | .leaf q => q
  | .modN ts => todaAmpIterP k (1 - ((ts.map (mrep p k)).sum) ^ (p - 1))
  | .andN ts => (ts.map (mrep p k)).prod

/-- Tower depth. -/
def mdepth : MTower σ → ℕ
  | .leaf _ => 0
  | .modN ts => ts.foldl (fun m t => max m (mdepth t)) 0 + 1
  | .andN ts => ts.foldl (fun m t => max m (mdepth t)) 0 + 1

/-- Boundedness: leaves degree `≤ 1`, `AND` fan-in `≤ w`. -/
def MBounded (w : ℕ) : MTower σ → Prop
  | .leaf q => q.totalDegree ≤ 1
  | .modN ts => ∀ t ∈ ts, MBounded w t
  | .andN ts => ts.length ≤ w ∧ ∀ t ∈ ts, MBounded w t

/-- `(L.map totalDegree).sum ≤ L.length * D` when every element has degree `≤ D`. -/
theorem map_deg_sum_le (L : List (MvPolynomial σ ℤ)) (D : ℕ)
    (h : ∀ q ∈ L, q.totalDegree ≤ D) : (L.map totalDegree).sum ≤ L.length * D := by
  have := List.sum_le_card_nsmul (L.map totalDegree) D (by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨q, hq, rfl⟩ := hx; exact h q hq)
  simpa [List.length_map, smul_eq_mul] using this

mutual

/-- **Mixed-tower degree bound (proved): `deg(mrep t) ≤ K^(mdepth t)`, `K = max(w, 3^k(p−1))`.** -/
theorem mrep_totalDegree_le (p k w : ℕ) (hpos : 1 ≤ max w (3 ^ k * (p - 1))) :
    (t : MTower σ) → MBounded w t →
      (mrep p k t).totalDegree ≤ (max w (3 ^ k * (p - 1))) ^ mdepth t
  | .leaf q, h => by
      simp only [MBounded] at h
      rw [mrep, mdepth, pow_zero]; exact h
  | .modN ts, h => by
      simp only [MBounded] at h
      set K := max w (3 ^ k * (p - 1)) with hK
      set fm := ts.foldl (fun m t => max m (mdepth t)) 0 with hfm
      have hsum : ((ts.map (mrep p k)).sum).totalDegree ≤ K ^ fm :=
        list_sum_deg_le _ _ (by
          intro r hr; simp only [List.mem_map] at hr; obtain ⟨t, ht, rfl⟩ := hr
          exact le_trans (mrep_totalDegree_le_list p k w hpos ts h t ht)
            (Nat.pow_le_pow_right hpos (le_foldl_max (fun t => mdepth t) ts 0 ht)))
      have hkK : 3 ^ k * (p - 1) ≤ K := le_max_right _ _
      have hstep : (1 - ((ts.map (mrep p k)).sum) ^ (p - 1)).totalDegree ≤ (p - 1) * K ^ fm :=
        le_trans (fermat_poly_deg p _) (by gcongr)
      rw [mrep, mdepth]
      refine le_trans (todaAmpIterP_totalDegree_le k _) ?_
      calc 3 ^ k * (1 - ((ts.map (mrep p k)).sum) ^ (p - 1)).totalDegree
          ≤ 3 ^ k * ((p - 1) * K ^ fm) := by gcongr
        _ = (3 ^ k * (p - 1)) * K ^ fm := by ring
        _ ≤ K * K ^ fm := by gcongr
        _ = K ^ (fm + 1) := by rw [pow_succ]; ring
  | .andN ts, h => by
      simp only [MBounded] at h
      obtain ⟨hlen, hch⟩ := h
      set K := max w (3 ^ k * (p - 1)) with hK
      set fm := ts.foldl (fun m t => max m (mdepth t)) 0 with hfm
      have hbd : ∀ r ∈ (ts.map (mrep p k)), r.totalDegree ≤ K ^ fm := by
        intro r hr; simp only [List.mem_map] at hr; obtain ⟨t, ht, rfl⟩ := hr
        exact le_trans (mrep_totalDegree_le_list p k w hpos ts hch t ht)
          (Nat.pow_le_pow_right hpos (le_foldl_max (fun t => mdepth t) ts 0 ht))
      have hwK : w ≤ K := le_max_left _ _
      rw [mrep, mdepth]
      refine le_trans (totalDegree_list_prod _) ?_
      calc ((ts.map (mrep p k)).map totalDegree).sum
          ≤ (ts.map (mrep p k)).length * K ^ fm := map_deg_sum_le _ _ hbd
        _ = ts.length * K ^ fm := by rw [List.length_map]
        _ ≤ w * K ^ fm := by gcongr
        _ ≤ K * K ^ fm := by gcongr
        _ = K ^ (fm + 1) := by rw [pow_succ]; ring

/-- List companion. -/
theorem mrep_totalDegree_le_list (p k w : ℕ) (hpos : 1 ≤ max w (3 ^ k * (p - 1))) :
    (ts : List (MTower σ)) → (∀ t ∈ ts, MBounded w t) →
      ∀ t ∈ ts, (mrep p k t).totalDegree ≤ (max w (3 ^ k * (p - 1))) ^ mdepth t
  | [], _ => fun t ht => absurd ht (by simp)
  | a :: ts, h => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact mrep_totalDegree_le p k w hpos t (h t (by simp))
      · exact mrep_totalDegree_le_list p k w hpos ts (fun t' ht' => h t' (by simp [ht'])) t hmem

end

/-!
**Mixed-tower degree bound proved.**  `deg(mrep t) ≤ (max w (3^k(p−1)))^(mdepth t)` — `MOD` via Toda (any
modulus, degree `3^k(p−1)`), bounded `AND` (degree `≤ w`).  Polylog for `w, 3^k(p−1) = polylog`, constant
depth — strictly more than `ExactBoundedAndOr` (large-modulus `MOD` allowed).  `OR`, the value side, the
exactness `2^k` choice, and the `SYM∘AND` assembly remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0MixedTowerDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MixedTowerDegree.mrep_totalDegree_le
