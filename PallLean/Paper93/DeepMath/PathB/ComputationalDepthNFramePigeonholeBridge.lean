import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameHittingRank
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The quantitative pigeonhole bridge

Discharging the one remaining hypothesis of `pathMatrix_sparse_lowrank_split` — the hitting-set
factorization of the length-`p` walk matrix — with a concrete `r`, via a genuine pigeonhole.

The clean, fully-provable instance is the **level** pigeonhole at the top length `p = maxLvl`.  A walk
of length `maxLvl` raises the level by `maxLvl` over `maxLvl` edges, each by `≥ 1`, so **every edge
raises it by exactly 1** — the longest walks are synchronous and route through *every* level.  Hence
`W^maxLvl` factors through the vertices at any single level `ℓ` (`Wpow_maxLvl_factor`), giving
`rank (W^maxLvl) ≤ (#vertices at level ℓ)` (`Wpow_maxLvl_rank_le`).  Pigeonhole over the `maxLvl+1`
levels (`exists_thin_level`): some level has `≤ N/(maxLvl+1)` vertices.  Assembled in
`valiant_pigeonhole_split`: the sparse + low-rank split with `rank (longPart) ≤ r`, `r·(maxLvl+1) ≤ N`.

So for a depth-`d` circuit the longest-walk part has rank `≤ N/(d+1)` — a concrete, unconditional
rigidity-flavored bound.

## Honest scope

This discharges the hypothesis via the **level** structure, yielding the `N/(depth+1)` bound on the
longest-walk part.  It does **not** use the label classes, and it is weaker than Valiant's `s/log d`:
that sharper bound needs the label-based hitting set (targets of high-label edges), whose clean
formalization is blocked by the walk-*position* issue — a length-`p` walk's high-label edge can sit
anywhere, so `W^p` (fixed length) does not factor through those vertices at a fixed position the way the
synchronous longest walks factor through a fixed level.  Bridging that (a first-passage convolution on
the full `longPart`, not on `W^p`) is the remaining step.  Rigidity itself stays the open,
P≠NP-strength input.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

namespace LinCircuit

variable {F : Type*} [Field F] {N : ℕ} (G : LinCircuit F N)

/-- **The longest walks factor through any single level.**  `W^maxLvl = W^{maxLvl-ℓ}·D_ℓ·W^ℓ`, where
`D_ℓ` is the diagonal projector onto vertices at level `ℓ`: a length-`maxLvl` walk is synchronous, so at
"time `ℓ`" it sits at a level-`ℓ` vertex. -/
theorem Wpow_maxLvl_factor (ℓ : ℕ) (hℓ : ℓ ≤ G.maxLvl) :
    G.W ^ G.maxLvl
      = G.W ^ (G.maxLvl - ℓ) * Matrix.diagonal (fun v => if G.lvl v = ℓ then (1 : F) else 0)
        * G.W ^ ℓ := by
  have hpow : G.W ^ G.maxLvl = G.W ^ (G.maxLvl - ℓ) * G.W ^ ℓ := by
    rw [← pow_add, Nat.sub_add_cancel hℓ]
  rw [Matrix.mul_assoc]
  ext i j
  rw [hpow, Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.diagonal_mul]
  by_cases hk : G.lvl k = ℓ
  · rw [if_pos hk, one_mul]
  · rw [if_neg hk, zero_mul, mul_zero]
    by_contra hne
    have hA : (G.W ^ (G.maxLvl - ℓ)) i k ≠ 0 := left_ne_zero_of_mul hne
    have hB : (G.W ^ ℓ) k j ≠ 0 := right_ne_zero_of_mul hne
    have e1 := G.walk_level_bound i (G.maxLvl - ℓ) k hA
    have e2 := G.walk_level_bound k ℓ j hB
    have e3 := G.lvl_le_maxLvl i
    exact hk (by omega)

/-- **The longest-walk matrix has rank at most any level's width.**  `rank (W^maxLvl) ≤ (#vertices at
level ℓ)`. -/
theorem Wpow_maxLvl_rank_le (ℓ : ℕ) (hℓ : ℓ ≤ G.maxLvl) :
    (G.W ^ G.maxLvl).rank ≤ (Finset.univ.filter (fun v => G.lvl v = ℓ)).card := by
  classical
  rw [G.Wpow_maxLvl_factor ℓ hℓ]
  refine (rank_mul_mul_le_mid _ _ _).trans ?_
  rw [Matrix.rank_diagonal, Fintype.card_subtype]
  apply le_of_eq
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro v _
  by_cases h : G.lvl v = ℓ <;> simp [h]

/-- The level widths sum to `N`: every vertex sits at exactly one level in `[0, maxLvl]`. -/
theorem sum_levelCard :
    ∑ ℓ ∈ Finset.range (G.maxLvl + 1), (Finset.univ.filter (fun v => G.lvl v = ℓ)).card = N := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin N))) (t := Finset.range (G.maxLvl + 1)) (f := G.lvl)
    (fun v _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (G.lvl_le_maxLvl v)))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

/-- **Pigeonhole.**  Some level has at most `N/(maxLvl+1)` vertices: `#·(maxLvl+1) ≤ N`. -/
theorem exists_thin_level :
    ∃ ℓ ∈ Finset.range (G.maxLvl + 1),
      (Finset.univ.filter (fun v => G.lvl v = ℓ)).card * (G.maxLvl + 1) ≤ N := by
  by_contra hcon
  push_neg at hcon
  have h1 : ∑ _ℓ ∈ Finset.range (G.maxLvl + 1), (N + 1)
      ≤ ∑ ℓ ∈ Finset.range (G.maxLvl + 1),
          (Finset.univ.filter (fun v => G.lvl v = ℓ)).card * (G.maxLvl + 1) :=
    Finset.sum_le_sum (fun ℓ hℓ => hcon ℓ hℓ)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.sum_mul, G.sum_levelCard] at h1
  have e : (G.maxLvl + 1) * (N + 1) = N * (G.maxLvl + 1) + (G.maxLvl + 1) := by ring
  omega

/-- **The quantitative pigeonhole bridge.**  There is a concrete `r ≤ N/(maxLvl+1)` and a level `ℓ`
such that the path matrix splits as short + long with the long (longest-walk) part of rank `≤ r`.  This
discharges the hitting-set hypothesis of `pathMatrix_sparse_lowrank_split` at `p = maxLvl`, via the
level pigeonhole. -/
theorem valiant_pigeonhole_split :
    ∃ r : ℕ, r * (G.maxLvl + 1) ≤ N ∧
      G.pathMatrix = G.shortPart G.maxLvl + G.longPart G.maxLvl ∧
      (G.longPart G.maxLvl).rank ≤ r := by
  obtain ⟨ℓ, hℓrange, hcard⟩ := G.exists_thin_level
  have hℓ : ℓ ≤ G.maxLvl := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓrange)
  refine ⟨(Finset.univ.filter (fun v => G.lvl v = ℓ)).card, hcard, ?_, ?_⟩
  · exact G.pathMatrix_split G.maxLvl (Nat.le_succ _)
  · exact (G.longPart_rank_le G.maxLvl).trans (G.Wpow_maxLvl_rank_le ℓ hℓ)

end LinCircuit

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
