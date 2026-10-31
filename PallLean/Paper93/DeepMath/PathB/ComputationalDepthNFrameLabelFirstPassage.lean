import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameHittingRank
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The label first-passage split — the sharper (`s/log d`) bridge

The `N/depth` bound (`NFramePigeonholeBridge`) used only levels.  This file uses the covering lemma's
**labels** to get a bound in terms of the *high-label edges*, resolving the walk-position issue that
blocks a fixed-length factorization.

The trick is to split not `W^p` (fixed length) but the whole path matrix, by **first passage through a
high-label edge**.  Fix `j` and let `L = lowMask j` be the edges of label `≤ j`, `H = highMask j` the
rest.  A walk using only `≤ j`-labelled edges has length `< 2^j` (`lowMask_pow_eq_zero`), so every long
walk contains a high-label edge; splitting at its *first* one, and summing over **all** lengths, closes
into a convolution:

* `firstPassage_split` — `pathMatrix = lowPath j + pathMatrix · highMask j · lowPath j`, where
  `lowPath j = ∑_{a<2^j} (lowMask j)^a` (all low-label walks — length `< 2^j`).  This is the `M = C + L`
  split, proved algebraically from `(1−W)·pathMatrix = 1` and `(1−L)·lowPath = 1` (geometric series /
  nilpotency), i.e. the `(I−W)⁻¹` identity `(I−W)⁻¹ = (I−L)⁻¹ + (I−W)⁻¹ H (I−L)⁻¹`.
* `highPart_rank_le` — `rank (pathMatrix · highMask j · lowPath j) ≤ rank (highMask j)`: the long part's
  rank is bounded by the rank of the **high-label-edge** matrix, `≤` the number of high-label edges.
* `lowPath_support` — the short part is supported on low-label walks of length `< 2^j`.

Because the rank is controlled by `highMask j` (label `> j` edges) rather than by `N`, this is sharp for
sparse circuits: choosing `j` trades the sparse part's reach (`< 2^j`) against the long part's rank
(`#` high-label edges).

## Honest scope

`firstPassage_split` and the rank bound are unconditional and exact.  What they give, for every `j`, is
`M = C + L` with `C` = low-label walks (length `< 2^j`) and `rank L ≤ rank (highMask j) ≤ #{label > j
edges}`.  The headline `s / log d` is the *numerical instantiation*: with `B ≈ log d` label classes
summing to `s` edges, balance `j` so the high-edge count and the sparse reach meet — that choice depends
on the circuit's edge distribution (degree/size), and is **not** discharged here as a bare pigeonhole.
Rigidity itself stays the open, P≠NP-strength input.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

namespace LinCircuit

variable {F : Type*} [Field F] {N : ℕ}

/-- Geometric-series telescoping (left form): `(1 − X)·∑_{i<n} X^i = 1 − X^n`. -/
theorem one_sub_mul_geomSum (X : Matrix (Fin N) (Fin N) F) (n : ℕ) :
    (1 - X) * ∑ i ∈ Finset.range n, X ^ i = 1 - X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, sub_mul, one_mul, ← pow_succ']
    abel

/-- Geometric-series telescoping (right form): `(∑_{i<n} X^i)·(1 − X) = 1 − X^n`. -/
theorem geomSum_mul_one_sub (X : Matrix (Fin N) (Fin N) F) (n : ℕ) :
    (∑ i ∈ Finset.range n, X ^ i) * (1 - X) = 1 - X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, mul_sub, mul_one, ← pow_succ]
    abel

/-- Label `≤ j` ⇒ the two levels agree at exponent `j`. -/
theorem labelExp_le_agrees {a b j : ℕ} (h : labelExp a b ≤ j) : a / 2 ^ j = b / 2 ^ j := by
  have hspec := labelExp_spec a b
  obtain ⟨d, hd⟩ := Nat.le.dest h
  subst hd
  rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hspec]

variable (G : LinCircuit F N)

/-- The **low-label sub-adjacency**: keep the edges of label `≤ j`. -/
def lowMaskMat (j : ℕ) : Matrix (Fin N) (Fin N) F :=
  fun u v => if labelExp (G.lvl v) (G.lvl u) ≤ j then G.W u v else 0

/-- The low-label class as a circuit (same levels; edges still strictly raise the level). -/
def lowMask (j : ℕ) : LinCircuit F N where
  W := G.lowMaskMat j
  lvl := G.lvl
  edge_raises u v h := by
    simp only [lowMaskMat] at h
    split_ifs at h with hc
    · exact G.edge_raises u v h
    · exact absurd rfl h

@[simp] theorem lowMask_W_apply (j : ℕ) (u v : Fin N) :
    (G.lowMask j).W u v = if labelExp (G.lvl v) (G.lvl u) ≤ j then G.W u v else 0 := rfl

/-- A walk using only label-`≤ j` edges keeps its endpoints in one width-`2^j` level window. -/
theorem lowMask_agrees (j : ℕ) (u : Fin N) (k : ℕ) :
    ∀ v : Fin N, ((G.lowMask j).W ^ k) u v ≠ 0 → G.lvl v / 2 ^ j = G.lvl u / 2 ^ j := by
  induction k with
  | zero =>
    intro v h
    rw [pow_zero, Matrix.one_apply] at h
    by_cases huv : u = v
    · subst huv; rfl
    · simp [huv] at h
  | succ k ih =>
    intro v h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : ((G.lowMask j).W ^ k) u w ≠ 0 := left_ne_zero_of_mul hw
    have h2 : (G.lowMask j).W w v ≠ 0 := right_ne_zero_of_mul hw
    rw [lowMask_W_apply] at h2
    split_ifs at h2 with hc
    · rw [labelExp_le_agrees hc]; exact ih w h1
    · exact absurd rfl h2

/-- A walk using only label-`≤ j` edges has length `< 2^j`. -/
theorem lowMask_walk_short (j : ℕ) {k : ℕ} {u v : Fin N}
    (h : ((G.lowMask j).W ^ k) u v ≠ 0) : k < 2 ^ j := by
  have hlvl : G.lvl v + k ≤ G.lvl u := (G.lowMask j).walk_level_bound u k v h
  have hag : G.lvl v / 2 ^ j = G.lvl u / 2 ^ j := G.lowMask_agrees j u k v h
  have hsub : G.lvl u - G.lvl v < 2 ^ j := sub_lt_of_div_eq (pow_pos (by norm_num) j) hag.symm
  omega

/-- The low-label class is shallow: `(lowMask j)^k = 0` once `k ≥ 2^j`. -/
theorem lowMask_pow_eq_zero (j : ℕ) {k : ℕ} (hk : 2 ^ j ≤ k) : (G.lowMask j).W ^ k = 0 := by
  ext u v
  rw [Matrix.zero_apply]
  by_contra h
  exact absurd (G.lowMask_walk_short j h) (not_lt.mpr hk)

/-- The **high-label edges**: label `> j`. -/
def highMask (j : ℕ) : Matrix (Fin N) (Fin N) F := G.W - (G.lowMask j).W

/-- The **low-label path matrix**: all walks using only `≤ j`-labelled edges (length `< 2^j`). -/
def lowPath (j : ℕ) : Matrix (Fin N) (Fin N) F :=
  ∑ i ∈ Finset.range (2 ^ j), (G.lowMask j).W ^ i

theorem one_sub_W_mul_pathMatrix : (1 - G.W) * G.pathMatrix = 1 := by
  unfold pathMatrix
  rw [one_sub_mul_geomSum, G.pow_eq_zero_of_maxLvl_lt (Nat.lt_succ_self _), sub_zero]

theorem pathMatrix_mul_one_sub_W : G.pathMatrix * (1 - G.W) = 1 := by
  unfold pathMatrix
  rw [geomSum_mul_one_sub, G.pow_eq_zero_of_maxLvl_lt (Nat.lt_succ_self _), sub_zero]

theorem one_sub_lowMask_mul_lowPath (j : ℕ) : (1 - (G.lowMask j).W) * G.lowPath j = 1 := by
  unfold lowPath
  rw [one_sub_mul_geomSum, G.lowMask_pow_eq_zero j (le_refl _), sub_zero]

/-- **The label first-passage split.**  `pathMatrix = lowPath + pathMatrix · highMask · lowPath` — the
`M = C + L` split, `C` the low-label walks and `L` routed through the high-label edges.  This is the
resolvent identity `(I−W)⁻¹ = (I−L)⁻¹ + (I−W)⁻¹ H (I−L)⁻¹`. -/
theorem firstPassage_split (j : ℕ) :
    G.pathMatrix = G.lowPath j + G.pathMatrix * G.highMask j * G.lowPath j := by
  have hLH : G.W = (G.lowMask j).W + G.highMask j := by unfold highMask; abel
  have hP1 := G.one_sub_W_mul_pathMatrix
  have hP2 := G.pathMatrix_mul_one_sub_W
  have hQ := G.one_sub_lowMask_mul_lowPath j
  have hmid : (1 - G.W) * G.lowPath j = 1 - G.highMask j * G.lowPath j := by
    rw [hLH,
      show (1 : Matrix (Fin N) (Fin N) F) - ((G.lowMask j).W + G.highMask j)
          = (1 - (G.lowMask j).W) - G.highMask j from by abel,
      sub_mul, hQ]
  have step1 : (1 - G.W) * (G.pathMatrix - G.lowPath j) = G.highMask j * G.lowPath j := by
    rw [mul_sub, hP1, hmid]; abel
  have step2 : G.pathMatrix - G.lowPath j = G.pathMatrix * (G.highMask j * G.lowPath j) := by
    calc G.pathMatrix - G.lowPath j
        = (G.pathMatrix * (1 - G.W)) * (G.pathMatrix - G.lowPath j) := by rw [hP2, one_mul]
      _ = G.pathMatrix * ((1 - G.W) * (G.pathMatrix - G.lowPath j)) := by rw [Matrix.mul_assoc]
      _ = G.pathMatrix * (G.highMask j * G.lowPath j) := by rw [step1]
  rw [← Matrix.mul_assoc, sub_eq_iff_eq_add'] at step2
  exact step2

/-- **The long part's rank is bounded by the high-label-edge matrix.**  `rank (pathMatrix · highMask ·
lowPath) ≤ rank (highMask j)`. -/
theorem highPart_rank_le (j : ℕ) :
    (G.pathMatrix * G.highMask j * G.lowPath j).rank ≤ (G.highMask j).rank :=
  rank_mul_mul_le_mid _ _ _

/-- The short part is supported on low-label walks of length `< 2^j`. -/
theorem lowPath_support (j : ℕ) {u v : Fin N} (h : (G.lowPath j) u v ≠ 0) :
    ∃ i ∈ Finset.range (2 ^ j), ((G.lowMask j).W ^ i) u v ≠ 0 := by
  unfold lowPath at h
  rw [Matrix.sum_apply] at h
  exact Finset.exists_ne_zero_of_sum_ne_zero h

/-- **The label first-passage sparse + low-rank split.**  For every `j`:
`pathMatrix = lowPath + (long part)`, the short `lowPath` supported on length-`< 2^j` low-label walks,
and the long part of rank `≤ rank (highMask j)` — the high-label-edge count.  The sharper (than
`N/depth`) split, with the rank pinned to the label-`> j` edges. -/
theorem valiant_label_firstpassage_split (j : ℕ) :
    G.pathMatrix = G.lowPath j + G.pathMatrix * G.highMask j * G.lowPath j ∧
      (∀ u v, (G.lowPath j) u v ≠ 0 →
        ∃ i ∈ Finset.range (2 ^ j), ((G.lowMask j).W ^ i) u v ≠ 0) ∧
      (G.pathMatrix * G.highMask j * G.lowPath j).rank ≤ (G.highMask j).rank :=
  ⟨G.firstPassage_split j, fun _ _ h => G.lowPath_support j h, G.highPart_rank_le j⟩

end LinCircuit

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
