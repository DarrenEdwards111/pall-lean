import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGModel
import Mathlib.Data.Nat.Log

/-!
# Valiant's covering lemma (labeling form) on the DAG model

The combinatorial heart of Valiant's reduction, built on the `LinCircuit` DAG model.  We label each
edge `v → u` by the *most significant bit position at which `lvl v` and `lvl u` first agree* — i.e. the
smallest `t` with `lvl v / 2^t = lvl u / 2^t` (`labelExp`).  The two facts that make this Valiant's
argument:

* **each label class is shallow** (`labelClass_pow_eq_zero`): a walk that uses only label-`t` edges has
  length `< 2^t`, because all its vertices share the same high bits of their level (they lie in one
  window of width `2^t`) while levels strictly increase.  So the label-`t` sub-adjacency is nilpotent
  at index `2^t`.
* **logarithmically many classes cover every edge** (`labelClass_sum_W`, `labelBound_le`): every edge
  has a label `< log₂(maxLvl) + 2`, and summing the classes rebuilds `W`.

Packaged as `valiant_covering_labeling`: `W` decomposes into `O(log depth)` shallow classes.  This is
exactly the structural engine of Valiant's covering lemma — the reason a size-`s`, depth-`d` circuit's
long-walk contribution can be captured by few "special" vertices.

## Honest scope

This builds the **labeling / shallow-class decomposition** — the genuine combinatorial core, fully
proved, no `sorry`.  The **final assembly** — turning the `O(log d)` shallow classes into a concrete
`s / log d` vertex hitting set and the resulting rank bound on the long-walk matrix — is the remaining
step, not built here.  With the earlier files (`rank_le_inner_dim`, `notRigid_of_factorization`) that
assembly is what would yield `M = C + L` with `rank L ≈ s / log d`.  Rigidity itself stays the open,
P≠NP-strength input.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

namespace LinCircuit

variable {F : Type*} [Field F] {N : ℕ}

/-- Two naturals with the same quotient by `p > 0` differ by less than `p`. -/
theorem sub_lt_of_div_eq {a b p : ℕ} (hp : 0 < p) (h : a / p = b / p) : a - b < p := by
  have ha := Nat.div_add_mod a p
  have hb := Nat.div_add_mod b p
  have hma : a % p < p := Nat.mod_lt a hp
  have hmb : b % p < p := Nat.mod_lt b hp
  rw [h] at ha
  omega

/-- For a large enough exponent, `a` and `b` agree (both quotients vanish). -/
theorem agree_exp_exists (a b : ℕ) : ∃ n, a / 2 ^ n = b / 2 ^ n := by
  refine ⟨Nat.log 2 (a ⊔ b) + 1, ?_⟩
  have hbig : a ⊔ b < 2 ^ (Nat.log 2 (a ⊔ b) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  rw [Nat.div_eq_of_lt (lt_of_le_of_lt le_sup_left hbig),
      Nat.div_eq_of_lt (lt_of_le_of_lt le_sup_right hbig)]

/-- **The edge label**: the smallest exponent `t` at which the two levels agree, `lvl v / 2^t =
lvl u / 2^t`.  For an edge (`lvl v < lvl u`) this is the most-significant differing bit position `+ 1`. -/
def labelExp (a b : ℕ) : ℕ := Nat.find (agree_exp_exists a b)

theorem labelExp_spec (a b : ℕ) : a / 2 ^ labelExp a b = b / 2 ^ labelExp a b :=
  Nat.find_spec (agree_exp_exists a b)

/-- The label is at most `log₂ b + 1`: once the exponent exceeds the bit-length, both quotients are 0. -/
theorem labelExp_le_log (a b : ℕ) (hab : a ≤ b) : labelExp a b ≤ Nat.log 2 b + 1 := by
  unfold labelExp
  refine Nat.find_le ?_
  have hb : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self (by norm_num) b
  rw [Nat.div_eq_of_lt (lt_of_le_of_lt hab hb), Nat.div_eq_of_lt hb]

variable (G : LinCircuit F N)

/-- The **label-`t` sub-adjacency**: keep only the edges whose label is `t`. -/
def labelMask (t : ℕ) : Matrix (Fin N) (Fin N) F :=
  fun u v => if labelExp (G.lvl v) (G.lvl u) = t then G.W u v else 0

/-- The label-`t` class as a circuit in its own right (same levels; edges still strictly raise the
level, being a subset of `G`'s edges). -/
def labelClass (t : ℕ) : LinCircuit F N where
  W := G.labelMask t
  lvl := G.lvl
  edge_raises u v h := by
    simp only [labelMask] at h
    split_ifs at h with hc
    · exact G.edge_raises u v h
    · exact absurd rfl h

@[simp] theorem labelClass_W_apply (t : ℕ) (u v : Fin N) :
    (G.labelClass t).W u v = if labelExp (G.lvl v) (G.lvl u) = t then G.W u v else 0 := rfl

@[simp] theorem labelClass_lvl (t : ℕ) : (G.labelClass t).lvl = G.lvl := rfl

/-- **All vertices of a monochromatic-`t` walk share the same high bits.**  A walk using only label-`t`
edges has `lvl v / 2^t = lvl u / 2^t` for its endpoints. -/
theorem labelClass_agrees (t : ℕ) (u : Fin N) (k : ℕ) :
    ∀ v : Fin N, ((G.labelClass t).W ^ k) u v ≠ 0 → G.lvl v / 2 ^ t = G.lvl u / 2 ^ t := by
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
    have h1 : ((G.labelClass t).W ^ k) u w ≠ 0 := left_ne_zero_of_mul hw
    have h2 : (G.labelClass t).W w v ≠ 0 := right_ne_zero_of_mul hw
    rw [labelClass_W_apply] at h2
    split_ifs at h2 with hc
    · have e1 : G.lvl v / 2 ^ t = G.lvl w / 2 ^ t := by
        rw [← hc]; exact labelExp_spec _ _
      have e2 : G.lvl w / 2 ^ t = G.lvl u / 2 ^ t := ih w h1
      rw [e1, e2]
    · exact absurd rfl h2

/-- **Each label class is shallow.**  A walk using only label-`t` edges has length `< 2^t`. -/
theorem labelClass_walk_short (t : ℕ) {k : ℕ} {u v : Fin N}
    (h : ((G.labelClass t).W ^ k) u v ≠ 0) : k < 2 ^ t := by
  have hlvl : G.lvl v + k ≤ G.lvl u := (G.labelClass t).walk_level_bound u k v h
  have hagree : G.lvl v / 2 ^ t = G.lvl u / 2 ^ t := G.labelClass_agrees t u k v h
  have hsub : G.lvl u - G.lvl v < 2 ^ t :=
    sub_lt_of_div_eq (pow_pos (by norm_num) t) hagree.symm
  omega

/-- **Label-`t` nilpotency.**  `(labelClass t).W ^ k = 0` once `k ≥ 2^t`: monochromatic classes are
shallow, capped at depth `2^t`. -/
theorem labelClass_pow_eq_zero (t : ℕ) {k : ℕ} (hk : 2 ^ t ≤ k) :
    (G.labelClass t).W ^ k = 0 := by
  ext u v
  rw [Matrix.zero_apply]
  by_contra h
  exact absurd (G.labelClass_walk_short t h) (not_lt.mpr hk)

/-- A logarithmic bound on the number of label classes needed. -/
def labelBound : ℕ := Nat.log 2 G.maxLvl + 2

theorem labelExp_lt_labelBound {u v : Fin N} (h : G.W u v ≠ 0) :
    labelExp (G.lvl v) (G.lvl u) < G.labelBound := by
  have hlt : G.lvl v < G.lvl u := G.edge_raises u v h
  have hle : labelExp (G.lvl v) (G.lvl u) ≤ Nat.log 2 (G.lvl u) + 1 :=
    labelExp_le_log _ _ (le_of_lt hlt)
  have hmono : Nat.log 2 (G.lvl u) ≤ Nat.log 2 G.maxLvl :=
    Nat.log_mono_right (G.lvl_le_maxLvl u)
  unfold labelBound
  omega

/-- **The classes partition the edges.**  Summing the label classes over the logarithmic range
rebuilds the full adjacency `W`. -/
theorem labelClass_sum_W :
    ∑ t ∈ Finset.range G.labelBound, (G.labelClass t).W = G.W := by
  ext u v
  rw [Matrix.sum_apply]
  simp only [labelClass_W_apply]
  rw [Finset.sum_ite_eq]
  by_cases hmem : labelExp (G.lvl v) (G.lvl u) ∈ Finset.range G.labelBound
  · rw [if_pos hmem]
  · rw [if_neg hmem]
    symm
    by_contra hne
    exact hmem (Finset.mem_range.mpr (G.labelExp_lt_labelBound hne))

/-- **Valiant's covering lemma, labeling form.**  The adjacency `W` of any linear-circuit DAG splits
into `O(log depth)` label classes, each of which is *shallow* (nilpotent at depth `2^t`):

* `W = ∑_{t < labelBound} (labelClass t).W` (the classes cover all edges);
* `labelBound ≤ log₂(maxLvl) + 2` (logarithmically many);
* every class satisfies `(labelClass t).W ^ (2^t) = 0` (short monochromatic walks).

This is the combinatorial engine of the covering lemma. -/
theorem valiant_covering_labeling :
    G.W = ∑ t ∈ Finset.range G.labelBound, (G.labelClass t).W ∧
    G.labelBound ≤ Nat.log 2 G.maxLvl + 2 ∧
    ∀ t, (G.labelClass t).W ^ (2 ^ t) = 0 :=
  ⟨G.labelClass_sum_W.symm, le_refl _, fun t => G.labelClass_pow_eq_zero t (le_refl _)⟩

end LinCircuit

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
