import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitReduction

/-!
# A DAG model for linear circuits

The substrate Valiant's covering lemma needs: a linear circuit as a **weighted directed acyclic
graph**, with the path/walk structure exposed algebraically through powers of the adjacency matrix.

A circuit has `N` vertices, a weighted adjacency `W` (`W u v` = weight of the edge `v → u`), and a
level function `lvl` that *every edge strictly raises*.  The level condition is exactly acyclicity in a
usable form, and it makes the whole path structure computable:

* `(W^k) u v` is the total weight of length-`k` walks from `v` to `u` (matrix power = walk sum);
* `walk_level_bound` — a length-`k` walk raises the level by `≥ k` (each edge raises it by `≥ 1`).  This
  is the seed of Valiant's argument: **long walks cross many levels**.
* `pow_eq_zero_of_maxLvl_lt` / `walk_length_le_maxLvl` — hence no walk is longer than `maxLvl`: `W` is
  nilpotent, the graph is acyclic, and depth `≤ maxLvl`.
* `pathMatrix` — the total-weight-of-all-walks matrix `∑_k W^k` (a finite sum, higher terms vanish).
* `compMatrix` — the matrix the circuit computes from chosen input to chosen output vertices.

## Honest scope

This is the **model + its structural core** (the level/nilpotency geometry and the path interpretation)
— the graph substrate on which Valiant's covering lemma would be proved.  The **covering lemma itself**
— that a size-`s`, depth-`d` circuit's long-walk contribution has rank `≈ s / log d` because few
vertices cover all long walks — is the substantial combinatorial argument and is **not** built here.
What this gives is the honest foundation for it: walks are matrix powers, and long walks provably cross
many levels.  Rigidity itself stays the open, P≠NP-strength input.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

/-- A **linear circuit as a weighted DAG**: `N` vertices, a weighted adjacency `W` (`W u v` is the
weight of the edge `v → u`), and a level/depth function `lvl` that every edge strictly raises.  The
level condition makes the graph acyclic. -/
structure LinCircuit (F : Type*) [Field F] (N : ℕ) where
  /-- weighted adjacency: `W u v` = weight of the edge from `v` into `u`. -/
  W : Matrix (Fin N) (Fin N) F
  /-- level (depth) of each vertex. -/
  lvl : Fin N → ℕ
  /-- every edge strictly raises the level (hence the graph is acyclic). -/
  edge_raises : ∀ u v, W u v ≠ 0 → lvl v < lvl u

namespace LinCircuit

variable {F : Type*} [Field F] {N : ℕ} (G : LinCircuit F N)

/-- The maximum level over all vertices — an a-priori depth bound. -/
def maxLvl : ℕ := Finset.univ.sup G.lvl

theorem lvl_le_maxLvl (u : Fin N) : G.lvl u ≤ G.maxLvl :=
  Finset.le_sup (Finset.mem_univ u)

/-- **Structural core.**  A length-`k` walk from `v` to `u` (i.e. `(W^k) u v ≠ 0`) raises the level by
at least `k`: `lvl v + k ≤ lvl u`.  Each edge raises the level by `≥ 1`, so `k` edges raise it by
`≥ k` — long walks cross many levels. -/
theorem walk_level_bound (u : Fin N) (k : ℕ) :
    ∀ v : Fin N, (G.W ^ k) u v ≠ 0 → G.lvl v + k ≤ G.lvl u := by
  induction k with
  | zero =>
    intro v h
    rw [pow_zero, Matrix.one_apply] at h
    by_cases huv : u = v
    · subst huv; simp
    · simp [huv] at h
  | succ k ih =>
    intro v h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : (G.W ^ k) u w ≠ 0 := left_ne_zero_of_mul hw
    have h2 : G.W w v ≠ 0 := right_ne_zero_of_mul hw
    have e1 : G.lvl w + k ≤ G.lvl u := ih w h1
    have e2 : G.lvl v < G.lvl w := G.edge_raises w v h2
    omega

/-- **Acyclicity / nilpotency.**  There is no walk longer than `maxLvl`: `W^k = 0` once `k > maxLvl`. -/
theorem pow_eq_zero_of_maxLvl_lt {k : ℕ} (hk : G.maxLvl < k) : G.W ^ k = 0 := by
  ext u v
  rw [Matrix.zero_apply]
  by_contra h
  have hb := G.walk_level_bound u k v h
  have hu := G.lvl_le_maxLvl u
  omega

/-- Every walk has length at most `maxLvl`. -/
theorem walk_length_le_maxLvl {k : ℕ} {u v : Fin N} (h : (G.W ^ k) u v ≠ 0) : k ≤ G.maxLvl := by
  have hb := G.walk_level_bound u k v h
  have hu := G.lvl_le_maxLvl u
  omega

/-- The **path matrix**: `pathMatrix u v = ∑_k (W^k) u v` = the total weight of all walks from `v` to
`u`.  The sum is finite because every walk has length `≤ maxLvl`. -/
def pathMatrix : Matrix (Fin N) (Fin N) F :=
  ∑ k ∈ Finset.range (G.maxLvl + 1), G.W ^ k

/-- The **computed matrix** of the circuit for chosen input vertices `inp` and output vertices `out`:
entry `(i,j)` is the total weight of all walks from input `j` to output `i`. -/
def compMatrix {n m : ℕ} (inp : Fin n → Fin N) (out : Fin m → Fin N) :
    Matrix (Fin m) (Fin n) F :=
  Matrix.of fun i j => G.pathMatrix (out i) (inp j)

end LinCircuit

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
