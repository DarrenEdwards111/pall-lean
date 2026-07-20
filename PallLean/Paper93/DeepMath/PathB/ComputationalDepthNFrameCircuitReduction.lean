import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRigidLowerBound

/-!
# Circuit ⇒ non-rigidity: the low-rank ingredient of Valiant's reduction

Valiant's other half — a small, log-depth linear circuit computing `M` gives a sparse + low-rank
decomposition — splits into an **algebraic** half and a **combinatorial** half:

* algebraic (already have, `notRigid_of_factorization`): once the circuit is split into a sparse part
  `C` (short paths) and a part factoring through `r` shared vertices (long paths), `M = C + A·B` makes
  `M` not `(r,s)`-rigid;
* combinatorial (**Valiant's covering lemma**, NOT built here): a size-`s`, depth-`d` circuit *has* such
  a split with `r ≈ s / log d` — few vertices cover all long paths.

This file supplies the clean **low-rank ingredient**: a circuit with a width-`w` cut (every path through
`w` shared wires) computes a rank-`≤ w` matrix, hence a non-rigid one.  For a *levelled* circuit every
path crosses every layer, so this applies at the thinnest layer; the covering lemma is exactly what
handles circuits with no thin layer.

* `CircuitFactorsAt M w` — `M` is realized by a circuit with a width-`w` cut: `M = A · B`, `A : n×w`,
  `B : w×n`.
* `circuit_rank_le_width` — such an `M` has rank `≤ w`.
* `circuit_nonrigid` — hence `M` is not `(w, 0)`-rigid: a thin-cut circuit is non-rigid.

## Honest scope

The genuinely hard content — **Valiant's covering lemma** (size/depth ⇒ a small long-path cover),
which needs a DAG/circuit graph model and the depth-reduction argument — is **not** built here; it is
the remaining classical combinatorial theorem.  What is complete: the algebraic half
(`notRigid_of_factorization`) and this low-rank ingredient.  Rigidity itself stays the open,
P≠NP-strength input.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

variable {n : ℕ} {F : Type*} [Field F]

/-- `M` is realized by a linear circuit with a width-`w` cut: it factors as `A · B` through `w` shared
wires. -/
def CircuitFactorsAt (M : Matrix (Fin n) (Fin n) F) (w : ℕ) : Prop :=
  ∃ (A : Matrix (Fin n) (Fin w) F) (B : Matrix (Fin w) (Fin n) F), M = A * B

/-- The zero matrix has no nonzero entries. -/
theorem sparsity_zero : sparsity (0 : Matrix (Fin n) (Fin n) F) = 0 := by
  simp [sparsity]

/-- **Thin cut ⇒ low rank.**  A circuit with a width-`w` cut computes a rank-`≤ w` matrix. -/
theorem circuit_rank_le_width (M : Matrix (Fin n) (Fin n) F) {w : ℕ}
    (h : CircuitFactorsAt M w) : M.rank ≤ w := by
  obtain ⟨A, B, hM⟩ := h
  rw [hM]; exact rank_le_inner_dim A B

/-- **Thin cut ⇒ non-rigid.**  A circuit with a width-`w` cut computes a matrix that is not
`(w, 0)`-rigid — the low-rank ingredient of Valiant's reduction (the sparse part is empty here; the
covering lemma supplies the sparse + low-rank split in general). -/
theorem circuit_nonrigid (M : Matrix (Fin n) (Fin n) F) {w : ℕ}
    (h : CircuitFactorsAt M w) : ¬ MatrixRigid M w 0 := by
  obtain ⟨A, B, hM⟩ := h
  exact notRigid_of_factorization M 0 A B (by rw [zero_add]; exact hM) (by rw [sparsity_zero])

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
