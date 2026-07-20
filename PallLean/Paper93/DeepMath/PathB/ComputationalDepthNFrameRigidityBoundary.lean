import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameLabelFirstPassage

/-!
# The rigidity boundary: reducing the whole machine to one open input

The Valiant arc is complete except for two things, and this file treats each as it actually is.

**The reduction (proved).**  The label first-passage split writes every circuit's transfer matrix as
`pathMatrix = C + L` with `C` a low-label-walk matrix and `rank L ≤ rank (highMask j)`.  So the
transfer matrix is **provably not rigid** at those parameters (`pathMatrix_not_rigid`): a matrix that
*is* rigid there cannot be any linear-circuit DAG's transfer matrix (`rigid_pathMatrix_not_a_circuit`).
This is the payoff of the entire arc — it collapses "no small circuit for `M`" to "`M` is rigid," with
everything between machine-checked.

**The open input (not proved, not fakeable).**  Proving that an *explicit* matrix is rigid at
circuit-relevant parameters (superlinear sparsity budget, `≈ εn` rank) is a famous open problem; a real
proof would be a `P ≠ NP`-strength result.  It is stated here as a hypothesis
(`rigid_pathMatrix_not_a_circuit` takes rigidity as input) and **deliberately left open** — this file
does not, and cannot honestly, discharge it.  The only rigidity that is unconditionally provable is the
trivial universal bound (see `NFrameRankSparsity`: `identity_rigid`, `sparsity ≥ n − r`), which is far
below what circuit lower bounds require.

So the arc's honest end state: the reduction is done and axiom-clean; the strong rigidity it reduces to
is exactly the open problem, named and isolated, not fabricated.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

namespace LinCircuit

variable {F : Type*} [Field F] {N : ℕ} (G : LinCircuit F N)

/-- **A circuit's transfer matrix is not rigid.**  For every threshold `j`, `pathMatrix` is not
`(rank (highMask j), sparsity (lowPath j))`-rigid: the label first-passage split
`pathMatrix = lowPath j + (pathMatrix · highMask j · lowPath j)` is a witnessing sparse + low-rank
decomposition. -/
theorem pathMatrix_not_rigid (j : ℕ) :
    ¬ MatrixRigid G.pathMatrix (G.highMask j).rank (sparsity (G.lowPath j)) := by
  rw [notRigid_iff_decomp]
  exact ⟨G.lowPath j, G.pathMatrix * G.highMask j * G.lowPath j,
    le_refl _, G.highPart_rank_le j, G.firstPassage_split j⟩

/-- **The payoff: a rigid matrix is not a circuit's transfer matrix.**  If some target matrix `M`
equals a linear-circuit DAG's transfer matrix `pathMatrix`, and `M` is rigid at the first-passage
parameters, contradiction.  Contrapositive: a matrix rigid at `(rank (highMask j), sparsity (lowPath
j))` is **not** the transfer matrix of `G`.  This is the whole Valiant reduction discharged — modulo
the one open input, rigidity of `M`. -/
theorem rigid_pathMatrix_not_a_circuit {M : Matrix (Fin N) (Fin N) F} (j : ℕ)
    (hM : M = G.pathMatrix)
    (hrigid : MatrixRigid M (G.highMask j).rank (sparsity (G.lowPath j))) : False :=
  G.pathMatrix_not_rigid j (hM ▸ hrigid)

end LinCircuit

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
