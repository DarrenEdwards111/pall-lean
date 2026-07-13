import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBestPartitionReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBestPartitionExistence

/-!
# Cut-local character-span bridge (block rank → character span dimension)

**Scope correction.**  An earlier version of this file claimed a *global* best-partition-hard bond.  That was
overclaimed: the statements below are **cut-local**.  For each cut `S`, `charBlockSet (blk S M)` builds a *fresh*
character family from that cut's block `B`, i.e. a *different* bilinear function per cut.  There is no single global
`f : (Fin (2h) → Bool) → K`, no `residualOf S f`, and no proof that these cut-local families are residuals of one
function — so `finrank(span …)` here is **not** the tensor bond of a fixed function across every partition.  The
genuine statement, `∃ f, ∀ balanced S, 2^r ≤ finrank(span(range (residualOf S f)))`, is **not yet formalized**: it
requires a single global quadratic form `QF A z = sgn(∑ᵢⱼ Aᵢⱼ·bit zᵢ·bit zⱼ)`, the residual factorization
`residualOf S (QF A) α = D(z)·c(α)·χ_{y(α)}` (sum-split + the sign homomorphism `sgn(a+b)=sgn a·sgn b`), and a
probabilistic existence over the **symmetrized** block `(A+Aᵀ)[S][Sᶜ]` (the directed `exists_best_partition_hard`
does not transfer).  Foundations verified; the full build is pending.

What this file *correctly* proves is the **block-rank → character-span bridge**: a single `𝔽₂` block `B` of rank
`q` canonically generates `2^q` linearly independent Walsh characters.

* `charBlockSet B` — the `2^{rank B}` distinct characters `χ_{Bᵀa}` of the block `B`;
* `block_charspan_eq` — their span has dimension exactly `2^{rank B}` (`chi_subset_finrank` +
  `Module.card_eq_pow_finrank`);
* `exists_cutwise_charspan` — the rigid matrix supplies such a large *cut-local* family for every cut (**not** one
  shared function).

## Honest scope

A clean block-rank / character-span bridge, cut-local only.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BestPartitionBond

open Matrix
open PallLean.Paper93.DeepMath.PathB.InnerProductCommRank
open PallLean.Paper93.DeepMath.PathB.BestPartitionReduction
open PallLean.Paper93.DeepMath.PathB.BestPartitionExistence

variable {K : Type*} [Field K] [CharZero K] {h r : ℕ}

/-- Coordinatewise `ZMod 2 → Bool`. -/
def toBoolVec (c : Fin h → ZMod 2) : Fin h → Bool := fun i => decide (c i = 1)

theorem toBoolVec_injective : Function.Injective (toBoolVec (h := h)) := by
  intro c c' hcc
  funext i
  have : decide (c i = 1) = decide (c' i = 1) := congrFun hcc i
  have hinj : Function.Injective (fun z : ZMod 2 => decide (z = 1)) := by decide
  exact hinj this

/-- The set of distinct residual characters of the block `B` (indexed by `Bᵀa`). -/
noncomputable def charBlockSet (B : Matrix (Fin h) (Fin h) (ZMod 2)) : Finset (Fin h → Bool) :=
  Finset.univ.image (fun a : Fin h → ZMod 2 => toBoolVec (B.transpose *ᵥ a))

/-- `|image(Bᵀ)| = 2^{rank B}`. -/
theorem img_card (B : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (Finset.univ.image (fun a : Fin h → ZMod 2 => B.transpose *ᵥ a)).card = 2 ^ B.rank := by
  classical
  have h1 : (Finset.univ.image (fun a : Fin h → ZMod 2 => B.transpose *ᵥ a))
      = (LinearMap.range B.transpose.mulVecLin : Set (Fin h → ZMod 2)).toFinset := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_toFinset, SetLike.mem_coe,
      LinearMap.mem_range, Matrix.mulVecLin_apply]
  rw [h1, Set.toFinset_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2]
  congr 1
  rw [← Matrix.rank_transpose (A := B)]
  rfl

/-- The block has exactly `2^{rank B}` distinct residual characters. -/
theorem charBlockSet_card (B : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (charBlockSet B).card = 2 ^ B.rank := by
  classical
  have heq : charBlockSet B
      = (Finset.univ.image (fun a : Fin h → ZMod 2 => B.transpose *ᵥ a)).image toBoolVec := by
    unfold charBlockSet
    rw [Finset.image_image]
    rfl
  rw [heq, Finset.card_image_of_injective _ toBoolVec_injective, img_card]

/-- **Block-rank → character-span.**  The distinct characters of a block `B` are linearly independent
(`chi_subset_finrank`), so their span has dimension exactly `2^{rank B}`.  (Cut-local: this is the character span of
*one block*, not the residual span of a global function.) -/
theorem block_charspan_eq (B : Matrix (Fin h) (Fin h) (ZMod 2)) :
    Module.finrank K
        (Submodule.span K (Set.range (fun t : (charBlockSet B) => chi (K := K) t.val)))
      = 2 ^ B.rank := by
  rw [chi_subset_finrank, charBlockSet_card]

/-- **Cut-local character families.**  For `2r + 2 < h`, the rigid matrix supplies, at every balanced partition, a
character family of span-dimension `≥ 2^r`.  NOTE: for each cut `S` this is a *different* family
`charBlockSet (blk S M)` — a fresh bilinear function per cut, **not** the residual span of one shared function.  The
global `∃ f, ∀ S` statement is not yet formalized (see the file header). -/
theorem exists_cutwise_charspan (hh : 2 * r + 2 < h) :
    ∃ M : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ∀ S : Finset (Fin (2 * h)), S.card = h →
        2 ^ r ≤ Module.finrank K
          (Submodule.span K (Set.range (fun t : (charBlockSet (blk S M)) => chi (K := K) t.val))) := by
  obtain ⟨M, hM⟩ := exists_best_partition_hard hh
  refine ⟨M, fun S hS => ?_⟩
  rw [block_charspan_eq]
  exact Nat.pow_le_pow_right (by norm_num) (hM S hS)

end PallLean.Paper93.DeepMath.PathB.BestPartitionBond

#print axioms PallLean.Paper93.DeepMath.PathB.BestPartitionBond.block_charspan_eq
#print axioms PallLean.Paper93.DeepMath.PathB.BestPartitionBond.exists_cutwise_charspan
