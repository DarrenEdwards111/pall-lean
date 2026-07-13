import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorEntanglementLowerBound

/-!
# The inner-product communication matrix has full rank (Walsh/Hadamard)

This is the canonical communication-complexity rank lower bound, formalized directly. The `±1` inner-product
function `χ_y(x) = (-1)^{⟨x,y⟩} = ∏ᵢ (-1)^{xᵢyᵢ}` gives, across the `x | y` partition, the `2^N × 2^N` Walsh–
Hadamard matrix. Its `2^N` rows (the characters) are **linearly independent** over any `CharZero` field, via the
orthogonality relation `∑_x χ_y(x) χ_{y'}(x) = 2^N · [y = y']`. Hence the communication matrix has **full rank
`2^N`**, and the tensor bond of inner product across the `x | y` cut is `2^N`.

* `chi_orthogonality` — `∑_x χ_y(x) χ_{y'}(x) = if y = y' then 2^N else 0`;
* `chi_linearIndependent` — the `2^N` characters are linearly independent;
* `chi_finrank` — the character span has dimension `2^N` (full rank).

## Honest scope — this is a FIXED-partition bound, not best-partition

Inner product is high-rank only across the **fixed `x | y` partition**.  It is **not** best-partition-hard: the
partition that keeps each pair `(xᵢ, yᵢ)` on the *same* side gives `IP = A_local ⊕ B_local`, a XOR of two local
sums — rank `2`.  So, like equality, inner product collapses under a good ordering; its `2^N` bond is an artifact
of the `x | y` split.  (This corrects `SCOPE_TN_HARDNESS_ATTACK` §3, which wrongly called IP best-partition-hard:
best-partition tensor-network hardness needs a function hard under *every* partition, which IP is not.)

A genuine, self-contained fixed-partition communication/tensor rank bound, in the same species as `eqFun`.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InnerProductCommRank

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- The `±1` inner-product character `χ_y(x) = (-1)^{⟨x,y⟩}`. -/
def chi (y x : Fin N → Bool) : K := ∏ i, (if x i && y i then (-1 : K) else 1)

/-- **Orthogonality of the characters** (the Walsh–Hadamard relation). -/
theorem chi_orthogonality (y y' : Fin N → Bool) :
    ∑ x : Fin N → Bool, chi y x * chi y' x = if y = y' then (2 : K) ^ N else 0 := by
  have hswap : ∀ F : Fin N → Bool → K,
      ∑ x : Fin N → Bool, ∏ i, F i (x i) = ∏ i, ∑ b : Bool, F i b := by
    intro F
    rw [← Finset.sum_prod_piFinset Finset.univ F, Fintype.piFinset_univ]
  simp only [chi, ← Finset.prod_mul_distrib]
  rw [hswap (fun i b => (if b && y i then (-1 : K) else 1) * (if b && y' i then (-1 : K) else 1))]
  have hcoord : ∀ i : Fin N,
      (∑ b : Bool, (if b && y i then (-1 : K) else 1) * (if b && y' i then (-1 : K) else 1))
        = if y i = y' i then (2 : K) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases y i <;> cases y' i <;> norm_num
  simp_rw [hcoord]
  by_cases hyy : y = y'
  · subst hyy; simp
  · rw [if_neg hyy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hyy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- **The characters are linearly independent** — the `2^N` rows of the Walsh–Hadamard matrix. -/
theorem chi_linearIndependent : LinearIndependent K (chi (K := K) (N := N)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum y'
  have hfun : ∀ x, ∑ y, c y * chi y x = 0 := by
    intro x
    have h := congrFun hsum x
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  have hA : ∑ x : Fin N → Bool, (∑ y, c y * chi y x) * chi y' x = c y' * (2 : K) ^ N := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, chi_orthogonality]
    rw [Finset.sum_eq_single y']
    · rw [if_pos rfl]
    · intro y _ hy; rw [if_neg hy, mul_zero]
    · intro h; exact absurd (Finset.mem_univ y') h
  have hB : ∑ x : Fin N → Bool, (∑ y, c y * chi y x) * chi y' x = 0 := by
    simp_rw [hfun, zero_mul, Finset.sum_const_zero]
  rw [hB] at hA
  exact (mul_eq_zero.mp hA.symm).resolve_right (pow_ne_zero N two_ne_zero)

/-- **Full rank.**  The inner-product communication matrix has rank `2^N` across the `x | y` partition. -/
theorem chi_finrank :
    Module.finrank K (Submodule.span K (Set.range (chi (K := K) (N := N)))) = 2 ^ N := by
  rw [finrank_span_eq_card chi_linearIndependent, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.InnerProductCommRank

#print axioms PallLean.Paper93.DeepMath.PathB.InnerProductCommRank.chi_linearIndependent
#print axioms PallLean.Paper93.DeepMath.PathB.InnerProductCommRank.chi_finrank
