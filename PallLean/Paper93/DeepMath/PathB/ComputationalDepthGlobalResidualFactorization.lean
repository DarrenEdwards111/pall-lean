import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorEntanglementLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInnerProductCommRank

/-!
# The global residual factorization

The genuine content behind the (retracted) "best-partition-hard bond": a **single global** quadratic form whose
`residualOf S f` across each cut factors into a fixed local sign times a Walsh character, so its residual-span
dimension is `≥` the number of distinct residual characters at that cut.  Unlike `BestPartitionBond` (a fresh
family per cut), this is `residualOf` of *one* function `QF A`.

`QF A z = sgn(∑ᵢⱼ Aᵢⱼ · bit zᵢ · bit zⱼ)` over `𝔽₂`, `sgn : ZMod 2 → K` the `±1` homomorphism.

* `residual_factor` — `residualOf S (QF (K := K) A) α = D · c(α) · χ_{y(α)}` (local sign `D`, constant `c(α)`, character
  `χ_{y(α)}`), via the residual sum-split and `sgn(a+b) = sgn a · sgn b`;
* `residual_finrank_ge` — `finrank(span(range (residualOf S (QF (K := K) A)))) ≥ #{distinct residual characters}` — a bound
  on the **tensor bond of the single function `QF A`** across the cut `S`.

The count `#{distinct residual characters} = 2^{rank((A+Aᵀ)[S][Sᶜ])}` and the existence of an `A` making it large
for every cut are the remaining pieces (a probabilistic existence over the symmetrized block).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GlobalResidual

open Matrix
open PallLean.Paper93.DeepMath.PathB.TensorEntanglement
open PallLean.Paper93.DeepMath.PathB.InnerProductCommRank

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- `Bool → ZMod 2`. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The `±1` sign character of `ZMod 2`. -/
noncomputable def sgn (a : ZMod 2) : K := if a = 1 then -1 else 1

theorem sgn_zero : sgn (K := K) 0 = 1 := by simp [sgn]

theorem sgn_ne_zero (a : ZMod 2) : sgn (K := K) a ≠ 0 := by unfold sgn; split <;> norm_num

theorem sgn_add (a b : ZMod 2) : sgn (K := K) (a + b) = sgn (K := K) a * sgn (K := K) b := by
  have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases key a with ha | ha <;> rcases key b with hb | hb <;> subst ha <;> subst hb <;>
    simp [sgn] <;> norm_num

theorem sgn_sum (t : Finset (Fin n)) (g : Fin n → ZMod 2) :
    sgn (K := K) (∑ i ∈ t, g i) = ∏ i ∈ t, sgn (K := K) (g i) := by
  classical
  induction t using Finset.induction with
  | empty => simp [sgn_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

/-- The quadratic-form value (`ZMod 2`). -/
def qf (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool) : ZMod 2 :=
  ∑ i, ∑ j, A i j * bit (z i) * bit (z j)

/-- **The global quadratic form** `QF A : (Fin n → Bool) → K`. -/
noncomputable def QF (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool) : K := sgn (qf A z)

/-- The residual sum-split into within-`S`, cross, and within-`Sᶜ`. -/
theorem qf_split (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) (z α : Fin n → Bool) :
    qf A (fun i => if i ∈ S then z i else α i)
      = (∑ i ∈ S, ∑ j ∈ S, A i j * bit (z i) * bit (z j))
        + ((∑ i ∈ S, ∑ j ∈ Sᶜ, A i j * bit (z i) * bit (α j))
           + (∑ i ∈ Sᶜ, ∑ j ∈ S, A i j * bit (α i) * bit (z j)))
        + (∑ i ∈ Sᶜ, ∑ j ∈ Sᶜ, A i j * bit (α i) * bit (α j)) := by
  classical
  unfold qf
  rw [← Finset.sum_add_sum_compl S]
  have hin : ∀ i ∈ S,
      (∑ j, A i j * bit (if i ∈ S then z i else α i) * bit (if j ∈ S then z j else α j))
        = (∑ j ∈ S, A i j * bit (z i) * bit (z j)) + (∑ j ∈ Sᶜ, A i j * bit (z i) * bit (α j)) := by
    intro i hi
    rw [← Finset.sum_add_sum_compl S]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j hj => ?_) (Finset.sum_congr rfl fun j hj => ?_)
    · rw [if_pos hi, if_pos hj]
    · rw [if_pos hi, if_neg (Finset.mem_compl.mp hj)]
  have hout : ∀ i ∈ Sᶜ,
      (∑ j, A i j * bit (if i ∈ S then z i else α i) * bit (if j ∈ S then z j else α j))
        = (∑ j ∈ S, A i j * bit (α i) * bit (z j)) + (∑ j ∈ Sᶜ, A i j * bit (α i) * bit (α j)) := by
    intro i hi
    rw [← Finset.sum_add_sum_compl S]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j hj => ?_) (Finset.sum_congr rfl fun j hj => ?_)
    · rw [if_neg (Finset.mem_compl.mp hi), if_pos hj]
    · rw [if_neg (Finset.mem_compl.mp hi), if_neg (Finset.mem_compl.mp hj)]
  rw [Finset.sum_congr rfl hin, Finset.sum_congr rfl hout, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  ring

/-- The character index vector (`0` outside `S`). -/
def idx (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) (α : Fin n → Bool) : Fin n → ZMod 2 :=
  fun i => if i ∈ S then ∑ j ∈ Sᶜ, (A i j + A j i) * bit (α j) else 0

/-- The `Bool` character index `y(α)`. -/
noncomputable def yb (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) (α : Fin n → Bool) :
    Fin n → Bool := fun i => decide (idx A S α i = 1)

/-- The cross term reorganizes to `∑ᵢ bit(zᵢ)·idxᵢ`. -/
theorem cross_eq (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) (z α : Fin n → Bool) :
    (∑ i ∈ S, ∑ j ∈ Sᶜ, A i j * bit (z i) * bit (α j))
       + (∑ i ∈ Sᶜ, ∑ j ∈ S, A i j * bit (α i) * bit (z j))
      = ∑ i, bit (z i) * idx A S α i := by
  classical
  rw [← Finset.sum_add_sum_compl S (f := fun i => bit (z i) * idx A S α i)]
  have h2 : (∑ i ∈ Sᶜ, bit (z i) * idx A S α i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [idx, Finset.mem_compl.mp hi]
  rw [h2, add_zero]
  have hidx : (∑ i ∈ S, bit (z i) * idx A S α i)
      = (∑ i ∈ S, ∑ j ∈ Sᶜ, A i j * bit (z i) * bit (α j))
        + (∑ i ∈ S, ∑ j ∈ Sᶜ, A j i * bit (z i) * bit (α j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    simp only [idx, if_pos hi, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcross2 : (∑ i ∈ Sᶜ, ∑ j ∈ S, A i j * bit (α i) * bit (z j))
      = (∑ i ∈ S, ∑ j ∈ Sᶜ, A j i * bit (z i) * bit (α j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hidx, hcross2]

theorem sgn_cross_eq_chi (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n))
    (z α : Fin n → Bool) :
    sgn (K := K) (∑ i, bit (z i) * idx A S α i) = chi (K := K) (yb A S α) z := by
  rw [sgn_sum]
  unfold chi yb
  apply Finset.prod_congr rfl
  intro i _
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (idx A S α i) with hi | hi <;>
    cases hz : z i <;> simp [sgn, bit, hi, hz]

/-- The within-`S` local sign (a `±1` function of `z`). -/
noncomputable def D (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) (z : Fin n → Bool) : K :=
  sgn (∑ i ∈ S, ∑ j ∈ S, A i j * bit (z i) * bit (z j))

/-- The within-`Sᶜ` constant. -/
noncomputable def cc (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) (α : Fin n → Bool) : K :=
  sgn (∑ i ∈ Sᶜ, ∑ j ∈ Sᶜ, A i j * bit (α i) * bit (α j))

/-- **The residual factorization.**  `residualOf S (QF (K := K) A) α = D · χ_{y(α)} · c(α)` — a local sign, a Walsh
character, and a constant. -/
theorem residual_factor (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) (α : Fin n → Bool) :
    residualOf S (QF (K := K) A) α = fun z => D A S z * chi (K := K) (yb A S α) z * cc A S α := by
  funext z
  show QF (K := K) A (fun i => if i ∈ S then z i else α i) = _
  unfold QF
  rw [qf_split, sgn_add, sgn_add, cross_eq, sgn_cross_eq_chi]
  rfl

/-- The set of distinct residual characters of `QF A` at cut `S`. -/
noncomputable def indexImage (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) :
    Finset (Fin n → Bool) := Finset.univ.image (yb A S)

/-- **The bond of the single function `QF A` across `S` is at least the number of distinct residual characters.**
Unlike the cut-local `BestPartitionBond`, this is the residual span of *one* function. -/
theorem residual_finrank_ge (A : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Finset (Fin n)) :
    (indexImage A S).card
      ≤ Module.finrank K (Submodule.span K (Set.range (residualOf S (QF (K := K) A)))) := by
  classical
  haveI : FiniteDimensional K ((Fin n → Bool) → K) := inferInstance
  have hex : ∀ t : (indexImage A S), ∃ α, yb A S α = t.val := by
    intro t
    have ht := t.property
    simp only [indexImage, Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨α, hα⟩ := ht
    exact ⟨α, hα⟩
  choose secα hsecα using hex
  set g : (indexImage A S) → ((Fin n → Bool) → K) := fun t => residualOf S (QF (K := K) A) (secα t) with hg
  have hgli : LinearIndependent K g := by
    rw [Fintype.linearIndependent_iff]
    intro lam hsum t0
    have hchi_li : LinearIndependent K (fun t : (indexImage A S) => chi (K := K) t.val) :=
      (chi_linearIndependent (K := K) (N := n)).comp Subtype.val Subtype.val_injective
    have hfactor : ∀ z, (∑ t, lam t • g t) z
        = D A S z * (∑ t, (lam t * cc A S (secα t)) • chi (K := K) t.val) z := by
      intro z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      have hgt := congrFun (residual_factor (K := K) A S (secα t)) z
      simp only [hg]
      rw [hgt, hsecα t]
      ring
    have hchi_zero : (∑ t, (lam t * cc A S (secα t)) • chi (K := K) t.val) = 0 := by
      funext z
      have hk := hfactor z
      rw [congrFun hsum z, Pi.zero_apply] at hk
      rcases mul_eq_zero.mp hk.symm with h | h
      · exact absurd h (sgn_ne_zero _)
      · simpa using h
    rw [Fintype.linearIndependent_iff] at hchi_li
    have hz := hchi_li (fun t => lam t * cc A S (secα t)) hchi_zero t0
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (sgn_ne_zero _)
  have hsub : Submodule.span K (Set.range g)
      ≤ Submodule.span K (Set.range (residualOf S (QF (K := K) A))) := by
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨secα t, rfl⟩
  calc (indexImage A S).card = Fintype.card (indexImage A S) := (Fintype.card_coe _).symm
    _ = Module.finrank K (Submodule.span K (Set.range g)) := (finrank_span_eq_card hgli).symm
    _ ≤ Module.finrank K (Submodule.span K (Set.range (residualOf S (QF (K := K) A)))) :=
        Submodule.finrank_mono hsub

end PallLean.Paper93.DeepMath.PathB.GlobalResidual

#print axioms PallLean.Paper93.DeepMath.PathB.GlobalResidual.residual_factor
#print axioms PallLean.Paper93.DeepMath.PathB.GlobalResidual.residual_finrank_ge
