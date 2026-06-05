import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukSubfunctionLB

/-!
# Nečiporuk concrete hard function: multi-block shared-data lookup (Stage 1: defs + per-block bound)

The explicit super-linear witness for `neciporuk_formula_lower_bound`: a XOR of `m` table-lookups into
a shared data region.  Variables `Fin nn` (`nn = m·b + 2^b`) split into `m` address blocks of size
`b` and a shared data region of `2^b` cells.  Block `k`'s `b` bits address a cell; `f` XORs the `m`
looked-up bits.

Per block `Sₖ` (the address bits of gadget `k`), fixing every *other* address to a reserved cell
`c₀` with `data[c₀] = false` makes those terms vanish, so the subfunction reads off exactly the data
cell the free address selects: `f(merge Sₖ (wit c) (mk t)) = t c`.  Distinct data tables `t` (with
`t c₀ = false`) therefore give distinct subfunctions, so `#blockResiduals(Sₖ) ≥ 2^{2^b − 1}`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace NecHard

open scoped BigOperators

variable (b m : ℕ)

/-- The data region size `= 2^b`, written as a Fintype cardinality (so the address equiv is free). -/
abbrev Dsize : ℕ := Fintype.card (Fin b → Bool)

/-- Variable count: `m` address blocks of `b` bits + `2^b` data cells. -/
abbrev nn : ℕ := m * b + Dsize b

/-- Address equiv: block-bit patterns ↔ data-cell indices (`Fintype.equivFin`, no explicit formula). -/
noncomputable def e : (Fin b → Bool) ≃ Fin (Dsize b) := Fintype.equivFin (Fin b → Bool)

variable {b m}

/-- The `j`-th address-bit variable of block `k`. -/
def addrBitVar (k : Fin m) (j : Fin b) : Fin (nn b m) :=
  ⟨k.val * b + j.val, by
    have h1 : (k.val + 1) * b ≤ m * b := by gcongr; omega
    have h2 : (k.val + 1) * b = k.val * b + b := by ring
    have h3 : j.val < b := j.isLt
    show k.val * b + j.val < m * b + Dsize b
    omega⟩

/-- The data variable for cell `c`. -/
def dataVar (c : Fin (Dsize b)) : Fin (nn b m) :=
  ⟨m * b + c.val, by
    have := c.isLt
    show m * b + c.val < m * b + Dsize b
    omega⟩

/-- The address-bit block of gadget `k` (a `Finset` of variables). -/
def blockS (k : Fin m) : Finset (Fin (nn b m)) :=
  Finset.univ.image (addrBitVar (m := m) k)

/-- The data cell addressed by block `k` under assignment `x`. -/
noncomputable def addr (x : Fin (nn b m) → Bool) (k : Fin m) : Fin (Dsize b) :=
  e b (fun j => x (addrBitVar k j))

/-- Bool → `ZMod 2`. -/
def enc : Bool → ZMod 2 := fun t => if t then 1 else 0

/-- **The hard function**: XOR (in `ZMod 2`) of the `m` looked-up data bits. -/
noncomputable def hardF (x : Fin (nn b m) → Bool) : Bool :=
  decide ((∑ k : Fin m, enc (x (dataVar (addr x k)))) = 1)

/-- The reserved cell every *other* address points at (the all-`false` address). -/
noncomputable def c0 : Fin (Dsize b) := e b (fun _ => false)

/-! ## Membership lemmas for the address block `blockS k` -/

theorem addrBitVar_mem (k : Fin m) (j : Fin b) : addrBitVar (m := m) k j ∈ blockS k :=
  Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem dataVar_not_mem (k : Fin m) (c : Fin (Dsize b)) :
    dataVar (m := m) c ∉ blockS (b := b) k := by
  simp only [blockS, Finset.mem_image, not_exists]
  rintro j ⟨-, h⟩
  have h1 : (addrBitVar (m := m) k j).val = (dataVar (m := m) (b := b) c).val := by rw [h]
  simp only [addrBitVar, dataVar] at h1
  have hkj : k.val * b + j.val < m * b := by
    have e1 : (k.val + 1) * b ≤ m * b := by gcongr; omega
    have e2 : (k.val + 1) * b = k.val * b + b := by ring
    have e3 : j.val < b := j.isLt
    omega
  omega

theorem addrBitVar_ne_mem {k k' : Fin m} (hne : k' ≠ k) (j : Fin b) :
    addrBitVar (m := m) k' j ∉ blockS (b := b) k := by
  simp only [blockS, Finset.mem_image, not_exists]
  rintro j' ⟨-, h⟩
  have h1 : (addrBitVar (m := m) k j').val = (addrBitVar (m := m) k' j).val := by rw [h]
  simp only [addrBitVar] at h1
  -- k*b + j' = k'*b + j with j',j < b forces k = k'
  have hj' : j'.val < b := j'.isLt
  have hj : j.val < b := j.isLt
  have : k.val = k'.val := by
    rcases lt_trichotomy k.val k'.val with hlt | heq | hgt
    · exfalso
      have hle : (k.val + 1) * b ≤ k'.val * b := by gcongr; omega
      have e2 : (k.val + 1) * b = k.val * b + b := by ring
      omega
    · exact heq
    · exfalso
      have hle : (k'.val + 1) * b ≤ k.val * b := by gcongr; omega
      have e2 : (k'.val + 1) * b = k'.val * b + b := by ring
      omega
  exact hne (Fin.ext this.symm)

/-! ## The witness (free block) and the parameter table (`mk`) -/

/-- The free-block input that drives block `k`'s address to cell `c`. -/
noncomputable def wit (k : Fin m) (c : Fin (Dsize b)) : Fin (nn b m) → Bool :=
  fun i => if h : k.val * b ≤ i.val ∧ i.val < k.val * b + b then
    (e b).symm c ⟨i.val - k.val * b, by omega⟩ else false

theorem wit_addrBitVar (k : Fin m) (c : Fin (Dsize b)) (j : Fin b) :
    wit k c (addrBitVar (m := m) k j) = (e b).symm c j := by
  have hj : j.val < b := j.isLt
  have hval : (addrBitVar (m := m) k j).val = k.val * b + j.val := rfl
  have harg : (addrBitVar (m := m) k j).val - k.val * b = j.val := by omega
  unfold wit
  rw [dif_pos (by omega)]
  exact congrArg _ (Fin.ext harg)

/-- The parameter assignment for table `t` (other blocks → reserved cell `c0`, data → `t`). -/
noncomputable def mkt (t : Fin (Dsize b) → Bool) : Fin (nn b m) → Bool :=
  fun i => if h : m * b ≤ i.val then t ⟨i.val - m * b, by
    have hlt : i.val < m * b + Dsize b := i.isLt
    omega⟩ else false

theorem mkt_dataVar (t : Fin (Dsize b) → Bool) (c : Fin (Dsize b)) :
    mkt (m := m) t (dataVar (m := m) c) = t c := by
  unfold mkt dataVar
  rw [dif_pos (by simp)]
  congr 1
  apply Fin.ext
  simp

theorem mkt_addrBitVar (t : Fin (Dsize b) → Bool) (k : Fin m) (j : Fin b) :
    mkt (m := m) t (addrBitVar (m := m) k j) = false := by
  have hkj : k.val * b + j.val < m * b := by
    have e1 : (k.val + 1) * b ≤ m * b := by gcongr; omega
    have e2 : (k.val + 1) * b = k.val * b + b := by ring
    have e3 : j.val < b := j.isLt
    omega
  have hlt : (addrBitVar (m := m) k j).val < m * b := by
    show k.val * b + j.val < m * b; omega
  unfold mkt
  rw [dif_neg (Nat.not_le.mpr hlt)]

/-! ## The key value lemma and the per-block subfunction lower bound -/

/-- **The subfunction reads the addressed cell.**  Driving block `k`'s address to `c` (via `wit`),
with every other block pointing at the reserved cell `c0` whose data bit is `false`, the function
returns exactly the data cell `t c`. -/
theorem hardF_merge (k : Fin m) (c : Fin (Dsize b)) (t : Fin (Dsize b) → Bool)
    (hc0 : t c0 = false) :
    hardF (fun i => if i ∈ blockS k then wit k c i else mkt t i) = t c := by
  set M : Fin (nn b m) → Bool := (fun i => if i ∈ blockS k then wit k c i else mkt t i) with hM
  have hmd : ∀ v : Fin (Dsize b), M (dataVar (m := m) v) = t v := by
    intro v; rw [hM]; simp only [if_neg (dataVar_not_mem k v)]; exact mkt_dataVar t v
  have haddr_self : addr M k = c := by
    unfold addr
    have he : (fun j => M (addrBitVar (m := m) k j)) = (e b).symm c := by
      funext j; rw [hM]; simp only [if_pos (addrBitVar_mem k j)]; exact wit_addrBitVar k c j
    rw [he, Equiv.apply_symm_apply]
  have haddr_other : ∀ k' : Fin m, k' ≠ k → addr M k' = c0 := by
    intro k' hk'
    unfold addr
    have he : (fun j => M (addrBitVar (m := m) k' j)) = (fun _ => false) := by
      funext j; rw [hM]; simp only [if_neg (addrBitVar_ne_mem hk' j)]; exact mkt_addrBitVar t k' j
    rw [he]; rfl
  have hsum : (∑ k' : Fin m, enc (M (dataVar (addr M k')))) = enc (t c) := by
    rw [Finset.sum_eq_single k
      (fun k' _ hk' => by rw [haddr_other k' hk', hmd, hc0]; rfl)
      (fun h => absurd (Finset.mem_univ k) h)]
    rw [haddr_self, hmd]
  unfold hardF
  rw [hsum]
  cases h : t c <;> simp [enc, h]

/-- **Per-block subfunction lower bound for the explicit function.**  For any formula `F` computing
`hardF`, the number of distinct subfunctions on the address block `Sₖ` is at least the number of data
tables with the reserved cell `false` — i.e. `2^{2^b − 1}`.  Distinct such tables give distinct
subfunctions (witnessed by driving the free address to the differing cell, `hardF_merge`). -/
theorem card_blockResiduals_hardF_ge (k : Fin m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    (Finset.univ.filter (fun t : Fin (Dsize b) → Bool => t c0 = false)).card
      ≤ (blockResiduals (blockS k) F).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun t => (fun x => BFormula.eval F (fun i => if i ∈ blockS k then x i else mkt t i)))
    ?_ ?_
  · -- maps into blockResiduals
    intro t _
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨mkt t, Finset.mem_univ _, rfl⟩)
  · -- injective on the filter
    intro t ht t' ht' hgt
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    funext c
    have hc : BFormula.eval F (fun i => if i ∈ blockS k then wit k c i else mkt t i)
            = BFormula.eval F (fun i => if i ∈ blockS k then wit k c i else mkt t' i) :=
      congrFun hgt (wit k c)
    rw [hF, hF, hardF_merge k c t ht, hardF_merge k c t' ht'] at hc
    exact hc

end NecHard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_merge
#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.card_blockResiduals_hardF_ge
