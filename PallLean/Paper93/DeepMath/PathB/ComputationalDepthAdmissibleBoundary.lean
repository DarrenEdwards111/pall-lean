import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundaryHardFail

/-!
# The general admissible boundary: `Permₙ` under a `k×k`-block boundary equals the block `Permₖ`

`ComputationalDepthBoundaryHardFail.lean` showed the permanent is *fragile* under a **destructive** boundary (zeroing a
row kills it), so `BoundarySPDP` over *arbitrary* boundaries is a robustness, not a hardness, invariant — and that the
correct N-Frame object is `BoundarySPDP` over **admissible** (minor-preserving) boundaries.  The diagonal boundary was
the `k = n` warm-up.  This file proves the general minor-preservation statement the refinement demanded:

  `Permₙ` restricted by an admissible `k×k`-block boundary  =  `scalar · Permₖ`   (here `scalar = 1`).

## The construction

For an embedding `e : Fin k ↪ Fin n` (the visible `k×k` minor / block `B = range e`), the **block boundary**
`blockBoundary e` keeps `X_{i,j}` visible when both `i,j ∈ B`, and off the block fixes `1` on the diagonal, `0` off it —
an admissible, minor-preserving observer context (it does *not* destroy the block's witness structure).

  `permPoly_blockBoundary_eq` — `aeval (blockBoundary e) Permₙ = subPermPoly e`, where
        `subPermPoly e = ∑_{τ∈Sₖ} ∏_{a} X_{e a, e(τ a)}` is the permanent of the `k×k` submatrix on the block.
  `subPermPoly_eq_rename` — `subPermPoly e = aeval (X_{a,b} ↦ X_{e a, e b}) (Permₖ)`, i.e. it is literally `Permₖ`
        reindexed into the block — a genuine `Permₙ ↦ Permₖ` reduction.
  `permPoly_ne_zero` / `subPermPoly_ne_zero` — the permanent (and its block reduction) is nonzero (evaluate at the
        identity matrix: `perm(I) = 1`), so the permanent **survives** the admissible block boundary
        (`permPoly_blockBoundary_ne_zero`).

The proof is the honest combinatorics: only permutations that map the block `B` into itself survive the boundary (a
permutation crossing out of `B` hits a fixed `0`), and those are exactly the `extendDomain`s of `Sₖ` (Mathlib's
`Equiv.Perm.extendDomain`).  The surviving sum reindexes bijectively onto `subPermPoly e` via `Finset.sum_bij`.

## Honest status

This is a genuine minor-preservation theorem: the hardest object we have (the `VNP`-complete permanent) is *robust*
under admissible boundaries, reducing functorially `Permₙ ↦ Permₖ` — exactly the structure a hardness-aimed invariant
needs, and what *destructive* boundaries destroy.  It is **not** a hardness lower bound: making a hard target
admissibly-robust *and* proving its SPDP rank stays high under every admissible boundary is the barriered `A3`
hard-survival.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial

variable {k n : ℕ} {F : Type*} [Field F]

/-- The `k×k`-block admissible boundary for an embedding `e : Fin k ↪ Fin n`: keep visible the entries `(i,j)` with
both `i,j` in the block `B = range e`; off the block, fix to `1` on the diagonal and `0` off it (an admissible,
minor-preserving context, in contrast to the destructive row-zeroing of `permPoly_restrictRow_zero`). -/
noncomputable def blockBoundary (e : Fin k ↪ Fin n) :
    Fin n × Fin n → MvPolynomial (Fin n × Fin n) F :=
  fun p => if p.1 ∈ Finset.univ.map e ∧ p.2 ∈ Finset.univ.map e then X p
           else if p.1 = p.2 then 1 else 0

/-- The `k×k` sub-permanent on the block `e` — a genuine `Permₖ` in the block variables. -/
noncomputable def subPermPoly (e : Fin k ↪ Fin n) : MvPolynomial (Fin n × Fin n) F :=
  ∑ τ : Equiv.Perm (Fin k), ∏ a, X (e a, e (τ a))

/-- `subPermPoly e` is literally `Permₖ` reindexed into the block `e` — making the `Permₙ ↦ Permₖ` reduction explicit. -/
theorem subPermPoly_eq_rename (e : Fin k ↪ Fin n) :
    subPermPoly (F := F) e
      = aeval (fun p : Fin k × Fin k => X (e p.1, e p.2)) (permPoly k F) := by
  unfold subPermPoly permPoly
  rw [map_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [map_prod]
  exact Finset.prod_congr rfl (fun a _ => by simp)

/-- **The general admissible-boundary reduction (proved).**  `Permₙ` under the `k×k`-block admissible boundary equals
the block sub-permanent `subPermPoly e = Permₖ`.  Only permutations mapping the block `B = range e` into itself survive
the boundary; these are exactly the `extendDomain`s of `Sₖ`, and the surviving sum reindexes bijectively onto `Permₖ`. -/
theorem permPoly_blockBoundary_eq (e : Fin k ↪ Fin n) :
    aeval (blockBoundary e) (permPoly n F) = subPermPoly (F := F) e := by
  classical
  letI : DecidablePred (· ∈ Set.range e) :=
    fun x => decidable_of_iff (x ∈ Finset.univ.map e) (by simp [Finset.mem_map])
  set fe : Fin k ≃ Set.range e := Equiv.ofInjective e e.injective with hfe
  have hB : ∀ i : Fin n, i ∈ Finset.univ.map e ↔ i ∈ Set.range e := by
    intro i; simp [Finset.mem_map, Set.mem_range]
  have hcoe : ∀ a : Fin k, (fe a : Fin n) = e a := by intro a; rw [hfe]; simp [Equiv.ofInjective_apply]
  have hed_img : ∀ (τ : Equiv.Perm (Fin k)) (a : Fin k),
      (τ.extendDomain fe) (e a) = e (τ a) := by
    intro τ a
    have h1 : (e a : Fin n) = ↑(fe a) := (hcoe a).symm
    rw [h1, Equiv.Perm.extendDomain_apply_image, hcoe]
  have hed_fix : ∀ (τ : Equiv.Perm (Fin k)) (i : Fin n),
      i ∉ Finset.univ.map e → (τ.extendDomain fe) i = i := by
    intro τ i hi
    exact Equiv.Perm.extendDomain_apply_not_subtype τ fe (fun h => hi ((hB i).mpr h))
  -- Step 1: expand aeval over the permanent's sum of products
  have hLHS : aeval (blockBoundary e) (permPoly n F)
      = ∑ σ : Equiv.Perm (Fin n), ∏ i, blockBoundary (F := F) e (i, σ i) := by
    unfold permPoly
    rw [map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [map_prod]; refine Finset.prod_congr rfl (fun i _ => by rw [aeval_X])
  rw [hLHS]
  -- Step 2: cut the sum to the survivors (permutations fixing the complement of the block)
  set S : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun σ => ∀ i, i ∉ Finset.univ.map e → σ i = i) with hS
  have hcut : ∑ σ : Equiv.Perm (Fin n), ∏ i, blockBoundary (F := F) e (i, σ i)
      = ∑ σ ∈ S, ∏ i, blockBoundary (F := F) e (i, σ i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro σ _ hσS
    rw [hS, Finset.mem_filter] at hσS
    push_neg at hσS
    obtain ⟨i, hi, hne⟩ := hσS (Finset.mem_univ σ)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold blockBoundary
    simp only
    rw [if_neg (fun h => hi h.1), if_neg (Ne.symm hne)]
  rw [hcut]
  -- Step 3: the surviving sum reindexes bijectively onto Permₖ via extendDomain
  unfold subPermPoly
  symm
  apply Finset.sum_bij (fun τ _ => τ.extendDomain fe)
  · -- forward map lands in the survivors
    intro τ _
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i hi => hed_fix τ i hi⟩
  · -- injective (extendDomain is an injective hom)
    intro τ₁ _ τ₂ _ h
    exact Equiv.Perm.extendDomainHom_injective fe h
  · -- surjective onto the survivors: restrict a survivor back to a permutation of the block
    intro σ hσ
    rw [hS, Finset.mem_filter] at hσ
    obtain ⟨_, hfix⟩ := hσ
    have hp : ∀ x : Fin n, x ∈ Set.range e ↔ (σ x) ∈ Set.range e := by
      intro x
      constructor
      · intro hx
        by_contra hσx
        have : σ x ∉ Finset.univ.map e := fun h => hσx ((hB _).mp h)
        have h2 := hfix (σ x) this
        have h3 : σ x = x := σ.injective h2
        rw [h3] at hσx; exact hσx hx
      · intro hσx
        by_contra hx
        have : x ∉ Finset.univ.map e := fun h => hx ((hB _).mp h)
        have := hfix x this
        rw [this] at hσx
        exact hx hσx
    set τ : Equiv.Perm (Fin k) :=
      fe.symm.permCongr (σ.subtypePerm (fun x => (hp x).symm)) with hτdef
    refine ⟨τ, Finset.mem_univ _, ?_⟩
    ext i
    by_cases hi : i ∈ Finset.univ.map e
    · obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
      rw [hed_img, hτdef, Equiv.permCongr_apply, Equiv.symm_symm, ← hcoe,
          Equiv.apply_symm_apply, Equiv.Perm.subtypePerm_apply]
      simp [hcoe]
    · rw [hed_fix τ i hi, hfix i hi]
  · -- value equality: the surviving product on the block is the block monomial
    intro τ _
    rw [← Finset.prod_mul_prod_compl (Finset.univ.map e)
          (fun i => blockBoundary (F := F) e (i, (τ.extendDomain fe) i))]
    have hcompl : ∏ i ∈ (Finset.univ.map e)ᶜ,
        blockBoundary (F := F) e (i, (τ.extendDomain fe) i) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      rw [Finset.mem_compl] at hi
      rw [hed_fix τ i hi]
      unfold blockBoundary
      simp only
      rw [if_neg (fun h => hi h.1)]; simp
    have hmap : ∏ i ∈ Finset.univ.map e,
        blockBoundary (F := F) e (i, (τ.extendDomain fe) i) = ∏ a, X (e a, e (τ a)) := by
      rw [Finset.prod_map]
      refine Finset.prod_congr rfl (fun a _ => ?_)
      rw [hed_img]
      unfold blockBoundary
      simp only
      rw [if_pos ⟨Finset.mem_map_of_mem e (Finset.mem_univ a),
                  Finset.mem_map_of_mem e (Finset.mem_univ (τ a))⟩]
    rw [hcompl, hmap, mul_one]

/-- **The permanent is nonzero (proved).**  Evaluate at the identity matrix `X_{i,j} ↦ [i = j]`: only `σ = id` survives,
so `perm(I) = 1 ≠ 0`.  In particular `Permₙ ≠ 0`. -/
theorem permPoly_ne_zero [Nontrivial F] : permPoly n F ≠ 0 := by
  intro h
  have hev : aeval (fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0) (permPoly n F) = 1 := by
    unfold permPoly
    rw [map_sum, Finset.sum_eq_single (Equiv.refl (Fin n))]
    · rw [map_prod]; simp
    · intro σ _ hσ
      rw [map_prod]
      obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
        by_contra hc; push_neg at hc; exact hσ (Equiv.ext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi])
    · intro hc; exact absurd (Finset.mem_univ _) hc
  rw [h, map_zero] at hev
  exact one_ne_zero hev.symm

/-- **The block sub-permanent is nonzero (proved).**  Same identity-matrix evaluation: only `τ = id` survives (`e`
injective), so `subPermPoly e` evaluates to `1`. -/
theorem subPermPoly_ne_zero [Nontrivial F] (e : Fin k ↪ Fin n) : subPermPoly (F := F) e ≠ 0 := by
  intro h
  have hev : aeval (fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0) (subPermPoly (F := F) e) = 1 := by
    unfold subPermPoly
    rw [map_sum, Finset.sum_eq_single (Equiv.refl (Fin k))]
    · rw [map_prod]; simp
    · intro τ _ hτ
      rw [map_prod]
      obtain ⟨a, ha⟩ : ∃ a, τ a ≠ a := by
        by_contra hc; push_neg at hc; exact hτ (Equiv.ext hc)
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      simp only [aeval_X]
      rw [if_neg (fun hh => ha (e.injective hh).symm)]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  rw [h, map_zero] at hev
  exact one_ne_zero hev.symm

/-- **The permanent survives the admissible block boundary (proved).**  Unlike the destructive row-zeroing
(`permPoly_restrictRow_zero → 0`), the `k×k`-block admissible boundary reduces `Permₙ` to the nonzero block `Permₖ`. -/
theorem permPoly_blockBoundary_ne_zero [Nontrivial F] (e : Fin k ↪ Fin n) :
    aeval (blockBoundary (F := F) e) (permPoly n F) ≠ 0 := by
  rw [permPoly_blockBoundary_eq]; exact subPermPoly_ne_zero e

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.permPoly_blockBoundary_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.subPermPoly_eq_rename
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.permPoly_blockBoundary_ne_zero
