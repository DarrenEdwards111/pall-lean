/-
  Paper93/PermutationInvariance.lean — Paper §9 Lemma 27
  =========================================================================

  Formalization of paper §9 Lemma 27 (Permutation-invariance within blocks):
  "If two canonical windows differ only by a permutation of interface
  identities within the same block partition, then [...] they contribute
  the same rank. Consequently, SPDP upper bounds depend only on the profile
  histogram h."

  Abstract combinatorial content: if a function `f : (Fin n → α) → β` is
  invariant under permutations acting within blocks of a partition, and in
  particular under all permutations (take the trivial single-block
  partition `block = Finset.univ`), then `f x` depends only on the multiset
  of values `x` attains — equivalently, on the fiber cardinalities
  `#{i : x i = a}` for each `a : α`.

  This is a standalone theorem: no external Paper93 dependencies.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace PallLean.Paper93

open Finset

universe u v

variable {α : Type u} {β : Type v}

/-- A function `f` on tuples is *block-permutation-invariant* on `block` if
permuting coordinates inside `block` (i.e. via a permutation fixing all
indices outside `block`) preserves `f`. -/
def IsBlockPermutationInvariant {n : ℕ} (f : (Fin n → α) → β)
    (block : Finset (Fin n)) : Prop :=
  ∀ (x : Fin n → α) (π : Equiv.Perm (Fin n)),
    (∀ i, i ∉ block → π i = i) → f (x ∘ π) = f x

/-! ### Reduction to full permutation invariance via `block = Finset.univ`. -/

lemma isBlockPermInvariant_univ_apply {n : ℕ}
    {f : (Fin n → α) → β}
    (h : IsBlockPermutationInvariant f (Finset.univ : Finset (Fin n)))
    (x : Fin n → α) (π : Equiv.Perm (Fin n)) :
    f (x ∘ π) = f x := by
  refine h x π ?_
  intro i hi
  exact (hi (Finset.mem_univ i)).elim

/-! ### Lift a permutation of `Fin n` to `Fin (n+1)` fixing the last index. -/

/-- Lift `σ : Equiv.Perm (Fin n)` to `Equiv.Perm (Fin (n+1))` fixing
`Fin.last n`. -/
private def liftPermLast {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n+1)) where
  toFun := fun i =>
    if h : i = Fin.last n then Fin.last n
    else Fin.castSucc (σ ⟨i.val, by
      rcases Nat.lt_succ_iff_lt_or_eq.mp i.isLt with hlt | heq
      · exact hlt
      · exfalso; exact h (Fin.ext heq)⟩)
  invFun := fun i =>
    if h : i = Fin.last n then Fin.last n
    else Fin.castSucc (σ.symm ⟨i.val, by
      rcases Nat.lt_succ_iff_lt_or_eq.mp i.isLt with hlt | heq
      · exact hlt
      · exfalso; exact h (Fin.ext heq)⟩)
  left_inv := by
    intro i
    by_cases hi : i = Fin.last n
    · subst hi; simp
    · simp only [hi, dif_neg, Fin.castSucc_ne_last, not_false_eq_true, dif_neg]
      apply Fin.ext
      show (σ.symm (σ ⟨i.val, _⟩)).val = i.val
      rw [σ.symm_apply_apply]
  right_inv := by
    intro i
    by_cases hi : i = Fin.last n
    · subst hi; simp
    · simp only [hi, dif_neg, Fin.castSucc_ne_last, not_false_eq_true, dif_neg]
      apply Fin.ext
      show (σ (σ.symm ⟨i.val, _⟩)).val = i.val
      rw [σ.apply_symm_apply]

private lemma liftPermLast_last {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    liftPermLast σ (Fin.last n) = Fin.last n := by
  show (if h : Fin.last n = Fin.last n then Fin.last n else _) = Fin.last n
  simp

private lemma liftPermLast_castSucc {n : ℕ} (σ : Equiv.Perm (Fin n))
    (k : Fin n) :
    liftPermLast σ k.castSucc = (σ k).castSucc := by
  show (if h : k.castSucc = Fin.last n then Fin.last n
        else Fin.castSucc (σ ⟨k.castSucc.val, _⟩)) = (σ k).castSucc
  rw [dif_neg (Fin.castSucc_ne_last k)]
  apply Fin.ext
  rfl

/-! ### Key combinatorial lemma: equal fiber cardinalities ⇒ related by a
    permutation. We work under `[DecidableEq α]`. -/

/-- If `x y : Fin n → α` have equal fiber cardinalities at every `a : α`,
then there exists a permutation `π` of `Fin n` such that `x ∘ π = y`. -/
theorem exists_perm_of_card_filter_eq {α : Type u} [DecidableEq α]
    {n : ℕ} (x y : Fin n → α)
    (hmulti : ∀ a : α,
        ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card
      = ((Finset.univ : Finset (Fin n)).filter (fun i => y i = a)).card) :
    ∃ π : Equiv.Perm (Fin n), x ∘ π = y := by
  induction n with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      funext i; exact i.elim0
  | succ n ih =>
      -- Step 1: Find `j : Fin (n+1)` with `x j = y (Fin.last n)`.
      set a0 : α := y (Fin.last n) with ha0def
      have hlast_mem :
          Fin.last n ∈ (Finset.univ : Finset (Fin (n+1))).filter
            (fun i => y i = a0) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        show y (Fin.last n) = a0
        rfl
      have hy_pos :
          0 < ((Finset.univ : Finset (Fin (n+1))).filter
                (fun i => y i = a0)).card :=
        Finset.card_pos.mpr ⟨_, hlast_mem⟩
      have hx_pos :
          0 < ((Finset.univ : Finset (Fin (n+1))).filter
                (fun i => x i = a0)).card := by
        rw [hmulti a0]; exact hy_pos
      obtain ⟨j, hj⟩ :
          ((Finset.univ : Finset (Fin (n+1))).filter
              (fun i => x i = a0)).Nonempty := Finset.card_pos.mp hx_pos
      have hxj : x j = a0 := (Finset.mem_filter.mp hj).2
      -- Step 2: Swap j and Fin.last n in x; call the result x'.
      let swp : Equiv.Perm (Fin (n+1)) := Equiv.swap j (Fin.last n)
      let x' : Fin (n+1) → α := x ∘ swp
      have hx'_last : x' (Fin.last n) = a0 := by
        show x (swp (Fin.last n)) = a0
        have hswp : swp (Fin.last n) = j :=
          Equiv.swap_apply_right (α := Fin (n+1)) j (Fin.last n)
        rw [hswp, hxj]
      -- Step 3: Restrict to the first n coordinates.
      let x'' : Fin n → α := fun i => x' i.castSucc
      let y'' : Fin n → α := fun i => y i.castSucc
      -- The fiber cardinalities of x'' and y'' match.
      have hmulti' : ∀ a : α,
          ((Finset.univ : Finset (Fin n)).filter (fun i => x'' i = a)).card
        = ((Finset.univ : Finset (Fin n)).filter
              (fun i => y'' i = a)).card := by
        intro a
        have hxx' :
            ((Finset.univ : Finset (Fin (n+1))).filter
                (fun i => x' i = a)).card
          = ((Finset.univ : Finset (Fin (n+1))).filter
                (fun i => x i = a)).card := by
          refine Finset.card_bij (fun i _ => swp i) ?_ ?_ ?_
          · intro i hi
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            have hi2 : x' i = a := (Finset.mem_filter.mp hi).2
            show x (swp i) = a
            exact hi2
          · intro i _ i' _ hii'
            exact swp.injective hii'
          · intro k hk
            refine ⟨swp.symm k, ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              have hk' : x k = a := (Finset.mem_filter.mp hk).2
              show x (swp (swp.symm k)) = a
              rw [Equiv.apply_symm_apply]
              exact hk'
            · exact Equiv.apply_symm_apply _ _
        -- Now split the (n+1)-fibers into castSucc-image plus last n piece.
        have split_x :
            ((Finset.univ : Finset (Fin (n+1))).filter
                (fun i => x' i = a)).card
          = ((Finset.univ : Finset (Fin n)).filter
                (fun i => x'' i = a)).card
            + (if x' (Fin.last n) = a then 1 else 0) := by
          have heq :
              ((Finset.univ : Finset (Fin (n+1))).filter
                  (fun i => x' i = a))
              = ((Finset.univ : Finset (Fin n)).filter
                    (fun i => x'' i = a)).image Fin.castSucc
                ∪ (if x' (Fin.last n) = a
                   then ({Fin.last n} : Finset (Fin (n+1)))
                   else (∅ : Finset (Fin (n+1)))) := by
            ext i
            refine Iff.intro ?_ ?_
            · intro hi
              have hi2 : x' i = a := (Finset.mem_filter.mp hi).2
              rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
              · refine Finset.mem_union.mpr (Or.inl ?_)
                refine Finset.mem_image.mpr ⟨k, ?_, rfl⟩
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                show x' k.castSucc = a
                exact hi2
              · refine Finset.mem_union.mpr (Or.inr ?_)
                have hcond : x' (Fin.last n) = a := hi2
                rw [if_pos hcond]
                exact Finset.mem_singleton.mpr rfl
            · intro hi
              rcases Finset.mem_union.mp hi with h1 | h2
              · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h1
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                have : x'' k = a := (Finset.mem_filter.mp hk).2
                show x' k.castSucc = a
                exact this
              · by_cases hlast : x' (Fin.last n) = a
                · rw [if_pos hlast] at h2
                  have : i = Fin.last n := Finset.mem_singleton.mp h2
                  subst this
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                  exact hlast
                · rw [if_neg hlast] at h2
                  exact absurd h2 (Finset.notMem_empty _)
          rw [heq]
          rw [Finset.card_union_of_disjoint]
          · rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
            by_cases h : x' (Fin.last n) = a
            · rw [if_pos h, if_pos h]
              simp
            · rw [if_neg h, if_neg h]
              simp
          · rw [Finset.disjoint_left]
            intro i hi1 hi2
            obtain ⟨k, _, hk_eq⟩ := Finset.mem_image.mp hi1
            by_cases hlast : x' (Fin.last n) = a
            · rw [if_pos hlast] at hi2
              have : i = Fin.last n := Finset.mem_singleton.mp hi2
              rw [this] at hk_eq
              exact (Fin.castSucc_lt_last k).ne hk_eq
            · rw [if_neg hlast] at hi2
              exact absurd hi2 (Finset.notMem_empty _)
        have split_y :
            ((Finset.univ : Finset (Fin (n+1))).filter
                (fun i => y i = a)).card
          = ((Finset.univ : Finset (Fin n)).filter
                (fun i => y'' i = a)).card
            + (if y (Fin.last n) = a then 1 else 0) := by
          have heq :
              ((Finset.univ : Finset (Fin (n+1))).filter
                  (fun i => y i = a))
              = ((Finset.univ : Finset (Fin n)).filter
                    (fun i => y'' i = a)).image Fin.castSucc
                ∪ (if y (Fin.last n) = a
                   then ({Fin.last n} : Finset (Fin (n+1)))
                   else (∅ : Finset (Fin (n+1)))) := by
            ext i
            refine Iff.intro ?_ ?_
            · intro hi
              have hi2 : y i = a := (Finset.mem_filter.mp hi).2
              rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
              · refine Finset.mem_union.mpr (Or.inl ?_)
                refine Finset.mem_image.mpr ⟨k, ?_, rfl⟩
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                show y k.castSucc = a
                exact hi2
              · refine Finset.mem_union.mpr (Or.inr ?_)
                have hcond : y (Fin.last n) = a := hi2
                rw [if_pos hcond]
                exact Finset.mem_singleton.mpr rfl
            · intro hi
              rcases Finset.mem_union.mp hi with h1 | h2
              · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h1
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                have : y'' k = a := (Finset.mem_filter.mp hk).2
                show y k.castSucc = a
                exact this
              · by_cases hlast : y (Fin.last n) = a
                · rw [if_pos hlast] at h2
                  have : i = Fin.last n := Finset.mem_singleton.mp h2
                  subst this
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                  exact hlast
                · rw [if_neg hlast] at h2
                  exact absurd h2 (Finset.notMem_empty _)
          rw [heq]
          rw [Finset.card_union_of_disjoint]
          · rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
            by_cases h : y (Fin.last n) = a
            · rw [if_pos h, if_pos h]
              simp
            · rw [if_neg h, if_neg h]
              simp
          · rw [Finset.disjoint_left]
            intro i hi1 hi2
            obtain ⟨k, _, hk_eq⟩ := Finset.mem_image.mp hi1
            by_cases hlast : y (Fin.last n) = a
            · rw [if_pos hlast] at hi2
              have : i = Fin.last n := Finset.mem_singleton.mp hi2
              rw [this] at hk_eq
              exact (Fin.castSucc_lt_last k).ne hk_eq
            · rw [if_neg hlast] at hi2
              exact absurd hi2 (Finset.notMem_empty _)
        -- The two "last" boundary contributions are equal.
        have hlast_eq :
            (if x' (Fin.last n) = a then (1:ℕ) else 0)
          = (if y (Fin.last n) = a then (1:ℕ) else 0) := by
          have hxy : x' (Fin.last n) = y (Fin.last n) := by
            rw [hx'_last]
          rw [hxy]
        have htotal :
            ((Finset.univ : Finset (Fin (n+1))).filter
                (fun i => x' i = a)).card
          = ((Finset.univ : Finset (Fin (n+1))).filter
                (fun i => y i = a)).card := by
          rw [hxx']
          exact hmulti a
        have chain :
            ((Finset.univ : Finset (Fin n)).filter
                (fun i => x'' i = a)).card
              + (if x' (Fin.last n) = a then (1:ℕ) else 0)
            = ((Finset.univ : Finset (Fin n)).filter
                (fun i => y'' i = a)).card
              + (if y (Fin.last n) = a then (1:ℕ) else 0) := by
          calc
            ((Finset.univ : Finset (Fin n)).filter
                (fun i => x'' i = a)).card
                + (if x' (Fin.last n) = a then (1:ℕ) else 0)
                = ((Finset.univ : Finset (Fin (n+1))).filter
                    (fun i => x' i = a)).card := split_x.symm
            _ = ((Finset.univ : Finset (Fin (n+1))).filter
                    (fun i => y i = a)).card := htotal
            _ = ((Finset.univ : Finset (Fin n)).filter
                    (fun i => y'' i = a)).card
                + (if y (Fin.last n) = a then (1:ℕ) else 0) := split_y
        rw [hlast_eq] at chain
        exact Nat.add_right_cancel chain
      -- Step 4: Apply IH.
      obtain ⟨σ, hσ⟩ := ih x'' y'' hmulti'
      -- Step 5: Build the final permutation.
      -- π := (liftPermLast σ).trans swp, so π i = swp (liftPermLast σ i).
      refine ⟨(liftPermLast σ).trans swp, ?_⟩
      funext i
      show x (swp (liftPermLast σ i)) = y i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
      · rw [liftPermLast_castSucc]
        -- Goal: x (swp (σ k).castSucc) = y k.castSucc
        have key : x'' (σ k) = y'' k := congrFun hσ k
        show x (swp (σ k).castSucc) = y k.castSucc
        have hredu : x (swp (σ k).castSucc) = x'' (σ k) := rfl
        rw [hredu, key]
      · rw [liftPermLast_last]
        -- Goal: x (swp (Fin.last n)) = y (Fin.last n)
        show x (swp (Fin.last n)) = y (Fin.last n)
        have hswp : swp (Fin.last n) = j :=
          Equiv.swap_apply_right (α := Fin (n+1)) j (Fin.last n)
        rw [hswp, hxj, ha0def]

/-! ### Main theorem: permutation-invariance ⇒ determined by fiber multiset. -/

/-- **Paper §9 Lemma 27 (Permutation-invariance within blocks).**

If `f : (Fin n → α) → β` is block-permutation-invariant for every block
(in particular, for the trivial single-block partition
`block = Finset.univ`), then `f` depends only on the multiset of values
of its input. Concretely: whenever two tuples `x, y : Fin n → α` satisfy
the fiber-cardinality equality `#{i : x i = a} = #{i : y i = a}` for
every `a : α`, then `f x = f y`. -/
theorem permInvariant_determined_by_multiset {α : Type u} [DecidableEq α]
    {n : ℕ} (f : (Fin n → α) → β)
    (hinv : ∀ block, IsBlockPermutationInvariant f block)
    (x y : Fin n → α)
    (hmulti : ∀ a : α,
        ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card
      = ((Finset.univ : Finset (Fin n)).filter (fun i => y i = a)).card) :
    f x = f y := by
  obtain ⟨π, hπ⟩ := exists_perm_of_card_filter_eq x y hmulti
  -- `f (x ∘ π) = f x` by full permutation invariance, and `x ∘ π = y`.
  have hfix := isBlockPermInvariant_univ_apply (hinv Finset.univ) x π
  rw [hπ] at hfix
  exact hfix.symm

end PallLean.Paper93
