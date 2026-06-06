import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukCountingLemma

/-!
# Toward the optimal `n²/log n`: the subfunction-count multiplicativity recursion

The current `blockResiduals_card_le` charges `clog₂(|Tok n|) ≈ log n` bits per leaf (it serialises the
residual over the *full* `n`-variable alphabet, redundantly re-encoding variable identities that the
fixed formula `F` already determines).  That spurious `log n` factor is exactly why the formalised
Nečiporuk bound tops out at `N²/log²N` rather than the classic optimal `N²/log N`.

Reaching `N²/log N` requires a **constant** number of bits per block-leaf: `s_i ≤ C^{leavesIn(S_i)}`.
This file establishes the *rigorous, correct* foundation of that bound — the **multiplicativity** of the
block-subfunction count over formula structure:

* `card_blockResiduals_bin`  — `s(bin g a b) ≤ s(a)·s(b)`  (the pair of child-residuals determines the
  parent residual; the pairs live in the product).
* `card_blockResiduals_un`   — `s(un u t) ≤ s(t)`.
* `card_blockResiduals_lit_in` / `_lit_out` / `_cst` — leaves: `=1` for an `S`-literal or a constant,
  `≤2` for a non-`S` literal (its residual is a constant fixed by the outside assignment).

## What is rigorously proved vs. the remaining core (FLAGGED, not faked)

These lemmas are exact and composable.  Naively folding them bounds `s_i` by `2^{(# non-S leaves)}`,
which is the **wrong direction** (it is not in terms of `leavesIn(S_i)`), so it does **not** yet give
the constant-per-leaf bound.

The genuine Nečiporuk core — the step this file does **not** establish — is:
> collapse every *maximal subtree containing no `S_i`-leaf* to a single constant before counting.
> There are at most `leavesIn(S_i) + 1` such maximal subtrees, so `s_i ≤ 2^{leavesIn(S_i)+1}`.

That collapse interacts with constant-folding (`simplify`): the simplified shape of `restrict S α F`
**depends on `α`** (e.g. `a ∧ cst c` collapses to `cst 0` when `c = 0` but to `a` when `c = 1`), so the
"≤ leavesIn + 1 constant slots" count is not a clean structural induction.  I have **not** reduced it to
a rigorous Lean proof, and I am **not** asserting `s_i ≤ 2^{O(leavesIn)}` here.  This is the honest
frontier of the `n²/log n` improvement.
-/

namespace PallLean.Paper93.DeepMath.PathB

open BFormula

variable {n : ℕ}

/-- **Multiplicativity over a binary gate.**  The residual of `bin g a b` on block `S` is
`g` applied pointwise to the residuals of `a` and `b` under the *same* outside assignment, so the
parent residual is determined by the pair of child residuals — whence `s(bin) ≤ s(a)·s(b)`. -/
theorem card_blockResiduals_bin (S : Finset (Fin n)) (g : Bool → Bool → Bool) (a b : BFormula n) :
    (blockResiduals S (BFormula.bin g a b)).card
      ≤ (blockResiduals S a).card * (blockResiduals S b).card := by
  classical
  have hsub : blockResiduals S (BFormula.bin g a b) ⊆
      (blockResiduals S a ×ˢ blockResiduals S b).image
        (fun p => fun x => g (p.1 x) (p.2 x)) := by
    intro φ hφ
    simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hφ
    obtain ⟨α, hα⟩ := hφ
    rw [Finset.mem_image]
    refine ⟨(fun x => BFormula.eval a (fun i => if i ∈ S then x i else α i),
             fun x => BFormula.eval b (fun i => if i ∈ S then x i else α i)), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨?_, ?_⟩ <;>
        · simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨α, rfl⟩
    · rw [← hα]; funext x; simp only [BFormula.eval]
  calc (blockResiduals S (BFormula.bin g a b)).card
      ≤ ((blockResiduals S a ×ˢ blockResiduals S b).image _).card := Finset.card_le_card hsub
    _ ≤ (blockResiduals S a ×ˢ blockResiduals S b).card := Finset.card_image_le
    _ = (blockResiduals S a).card * (blockResiduals S b).card := Finset.card_product _ _

/-- **Monotone under a unary gate.**  `s(un u t) ≤ s(t)`. -/
theorem card_blockResiduals_un (S : Finset (Fin n)) (u : Bool → Bool) (t : BFormula n) :
    (blockResiduals S (BFormula.un u t)).card ≤ (blockResiduals S t).card := by
  classical
  have hsub : blockResiduals S (BFormula.un u t) ⊆
      (blockResiduals S t).image (fun φ => fun x => u (φ x)) := by
    intro φ hφ
    simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hφ
    obtain ⟨α, hα⟩ := hφ
    rw [Finset.mem_image]
    refine ⟨fun x => BFormula.eval t (fun i => if i ∈ S then x i else α i), ?_, ?_⟩
    · simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨α, rfl⟩
    · rw [← hα]; funext x; simp only [BFormula.eval]
  calc (blockResiduals S (BFormula.un u t)).card
      ≤ ((blockResiduals S t).image _).card := Finset.card_le_card hsub
    _ ≤ (blockResiduals S t).card := Finset.card_image_le

/-- **`S`-literal leaf.**  An `S`-variable literal's residual is independent of the outside
assignment, so there is exactly one residual. -/
theorem card_blockResiduals_lit_in (S : Finset (Fin n)) {i : Fin n} (hi : i ∈ S) (b : Bool) :
    (blockResiduals S (BFormula.lit i b)).card ≤ 1 := by
  classical
  have hsub : blockResiduals S (BFormula.lit i b) ⊆
      {fun x : Fin n → Bool => cond b (x i) (!(x i))} := by
    intro φ hφ
    simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hφ
    obtain ⟨α, hα⟩ := hφ
    simp only [Finset.mem_singleton]
    rw [← hα]; funext x; simp only [BFormula.eval, if_pos hi]
  calc (blockResiduals S (BFormula.lit i b)).card
      ≤ ({fun x : Fin n → Bool => cond b (x i) (!(x i))} : Finset _).card :=
        Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-- **Non-`S` literal leaf.**  Its residual is the constant `cond b (α i) (!(α i))`, determined by the
single outside bit `α i`, so there are at most two residuals. -/
theorem card_blockResiduals_lit_out (S : Finset (Fin n)) {i : Fin n} (hi : i ∉ S) (b : Bool) :
    (blockResiduals S (BFormula.lit i b)).card ≤ 2 := by
  classical
  have hsub : blockResiduals S (BFormula.lit i b) ⊆
      (Finset.univ : Finset Bool).image (fun v => (fun _ : Fin n → Bool => cond b v (!v))) := by
    intro φ hφ
    simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hφ
    obtain ⟨α, hα⟩ := hφ
    rw [Finset.mem_image]
    refine ⟨α i, Finset.mem_univ _, ?_⟩
    rw [← hα]; funext x; simp only [BFormula.eval, if_neg hi]
  calc (blockResiduals S (BFormula.lit i b)).card
      ≤ ((Finset.univ : Finset Bool).image _).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset Bool).card := Finset.card_image_le
    _ = 2 := by simp

/-- **Constant leaf.**  Exactly one residual (the constant itself). -/
theorem card_blockResiduals_cst (S : Finset (Fin n)) (c : Bool) :
    (blockResiduals S (BFormula.cst c)).card ≤ 1 := by
  classical
  have hsub : blockResiduals S (BFormula.cst c) ⊆ {fun _ : Fin n → Bool => c} := by
    intro φ hφ
    simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hφ
    obtain ⟨α, hα⟩ := hφ
    simp only [Finset.mem_singleton]
    rw [← hα]; funext x; simp only [BFormula.eval]
  calc (blockResiduals S (BFormula.cst c)).card
      ≤ ({fun _ : Fin n → Bool => c} : Finset _).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.card_blockResiduals_bin
#print axioms PallLean.Paper93.DeepMath.PathB.card_blockResiduals_un
#print axioms PallLean.Paper93.DeepMath.PathB.card_blockResiduals_lit_out
