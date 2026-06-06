import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukLeafFactor

/-!
# The spine-path contraction (algebraic form): post-composition closure is pass-through invariant

The skeleton route failed because gate-chains have unboundedly many `S`-free subtrees, yet the residual
count stays small — the gates *collapse* them.  The algebraic capture of that collapse is the
**post-composition closure**
  `Qset S F := { x ↦ h (eval F (mergeₛ x α)) : h : Bool → Bool, α }`,
i.e. all block residuals of `F` post-composed with every `Bool → Bool` function.  Since `Bool → Bool`
is a 4-element *monoid* under composition, `Qset` does not grow along **pass-through** nodes — and a
gate-chain is exactly a path of pass-through nodes.  This is the "contract each maximal degree-2 spine
path to one of the 4 edge-functions" step, done algebraically.

Proved here (all rigorous):
* `leavesIn_zero_indep` — an `S`-free subformula's value is independent of the block input.
* `blockResiduals_subset_Qset` — `s_i ≤ |Qset|` (take `h = id`).
* `Qset_un_subset` — `Qset (un u t) ⊆ Qset t`           (pass through a unary gate: `h ↦ h ∘ u`).
* `Qset_bin_left_free` / `Qset_bin_right_free` — `leavesIn S a = 0 ⇒ Qset (bin g a b) ⊆ Qset b`
  (pass through a binary gate whose other child is `S`-free: `h ↦ (v ↦ h (g c v))`, `c` the frozen
  `S`-free value).  **This is the chain collapse**: no growth along the spine path.
* `Qset_card_le_two_of_leavesIn_zero` — base of a contracted path: an `S`-free formula has `|Qset| ≤ 2`.

## What remains (FLAGGED, not faked)

The contraction handles **pass-through** (degree-2) nodes.  The **branching** case — `bin g a b` with
*both* children reading `S` — genuinely combines two channels: `|Qset (bin g a b)| ≤ 4·|Qset a|·|Qset b|`
(not proved here).  Combining the contraction (this file) with that branching bound under the invariant
`|Qset F| ≤ 4^{2·leavesIn − 1}` (for `leavesIn ≥ 1`) closes `s_i ≤ 16^{leavesIn}`, hence `N²/log N`.
That branching bound + the inductive assembly are the remaining work; the headline stays `N²/log²N`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open BFormula

variable {n : ℕ}

/-- An `S`-free subformula computes a value independent of the block input. -/
theorem leavesIn_zero_indep {S : Finset (Fin n)} :
    ∀ (G : BFormula n), BFormula.leavesIn S G = 0 → ∀ (z x x' : Fin n → Bool),
      BFormula.eval G (fun i => if i ∈ S then x i else z i)
        = BFormula.eval G (fun i => if i ∈ S then x' i else z i)
  | BFormula.lit i b, h, z, x, x' => by
      by_cases hi : i ∈ S
      · simp [BFormula.leavesIn, if_pos hi] at h
      · simp [BFormula.eval, if_neg hi]
  | BFormula.cst c, _, _, _, _ => rfl
  | BFormula.un u t, h, z, x, x' => by
      simp only [BFormula.leavesIn] at h
      simp only [BFormula.eval, leavesIn_zero_indep t h z x x']
  | BFormula.bin g a b, h, z, x, x' => by
      simp only [BFormula.leavesIn] at h
      have ha : BFormula.leavesIn S a = 0 := by omega
      have hb : BFormula.leavesIn S b = 0 := by omega
      simp only [BFormula.eval, leavesIn_zero_indep a ha z x x',
        leavesIn_zero_indep b hb z x x']

/-- The **post-composition closure** of the block residuals of `F`: every residual, composed with every
`Bool → Bool` function. -/
noncomputable def Qset (S : Finset (Fin n)) (F : BFormula n) : Finset ((Fin n → Bool) → Bool) := by
  classical
  exact Finset.image
    (fun p : (Bool → Bool) × (Fin n → Bool) =>
      fun x => p.1 (BFormula.eval F (fun i => if i ∈ S then x i else p.2 i)))
    Finset.univ

/-- `s_i ≤ |Qset|` (residuals are the `h = id` slice). -/
theorem blockResiduals_subset_Qset (S : Finset (Fin n)) (F : BFormula n) :
    blockResiduals S F ⊆ Qset S F := by
  classical
  intro φ hφ
  simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hφ
  obtain ⟨α, hφ⟩ := hφ
  simp only [Qset, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨(id, α), by rw [← hφ]; funext x; rfl⟩

/-- **Contraction through a unary gate.**  `Qset (un u t) ⊆ Qset t` via `h ↦ h ∘ u`. -/
theorem Qset_un_subset (S : Finset (Fin n)) (u : Bool → Bool) (t : BFormula n) :
    Qset S (BFormula.un u t) ⊆ Qset S t := by
  classical
  intro ψ hψ
  simp only [Qset, Finset.mem_image, Finset.mem_univ, true_and] at hψ ⊢
  obtain ⟨⟨h, α⟩, hψ⟩ := hψ
  exact ⟨(h ∘ u, α), by rw [← hψ]; funext x; simp only [BFormula.eval, Function.comp]⟩

/-- **Contraction through a binary gate with an `S`-free left child** — the chain collapse.  The
`S`-free child freezes to a constant `c`, so the gate acts as a single `Bool → Bool` function
`v ↦ h (g c v)`, and `Qset (bin g a b) ⊆ Qset b`. -/
theorem Qset_bin_left_free (S : Finset (Fin n)) (g : Bool → Bool → Bool) (a b : BFormula n)
    (ha : BFormula.leavesIn S a = 0) : Qset S (BFormula.bin g a b) ⊆ Qset S b := by
  classical
  intro ψ hψ
  simp only [Qset, Finset.mem_image, Finset.mem_univ, true_and] at hψ ⊢
  obtain ⟨⟨h, α⟩, hψ⟩ := hψ
  refine ⟨(fun v => h (g (BFormula.eval a (fun i => if i ∈ S then false else α i)) v), α), ?_⟩
  rw [← hψ]; funext x
  have key : BFormula.eval a (fun i => if i ∈ S then false else α i)
           = BFormula.eval a (fun i => if i ∈ S then x i else α i) :=
    leavesIn_zero_indep a ha α (fun _ => false) x
  simp only [BFormula.eval, key]

/-- **Contraction through a binary gate with an `S`-free right child.** -/
theorem Qset_bin_right_free (S : Finset (Fin n)) (g : Bool → Bool → Bool) (a b : BFormula n)
    (hb : BFormula.leavesIn S b = 0) : Qset S (BFormula.bin g a b) ⊆ Qset S a := by
  classical
  intro ψ hψ
  simp only [Qset, Finset.mem_image, Finset.mem_univ, true_and] at hψ ⊢
  obtain ⟨⟨h, α⟩, hψ⟩ := hψ
  refine ⟨(fun v => h (g v (BFormula.eval b (fun i => if i ∈ S then false else α i))), α), ?_⟩
  rw [← hψ]; funext x
  have key : BFormula.eval b (fun i => if i ∈ S then false else α i)
           = BFormula.eval b (fun i => if i ∈ S then x i else α i) :=
    leavesIn_zero_indep b hb α (fun _ => false) x
  simp only [BFormula.eval, key]

/-- **Base of a contracted path.**  An `S`-free formula has at most two closure elements (constants). -/
theorem Qset_card_le_two_of_leavesIn_zero {S : Finset (Fin n)} {F : BFormula n}
    (h : BFormula.leavesIn S F = 0) : (Qset S F).card ≤ 2 := by
  classical
  have hconst : ∀ ψ ∈ Qset S F, ∀ x y, ψ x = ψ y := by
    intro ψ hψ x y
    simp only [Qset, Finset.mem_image, Finset.mem_univ, true_and] at hψ
    obtain ⟨⟨h', α⟩, rfl⟩ := hψ
    show h' (BFormula.eval F (fun i => if i ∈ S then x i else α i))
       = h' (BFormula.eval F (fun i => if i ∈ S then y i else α i))
    rw [leavesIn_zero_indep F h α x y]
  have hinj : Set.InjOn (fun ψ : (Fin n → Bool) → Bool => ψ (fun _ => false)) (Qset S F : Set _) := by
    intro ψ hψ χ hχ hpq
    simp only [Finset.mem_coe] at hψ hχ
    funext x
    rw [hconst ψ hψ x (fun _ => false), hconst χ hχ x (fun _ => false)]; exact hpq
  calc (Qset S F).card
      = ((Qset S F).image (fun ψ => ψ (fun _ => false))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset Bool).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := by decide

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Qset_bin_left_free
#print axioms PallLean.Paper93.DeepMath.PathB.Qset_card_le_two_of_leavesIn_zero
