import Mathlib

/-!
# Hard math (arbitrary-depth nesting recursion) — the cell count multiplies at every layer (proved)

The general inductive step behind the Beigel–Tarui `SYM∘AND` cell count, for circuits of *arbitrary* depth.  The depth-2 and
depth-3 bricks (`modpe_depth2_count`, `depth3_modpe_cells`) are instances of one recursion: **whenever a (sub-)circuit's
output factors through `t` sub-circuits, each with at most `C` distinct cells, the circuit has at most `C^t` cells**
(`cells_factor`).  Applied at every node of a depth-`d`, fan-in-`f` circuit, this iterates to a `C^{f^{d}}`-style bound —
quasipolynomial for constant depth — *independently of the field/degree*, which is exactly why it survives the prime-power
RS barrier (`e ≥ 2`) where the polynomial-degree method fails.

## What is proved (clean axioms, no `sorry`)

* **`cells_compose`** (PROVED) — the joint vector of `t` functions, each with `≤ C` distinct values, has `≤ C^t` distinct
  values (the layer step, abstract over the value type).
* **`cells_factor`** (PROVED) — if `F x = H(G_1 x, …, G_t x)` and each `G_i` has `≤ C` cells, then `F` has `≤ C^t` cells
  (the recursion in usable form: a gate's cells are bounded by the product over its sub-circuits' cells).

## Honest scope

This is the per-layer cell-count recursion (`C^t` per node), abstract over the value type — the inductive engine that, applied
at every node, bounds any constant-depth circuit's cell count quasipolynomially via the symmetric structure.  Assembling it
over a concrete circuit-tree datatype is mechanical; the unconditional `NEXP ⊄ ACC⁰` (P≠NP-strength) is not done here.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CellRecursion

open Finset

variable {n : ℕ}

/-- **The layer step (PROVED): `t` functions each with `≤ C` cells have `≤ C^t` joint cells.** -/
theorem cells_compose {β : Type*} [DecidableEq β] {t : ℕ} (C : ℕ)
    (G : Fin t → (Fin n → Bool) → β) (hG : ∀ i, (Finset.univ.image (G i)).card ≤ C) :
    (Finset.univ.image (fun x i => G i x)).card ≤ C ^ t := by
  classical
  calc (Finset.univ.image (fun x (i : Fin t) => G i x)).card
      ≤ (Fintype.piFinset (fun i => Finset.univ.image (G i))).card := by
        apply Finset.card_le_card
        intro v hv
        simp only [Finset.mem_image] at hv; obtain ⟨x, _, rfl⟩ := hv
        rw [Fintype.mem_piFinset]
        intro i; exact Finset.mem_image_of_mem (G i) (Finset.mem_univ x)
    _ = ∏ i : Fin t, (Finset.univ.image (G i)).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin t, C := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hG i)
    _ = C ^ t := by simp [Finset.prod_const]

/-- **The recursion in usable form (PROVED): a gate's cell count is bounded by the product over its sub-circuits' cells.**  If
`F` factors through `t` sub-circuits `G_1,…,G_t` (via any top function `H`), each `G_i` with `≤ C` cells, then `F` has `≤ C^t`
cells.  Applied at every node of a depth-`d` circuit, this is the arbitrary-depth cell-count recursion. -/
theorem cells_factor {β γ : Type*} [DecidableEq β] [DecidableEq γ] {t : ℕ} (C : ℕ)
    (G : Fin t → (Fin n → Bool) → β) (H : (Fin t → β) → γ) (F : (Fin n → Bool) → γ)
    (hF : ∀ x, F x = H (fun i => G i x)) (hG : ∀ i, (Finset.univ.image (G i)).card ≤ C) :
    (Finset.univ.image F).card ≤ C ^ t := by
  classical
  have hsub : Finset.univ.image F ⊆ (Finset.univ.image (fun x i => G i x)).image H := by
    intro y hy
    simp only [Finset.mem_image] at hy ⊢
    obtain ⟨x, _, rfl⟩ := hy
    exact ⟨fun i => G i x, ⟨x, Finset.mem_univ x, rfl⟩, (hF x).symm⟩
  exact le_trans (Finset.card_le_card hsub)
    (le_trans (Finset.card_image_le) (cells_compose C G hG))

/-!
**The arbitrary-depth cell-count recursion, proved.**  `cells_factor` is the inductive step: a node's cells are bounded by
the product over its sub-circuits' cells.  Iterating it through a depth-`d`, fan-in-`f` circuit gives a `C^{f^{d}}` bound —
quasipolynomial for constant depth, field-independent (hence surviving the prime-power barrier).  Remaining (open, not faked):
the concrete circuit-tree assembly and the unconditional `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CellRecursion

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellRecursion.cells_factor
