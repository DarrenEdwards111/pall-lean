import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Parity
import Mathlib.Data.Fintype.BigOperators

/-!
# Block-DT model, foundation 34: half the inputs have odd parity (branch only)

The combinatorial foundation of the *minterm* route to a parity lower bound (no switching lemma needed):
exactly `2^(n-1)` of the `2^n` Boolean inputs have odd parity.  Proved by the bit-flip involution
(flipping coordinate `0` swaps odd ↔ even parity, via `parity_flip`).

* `parity_true_card` — `|{x : parity x = true}| = 2^(n-1)` for `n ≥ 1`.

This is the `2^(n-1)` that lower-bounds DNF size for parity (the minterm argument): each true input forces
a distinct full-width term.  Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open DTree

variable {n : ℕ}

/-- **Exactly half the inputs have odd parity.**  `|{x : parity x = true}| = 2^(n-1)`. -/
theorem parity_true_card (hn : 1 ≤ n) :
    (Finset.univ.filter (fun x : Fin n → Bool => parity x = true)).card = 2 ^ (n - 1) := by
  classical
  set j₀ : Fin n := ⟨0, hn⟩ with hj₀
  set e : (Fin n → Bool) → (Fin n → Bool) := fun x => Function.update x j₀ (!x j₀) with he
  have einv : ∀ x, e (e x) = x := by
    intro x
    funext i
    by_cases hi : i = j₀
    · subst hi; simp [he, Function.update_self]
    · simp [he, Function.update_of_ne hi]
  have einj : Function.Injective e := fun a b hab => by
    have := congrArg e hab; rwa [einv, einv] at this
  have eparity : ∀ x, parity (e x) = !parity x := fun x => parity_flip x j₀
  -- the false-filter is the image of the true-filter under e
  have himg : (Finset.univ.filter (fun x : Fin n → Bool => parity x = false))
      = (Finset.univ.filter (fun x : Fin n → Bool => parity x = true)).image e := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      exact ⟨e x, by simp [eparity, hx], einv x⟩
    · rintro ⟨y, hy, rfl⟩
      simp [eparity, hy]
  have hcard_eq : (Finset.univ.filter (fun x : Fin n → Bool => parity x = false)).card
      = (Finset.univ.filter (fun x : Fin n → Bool => parity x = true)).card := by
    rw [himg, Finset.card_image_of_injective _ einj]
  -- the two filters partition univ
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Bool)))
    (fun x => parity x = true)
  have hnot : (Finset.univ.filter (fun x : Fin n → Bool => ¬ parity x = true))
      = (Finset.univ.filter (fun x : Fin n → Bool => parity x = false)) := by
    apply Finset.filter_congr
    intro x _
    simp [Bool.not_eq_true]
  rw [hnot, hcard_eq] at hsum
  -- univ.card = 2^n
  have huniv : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [huniv] at hsum
  -- 2 * card = 2^n, n ≥ 1
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    ring
  omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_true_card
