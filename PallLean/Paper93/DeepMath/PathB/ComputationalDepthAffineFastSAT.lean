import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# Another P-side rung: affine (XOR) SAT — a single linear equation over `F₂`

A distinct branch of the fast-SAT ladder: the **affine** class (Schaefer's `F₂`-linear side).  A single
affine constraint is `∑ᵢ cᵢ xᵢ = b` over `ZMod 2`.  Its satisfiability has a closed rule with *no*
search: it is solvable iff some coefficient is nonzero (then the linear form is onto `F₂`, so it hits
`b`), or the target is `0` (then the all-zero assignment works).

Built through the Mikoshi pipeline: the solvability rule was gated by SymPy first — enumerating all
`c ∈ {0,1}⁴, b ∈ {0,1}` gave `0` mismatches against `(∃ i, cᵢ = 1) ∨ b = 0` — before this Lean proof.

## What is proved

* **`affine_sat_iff`** — `(∃ x, ∑ᵢ cᵢ xᵢ = b) ↔ (∃ i, cᵢ = 1) ∨ b = 0`.  Forward: if every `cᵢ = 0`
  the sum is `0`, forcing `b = 0`.  Backward: from a nonzero `cᵢ₀`, the assignment `xᵢ₀ = b` (rest `0`)
  hits `b`; from `b = 0`, the all-zero assignment works.

## Honest scope

A complete, real fast-SAT — for a **single affine (`F₂`-linear) constraint**, the atom of Schaefer's
affine tractable class.  It fills `Attack.decides` for this class.  It is *not* general CNF-SAT: by
Schaefer's dichotomy, the P-side is exactly {`0`-valid, `1`-valid, Horn, dual-Horn, affine, bijunctive},
and *everything else* (3-SAT, general SAT) is NP-complete — that hard side is the wall.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AffineFastSAT

open Finset

variable {n : ℕ}

/-- The value of the affine form `∑ᵢ cᵢ xᵢ` over `F₂` at an assignment `x`. -/
def affineVal (c x : Fin n → ZMod 2) : ZMod 2 := ∑ i, c i * x i

/-- The affine constraint `∑ᵢ cᵢ xᵢ = b` is satisfiable. -/
def AffineSat (c : Fin n → ZMod 2) (b : ZMod 2) : Prop := ∃ x, affineVal c x = b

/-- **Affine (`F₂`) SAT by a closed rule (proved).**  A single affine constraint is satisfiable iff some
coefficient is nonzero, or the target is `0` — no `2^n` search. -/
theorem affine_sat_iff (c : Fin n → ZMod 2) (b : ZMod 2) :
    AffineSat c b ↔ (∃ i, c i = 1) ∨ b = 0 := by
  have zmod_two : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  constructor
  · rintro ⟨x, hx⟩
    by_cases hc : ∃ i, c i = 1
    · exact Or.inl hc
    · right
      push_neg at hc
      have hall : ∀ i, c i = 0 := fun i => zmod_two (c i) (hc i)
      have hzero : affineVal c x = 0 := by
        unfold affineVal
        exact Finset.sum_eq_zero (fun i _ => by rw [hall i, zero_mul])
      rw [hzero] at hx
      exact hx.symm
  · rintro (⟨i₀, hi₀⟩ | hb)
    · refine ⟨fun j => if j = i₀ then b else 0, ?_⟩
      show ∑ i, c i * (if i = i₀ then b else 0) = b
      have h₀ : ∀ j ∈ (univ : Finset (Fin n)), j ≠ i₀ →
          c j * (if j = i₀ then b else 0) = 0 := by
        intro j _ hj; rw [if_neg hj, mul_zero]
      rw [Finset.sum_eq_single_of_mem i₀ (mem_univ i₀) h₀, if_pos rfl, hi₀, one_mul]
    · exact ⟨fun _ => 0, by simp [affineVal, hb]⟩

end PallLean.Paper93.DeepMath.PathB.AffineFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.AffineFastSAT.affine_sat_iff
