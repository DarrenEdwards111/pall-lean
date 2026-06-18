import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Boosting

/-!
# The per-clause agreement bound over `F₂` — discharging `SingleSubsetAgreement` by the parity-toggle involution

Entry 267 left `SingleSubsetAgreement` (the per-clause `≥ 1/2` probabilistic primitive of boosting) as a named socket.
This file **discharges it over `F₂`** — and there the bound is *exactly* `1/2`, proved by the parity-toggle involution.

**The bound.**  For a nonzero input `x` (some `xᵢ = true`), pick `j` with `xⱼ = true`.  The map `tog j S := S △ {j}`
(toggle membership of `j`) is an involution on subsets that *flips* the clause parity `par x S := ∑_{i∈S} xᵢ ∈ F₂`
(`par x (tog j S) = par x S + 1`, since the `j`-term equals `1`).  Hence `tog j` is a bijection between
`{S : par = 0}` and `{S : par ≠ 0}`, so the two fibers have *equal* cardinality — each `2ⁿ⁻¹`.  Therefore
`#{S : par x S ≠ 0} = 2ⁿ⁻¹`, i.e. `2ⁿ ≤ 2 · #{S : par x S ≠ 0}`: the clause fires correctly on exactly half the
subsets.

## What is proved (clean axioms, no `sorry`)

* **`par_tog`** (PROVED) — `par x (tog j S) = par x S + 1` over `F₂` (toggling `j ∈ supp x` flips the parity).
* **`tog_tog`** / **`tog_injective`** (PROVED) — `tog j` is an involution, hence injective.
* **`singleSubsetAgreement_two`** (PROVED) — for any `x` with a `true` coordinate,
  `SingleSubsetAgreement 2 n x` holds: the per-clause agreement over `F₂` is (exactly) `1/2`.  **The `SingleSubsetAgreement`
  socket of entry 267 is discharged over `F₂`.**

## Honest scope

This proves the per-clause `≥ 1/2` (in fact `= 1/2`) agreement bound over `F₂` — one of the two probabilistic sockets
of the boosting step (entry 267).  Composed with boosting (`boost_correct_off_iInter`, proved) and the remaining
`IndependentIntersectionBound` socket, it would give the single-gate low-degree approximation with error `2^{-k}`.  This
does **not** prove the general-`F_p` bound or the independence socket, and is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0SingleSubsetF2

/-- **The clause parity** `par x S := ∑_{i∈S} xᵢ ∈ F₂` (the Fermat clause sum at `p = 2`). -/
def parF2 {n : ℕ} (x : Fin n → Bool) (S : Finset (Fin n)) : ZMod 2 :=
  ∑ i ∈ S, (if x i then (1 : ZMod 2) else 0)

/-- **The toggle** `tog j S := S △ {j}` (add `j` if absent, remove it if present). -/
def tog {n : ℕ} (j : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if j ∈ S then S.erase j else insert j S

/-- **The parity flip (PROVED).**  Toggling `j` (with `xⱼ = true`) flips the clause parity: `par x (tog j S) =
par x S + 1` over `F₂`. -/
theorem par_tog {n : ℕ} (x : Fin n → Bool) (j : Fin n) (hj : x j = true) (S : Finset (Fin n)) :
    parF2 x (tog j S) = parF2 x S + 1 := by
  unfold tog
  by_cases hjS : j ∈ S
  · rw [if_pos hjS]
    have hsplit : parF2 x S = (if x j then (1 : ZMod 2) else 0) + parF2 x (S.erase j) := by
      unfold parF2
      exact (Finset.add_sum_erase S (fun i => if x i then (1 : ZMod 2) else 0) hjS).symm
    rw [if_pos hj] at hsplit
    exact (by decide : ∀ a b : ZMod 2, a = 1 + b → b = a + 1) _ _ hsplit
  · rw [if_neg hjS]
    have hsplit : parF2 x (insert j S) = (if x j then (1 : ZMod 2) else 0) + parF2 x S := by
      unfold parF2
      exact Finset.sum_insert hjS
    rw [if_pos hj] at hsplit
    exact (by decide : ∀ a b : ZMod 2, a = 1 + b → a = b + 1) _ _ hsplit

/-- **The toggle is an involution (PROVED).** -/
theorem tog_tog {n : ℕ} (j : Fin n) (S : Finset (Fin n)) : tog j (tog j S) = S := by
  by_cases hjS : j ∈ S
  · have h1 : tog j S = S.erase j := by unfold tog; rw [if_pos hjS]
    rw [h1]
    unfold tog
    rw [if_neg (show j ∉ S.erase j by simp), Finset.insert_erase hjS]
  · have h1 : tog j S = insert j S := by unfold tog; rw [if_neg hjS]
    rw [h1]
    unfold tog
    rw [if_pos (Finset.mem_insert_self j S), Finset.erase_insert hjS]

/-- **The toggle is injective (PROVED).** -/
theorem tog_injective {n : ℕ} (j : Fin n) : Function.Injective (tog j) :=
  Function.LeftInverse.injective (fun S => tog_tog j S)

/-- **The per-clause agreement bound over `F₂` (PROVED).**  For any `x` with a `true` coordinate, at least half the
subsets `S` make the clause parity nonzero (in fact exactly half): `SingleSubsetAgreement 2 n x`.  The `SingleSubsetAgreement`
socket of entry 267 is discharged over `F₂`, by the parity-toggle involution. -/
theorem singleSubsetAgreement_two {n : ℕ} (x : Fin n → Bool) (hx : ∃ i, x i = true) :
    PallLean.Paper93.DeepMath.PathB.ACC0Boosting.SingleSubsetAgreement 2 n x := by
  obtain ⟨j, hj⟩ := hx
  have hflip : ∀ a : ZMod 2, a ≠ 0 → a + 1 = 0 := by decide
  have hne : (0 : ZMod 2) + 1 ≠ 0 := by decide
  -- the toggle bijects the two parity fibers, so they are equinumerous
  have himg : (Finset.univ.filter (fun S => parF2 x S = 0)).image (tog j)
      = Finset.univ.filter (fun S => parF2 x S ≠ 0) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨S, hS, rfl⟩
      rw [par_tog x j hj, hS]
      exact hne
    · intro hT
      refine ⟨tog j T, ?_, tog_tog j T⟩
      rw [par_tog x j hj]
      exact hflip (parF2 x T) hT
  have hcard : (Finset.univ.filter (fun S => parF2 x S = 0)).card
      = (Finset.univ.filter (fun S => parF2 x S ≠ 0)).card := by
    rw [← himg, Finset.card_image_of_injective _ (tog_injective j)]
  have htot : (Finset.univ.filter (fun S => parF2 x S = 0)).card
      + (Finset.univ.filter (fun S => parF2 x S ≠ 0)).card = 2 ^ n := by
    simp only [ne_eq]
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_finset,
      Fintype.card_fin]
  have key : 2 ^ n ≤ 2 * (Finset.univ.filter (fun S => parF2 x S ≠ 0)).card := by omega
  exact key

/-!
**The rung.**  The per-clause agreement primitive `SingleSubsetAgreement` is now *proved* over `F₂` — and it is exactly
`1/2`, by the parity-toggle involution `S ↦ S △ {j}`.  Together with the proved boosting (`boost_correct_off_iInter`,
entry 267), the only probabilistic ingredient still socketed for the single-gate low-degree approximation is
`IndependentIntersectionBound` (independence of the random subsets).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SingleSubsetF2

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SingleSubsetF2.par_tog
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SingleSubsetF2.tog_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SingleSubsetF2.singleSubsetAgreement_two
