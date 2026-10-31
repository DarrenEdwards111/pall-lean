import Mathlib

/-!
# The Razborov–Smolensky per-point error bound — the detection involution (proved)

Entry 212 left the per-input `3/4`-supply (`Uniform34`) as the last BT-side socket: at every input, a `≥3/4` fraction
of the approximant family is correct.  Its source is the **Razborov–Smolensky probabilistic polynomial method's per-point
guarantee**: a random low-degree approximant of an `OR`/`MOD` gate agrees with it, at each fixed input, with probability
`≥ 3/4`.  This file proves the genuine *algebraic heart* of that guarantee — the **single-trial detection bound**, by an
involution — and boosts it to `≥ 3/4` with two independent trials.

The construction (RS for `OR`).  To detect whether an input vector `x` is nonzero, take a random subset `S` and test
`∑_{i∈S} x i ≠ 0`.  If `x = 0` the sum is always `0` (no false positive).  If some `x j ≠ 0`, a random `S` detects it
(`sum ≠ 0`) with probability `≥ 1/2`: pair each `S` with `S △ {j}`, whose sum differs by `±x j ≠ 0`, so at most one of
the pair has sum `0` — the **involution `toggle j`** maps the "missed" subsets injectively into the "detected" ones.
Two independent trials (`OR` of two subset tests) miss only if *both* miss (`≤ 1/4`), giving detection `≥ 3/4` — the
per-point error `≤ 1/4`.

## What is proved (clean axioms, no `sorry`)

* **`toggle`** / **`toggle_involutive`** — toggling coordinate `j` (`S △ {j}`) is an involution on `Finset (Fin s)`.
* **`subsetSum_toggle`** — the subset sum changes by exactly `±x j` under `toggle j`.
* **`detection_half`** — the single-trial detection bound: if `x j ≠ 0`, then `2^s ≤ 2 · #{S | ∑_{i∈S} x i ≠ 0}`
  (a random subset detects with probability `≥ 1/2`), via the `toggle j` involution.
* **`detection_two_thirds_four`** — the two-trial boost: `3·4^s ≤ 4 · #{(S₁,S₂) | sum₁ ≠ 0 ∨ sum₂ ≠ 0}` (detection
  `≥ 3/4`, per-point error `≤ 1/4`).

## Honest scope

This proves the genuine **algebraic heart of the RS per-point guarantee** — the single-trial subset-sum detection
`≥ 1/2` (the `toggle` involution / pairing argument) and its two-trial boost to `≥ 3/4` — completely, in pure
`AddCommGroup`/`Finset` arithmetic, no measure theory.  This is exactly the per-point error `≤ 1/4` that underlies the
`Uniform34` per-input `3/4`-supply socket of entry 212.  What remains, to fully discharge `Uniform34`, is the
**gate-to-supply packaging**: that this subset-sum test *is* the `OR`/`MOD`-gate approximant (the `(∑)^{p−1}` Fermat
indicator over `F_p`), that the `OR(x)=0` case is always correct (no false positive — proved here as "sum always `0`"),
and that composing per-gate approximants across the constant-depth circuit yields a per-input `≥3/4` supply for the whole
circuit (the RS composition).  This proves the per-point *detection* bound, the analytic core; the gate-encoding and
circuit-composition packaging remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RSPerPoint

open Finset

variable {F : Type*} [AddCommGroup F] [DecidableEq F] {s : ℕ}

/-- **Toggle coordinate `j`** — the symmetric difference `S △ {j}`: remove `j` if present, else insert it. -/
def toggle (j : Fin s) (S : Finset (Fin s)) : Finset (Fin s) :=
  if j ∈ S then S.erase j else insert j S

/-- **`toggle j` is an involution (PROVED).**  Toggling twice restores `S` (`insert_erase` / `erase_insert`). -/
theorem toggle_involutive (j : Fin s) : Function.Involutive (toggle j) := by
  intro S
  unfold toggle
  by_cases h : j ∈ S
  · rw [if_pos h, if_neg (by simp), insert_erase h]
  · rw [if_neg h, if_pos (by simp), erase_insert h]

/-- **The subset sum changes by `±x j` under `toggle j` (PROVED).**  `∑_{i∈toggle j S} x i = ∑_{i∈S} x i ± x j`
(`−x j` if `j ∈ S`, `+x j` otherwise). -/
theorem subsetSum_toggle (x : Fin s → F) (j : Fin s) (S : Finset (Fin s)) :
    (∑ i ∈ toggle j S, x i) = (∑ i ∈ S, x i) + (if j ∈ S then - x j else x j) := by
  unfold toggle
  by_cases h : j ∈ S
  · rw [if_pos h, if_pos h, Finset.sum_erase_eq_sub h]; abel
  · rw [if_neg h, if_neg h, Finset.sum_insert h]; abel

/-- **The single-trial detection bound (PROVED) — the RS per-point heart.**  If some coordinate `x j ≠ 0`, then a random
subset detects it (`∑_{i∈S} x i ≠ 0`) with probability `≥ 1/2`: `2^s ≤ 2 · #{S | ∑_{i∈S} x i ≠ 0}`.  Proof: the
involution `toggle j` maps each "missed" subset (`sum = 0`) to a "detected" one (`sum = ±x j ≠ 0`) injectively, so
`#{miss} ≤ #{detect}`; with `#{miss} + #{detect} = 2^s` this gives `2·#{detect} ≥ 2^s`. -/
theorem detection_half (x : Fin s → F) (j : Fin s) (hj : x j ≠ 0) :
    2 ^ s ≤ 2 * (Finset.univ.filter (fun S : Finset (Fin s) => (∑ i ∈ S, x i) ≠ 0)).card := by
  set B := Finset.univ.filter (fun S : Finset (Fin s) => (∑ i ∈ S, x i) = 0) with hB
  set G := Finset.univ.filter (fun S : Finset (Fin s) => (∑ i ∈ S, x i) ≠ 0) with hG
  have hmap : ∀ S ∈ B, toggle j S ∈ G := by
    intro S hSB
    rw [hB, Finset.mem_filter] at hSB
    rw [hG, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [subsetSum_toggle, hSB.2, zero_add]
    by_cases h : j ∈ S <;> simp [h, hj, neg_eq_zero]
  have hBG : B.card ≤ G.card :=
    Finset.card_le_card_of_injOn (toggle j) hmap
      (fun a _ b _ hab => (toggle_involutive j).injective hab)
  have hpart : B.card + G.card = 2 ^ s := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Finset (Fin s))))
      (p := fun S => (∑ i ∈ S, x i) = 0)
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at h
    rw [hB, hG]; exact h
  omega

/-- **The two-trial boost (PROVED): detection `≥ 3/4`.**  With two independent subset tests `OR`-ed, detection fails only
if *both* miss; since each misses with probability `≤ 1/2`, both miss with probability `≤ 1/4`, so
`3·4^s ≤ 4 · #{(S₁,S₂) | sum₁ ≠ 0 ∨ sum₂ ≠ 0}` — the per-point error `≤ 1/4`.  Proof: `#{both miss} = #{miss}²` (product
of the per-coordinate filters), `#{miss} ≤ 2^{s−1}` (from `detection_half`), so `4·#{miss}² ≤ 4^s`, and `#{detect} =
4^s − #{miss}² ≥ 3·4^{s−1}`. -/
theorem detection_two_thirds_four (x : Fin s → F) (j : Fin s) (hj : x j ≠ 0) :
    3 * 4 ^ s ≤ 4 * (Finset.univ.filter
      (fun p : Finset (Fin s) × Finset (Fin s) =>
        (∑ i ∈ p.1, x i) ≠ 0 ∨ (∑ i ∈ p.2, x i) ≠ 0)).card := by
  classical
  have hdet := detection_half x j hj
  set d := (Finset.univ.filter (fun S : Finset (Fin s) => (∑ i ∈ S, x i) ≠ 0)).card with hd
  set miss := (Finset.univ.filter (fun S : Finset (Fin s) => (∑ i ∈ S, x i) = 0)).card with hm
  have hsum : d + miss = 2 ^ s := by
    rw [hd, hm, add_comm]
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Finset (Fin s))))
      (p := fun S => (∑ i ∈ S, x i) = 0)
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at h
    exact h
  have hboth : (Finset.univ.filter (fun p : Finset (Fin s) × Finset (Fin s) =>
        (∑ i ∈ p.1, x i) = 0 ∧ (∑ i ∈ p.2, x i) = 0)).card = miss * miss := by
    rw [hm, ← Finset.card_product]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  have htot : Fintype.card (Finset (Fin s) × Finset (Fin s)) = 4 ^ s := by
    rw [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, ← mul_pow]; norm_num
  have hpart2 : (Finset.univ.filter (fun p : Finset (Fin s) × Finset (Fin s) =>
        (∑ i ∈ p.1, x i) = 0 ∧ (∑ i ∈ p.2, x i) = 0)).card
      + (Finset.univ.filter (fun p : Finset (Fin s) × Finset (Fin s) =>
        (∑ i ∈ p.1, x i) ≠ 0 ∨ (∑ i ∈ p.2, x i) ≠ 0)).card = 4 ^ s := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Finset (Fin s) × Finset (Fin s))))
      (p := fun p => (∑ i ∈ p.1, x i) = 0 ∧ (∑ i ∈ p.2, x i) = 0)
    rw [Finset.card_univ, htot] at h
    rw [show (Finset.univ.filter (fun p : Finset (Fin s) × Finset (Fin s) =>
            (∑ i ∈ p.1, x i) ≠ 0 ∨ (∑ i ∈ p.2, x i) ≠ 0))
          = (Finset.univ.filter (fun p => ¬ ((∑ i ∈ p.1, x i) = 0 ∧ (∑ i ∈ p.2, x i) = 0)))
          from Finset.filter_congr (fun p _ => not_and_or.symm)]
    exact h
  have hmle : 2 * miss ≤ 2 ^ s := by omega
  have h4 : 4 * (miss * miss) ≤ 4 ^ s := by
    calc 4 * (miss * miss) = (2 * miss) * (2 * miss) := by ring
      _ ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul hmle hmle
      _ = 4 ^ s := by rw [← mul_pow]; norm_num
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0RSPerPoint

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RSPerPoint.detection_half
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RSPerPoint.detection_two_thirds_four
