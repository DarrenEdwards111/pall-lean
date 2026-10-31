import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParitySupply

/-!
# N-Frame: the parity codebook — the explicit per-target supply

Rung 28d of the arc (… → parity supply → **parity codebook**).  The per-target supply package
of rung 28c, CONSTRUCTED explicitly over the singleton core of the expander-affine codebook,
exactly as the counting round derived it:

    w  := e_{j*}                        (the target's coordinate),
    a₀ := (j* ↦ b*+1, j_k ↦ b_k+1, else 0)   (the explicit falsifying point),
    pins    := the COMPLEMENTS of the target block's priced literals (one per tuple
               coordinate — consistent by design, `w`-kernel automatic),
    scaffold := (e_j, 1) on the remaining coordinates (falsified at `a₀`, `w`-kernel).

  `single` / `dotp_single` — the singleton functionals and their evaluation.
  `singleton_supply` — **PROVED, THE SUPPLY PACKAGE**: for every target coordinate `j*`,
        value `b*`, and dedup'd tuple-coordinate set `K ∌ j*` with values `bval`, explicit
        `(w, a₀)` satisfying ALL the linear slots of rung 28c's `parity_pair_dist`:
        `hlw`, `hwE`-kernels, `ha₀`-falsifications, the complement-pin consistency, and the
        pair-solution identity (pins ∧ scaffold-false ⟺ `a ∈ {a₀, a₀ + w}`).

## Honest scope

This is the singleton-core construction; per the counting round, the EXPANDER enters at pin
LIVENESS only (which reserve positions are probe-side — the `hlive` slot of 28c, already
hypothesis-shaped; without the expander's decomposition redundancy the kill/capacity ratio is
the knife-edge 1, with it `1 + c_d·d`).  The position-level bookkeeping tying these
coordinate-level literals to codebook indices, the Markov `|V| = Θ(T)` theorem, and the
rung-29 `cbudget` conversion are the remaining assembly.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval

variable {v : ℕ}

/-- The singleton functional `e_j`. -/
def single (v : ℕ) (j : Fin v) : Fin v → ZMod 2 := fun i => if i = j then 1 else 0

theorem dotp_single (j : Fin v) (a : Fin v → ZMod 2) :
    dotp (single v j) a = a j := by
  unfold dotp single
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, one_mul]
  · intro i _ hne
    rw [if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

set_option maxHeartbeats 1600000 in
/-- **THE SUPPLY PACKAGE (proved)**: the explicit `(w, a₀)` for any target coordinate and
dedup'd tuple-coordinate set — every linear slot of the rung-28c pair discharge. -/
theorem singleton_supply (v : ℕ) (jstar : Fin v) (bstar : ZMod 2)
    (K : Finset (Fin v)) (hK : jstar ∉ K) (bval : Fin v → ZMod 2) :
    ∃ w a₀ : Fin v → ZMod 2,
      dotp (single v jstar) w = 1
      ∧ (∀ j ∈ K, dotp (single v j) w = 0)
      ∧ ¬ litHolds a₀ (single v jstar, bstar)
      ∧ (∀ j ∈ K, ¬ litHolds a₀ (single v j, bval j))
      ∧ (∀ j ∈ K, litHolds a₀ (single v j, bval j + 1))
      ∧ (∀ a : Fin v → ZMod 2,
          ((∀ j ∈ K, litHolds a (single v j, bval j + 1))
            ∧ ∀ j : Fin v, j ∉ K → j ≠ jstar → ¬ litHolds a (single v j, 1))
          ↔ (a = a₀ ∨ a = a₀ + w)) := by
  classical
  have hy1 : ∀ x y : ZMod 2, ¬ x = y ↔ x = y + 1 := by decide
  have hy2 : ∀ y : ZMod 2, ¬ (y + 1 = y) := by decide
  have hz : ∀ x : ZMod 2, ¬ x = 1 → x = 0 := by decide
  have h11 : ∀ x : ZMod 2, x + 1 + 1 = x := by decide
  set a₀ : Fin v → ZMod 2 := fun j =>
    if j = jstar then bstar + 1 else if j ∈ K then bval j + 1 else 0 with ha₀
  have ha₀star : a₀ jstar = bstar + 1 := by
    rw [ha₀]
    exact if_pos rfl
  have ha₀K : ∀ j ∈ K, a₀ j = bval j + 1 := by
    intro j hj
    have hne : j ≠ jstar := fun hcon => hK (hcon ▸ hj)
    rw [ha₀]
    show (if j = jstar then bstar + 1 else if j ∈ K then bval j + 1 else 0)
      = bval j + 1
    rw [if_neg hne, if_pos hj]
  have ha₀off : ∀ j : Fin v, j ∉ K → j ≠ jstar → a₀ j = 0 := by
    intro j hjK hjs
    rw [ha₀]
    show (if j = jstar then bstar + 1 else if j ∈ K then bval j + 1 else 0) = 0
    rw [if_neg hjs, if_neg hjK]
  refine ⟨single v jstar, a₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dotp_single]
    show (if jstar = jstar then (1 : ZMod 2) else 0) = 1
    rw [if_pos rfl]
  · intro j hj
    rw [dotp_single]
    have hne : j ≠ jstar := fun hcon => hK (hcon ▸ hj)
    show (if j = jstar then (1 : ZMod 2) else 0) = 0
    rw [if_neg hne]
  · show ¬ dotp (single v jstar) a₀ = bstar
    rw [dotp_single, ha₀star]
    exact hy2 bstar
  · intro j hj
    show ¬ dotp (single v j) a₀ = bval j
    rw [dotp_single, ha₀K j hj]
    exact hy2 (bval j)
  · intro j hj
    show dotp (single v j) a₀ = bval j + 1
    rw [dotp_single]
    exact ha₀K j hj
  · intro a
    constructor
    · rintro ⟨hpins, hscaf⟩
      -- a agrees with a₀ off jstar
      have hoffK : ∀ j ∈ K, a j = a₀ j := by
        intro j hj
        have h1 : dotp (single v j) a = bval j + 1 := hpins j hj
        rw [dotp_single] at h1
        rw [h1, ha₀K j hj]
      have hoffO : ∀ j : Fin v, j ∉ K → j ≠ jstar → a j = a₀ j := by
        intro j hjK hjs
        have h1 : ¬ dotp (single v j) a = 1 := hscaf j hjK hjs
        rw [dotp_single] at h1
        rw [hz _ h1, ha₀off j hjK hjs]
      by_cases hstar : a jstar = a₀ jstar
      · left
        funext j
        by_cases hjs : j = jstar
        · rw [hjs]
          exact hstar
        · by_cases hjK : j ∈ K
          · exact hoffK j hjK
          · exact hoffO j hjK hjs
      · right
        funext j
        show a j = a₀ j + single v jstar j
        by_cases hjs : j = jstar
        · subst hjs
          show a j = a₀ j + (if j = j then (1 : ZMod 2) else 0)
          rw [if_pos rfl]
          have h1 : a j = a₀ j + 1 := (hy1 _ _).mp hstar
          exact h1
        · show a j = a₀ j + (if j = jstar then (1 : ZMod 2) else 0)
          rw [if_neg hjs, add_zero]
          by_cases hjK : j ∈ K
          · exact hoffK j hjK
          · exact hoffO j hjK hjs
    · rintro (rfl | rfl)
      · constructor
        · intro j hj
          show dotp (single v j) a₀ = bval j + 1
          rw [dotp_single]
          exact ha₀K j hj
        · intro j hjK hjs
          show ¬ dotp (single v j) a₀ = 1
          rw [dotp_single, ha₀off j hjK hjs]
          exact fun hcon => absurd hcon.symm (by decide)
      · constructor
        · intro j hj
          have hne : j ≠ jstar := fun hcon => hK (hcon ▸ hj)
          show dotp (single v j) (a₀ + single v jstar) = bval j + 1
          rw [dotp_single]
          show a₀ j + (if j = jstar then (1 : ZMod 2) else 0) = bval j + 1
          rw [if_neg hne, add_zero]
          exact ha₀K j hj
        · intro j hjK hjs
          show ¬ dotp (single v j) (a₀ + single v jstar) = 1
          rw [dotp_single]
          show ¬ (a₀ j + (if j = jstar then (1 : ZMod 2) else 0) = 1)
          rw [if_neg hjs, add_zero, ha₀off j hjK hjs]
          exact fun hcon => absurd hcon.symm (by decide)

end PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook.dotp_single
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook.singleton_supply
