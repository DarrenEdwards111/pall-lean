import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadTwoPoint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityCodebook

/-!
# N-Frame: the origin-pinning supply — homogeneous pins for the quadratic drag

Route H drag rung (… → quadratic two-point → **origin-pinning supply**).  `quad_two_point`
takes the witness cut `{0, w}` THROUGH THE ORIGIN as a hypothesis (`hpair`).  This constructs
it: HOMOGENEOUS pins (demanded value `0`, so `a = 0` always satisfies them) plus off-support
scaffold, whose joint solution set is exactly `{0, w}` with `w = e_i + e_j` — the quadratic
analog of `singleton_supply`, pinned through the origin so the non-affine primitive stays
value-independent.

  `homogeneous_pair_solution` — **PROVED, THE CORE**: the homogeneous system `a_i + a_j = 0`
        (the free-direction pin) together with `a_k = 0` off `{i,j}` (the scaffold) has
        solution set exactly `{0, e_i + e_j}` — a line through the ORIGIN.
  `origin_w_flip` — **PROVED**: `w = e_i + e_j` satisfies `w_i·w_j = 1` (the `hqw` the
        quadratic target monomial `[a_i·a_j = 1]` flips on).
  `homogeneous_hpair` — **PROVED, THE SUPPLY**: for the homogeneous pin/scaffold layout, the
        `quad_two_point` hypothesis `hpair` holds — the witness set is `{0, w}`.
  `quad_two_point_origin` — **PROVED, THE COMPOSITION**: `homogeneous_hpair` + `origin_w_flip`
        feed `quad_two_point` for the single-insert quadratic target, discharging every
        hypothesis — the origin-pinned quadratic drag runs end to end.

## Honest scope — what this closes (Route H)

With this the origin-pinned quadratic detection runs on a CONSTRUCTED witness cut, not an
assumed one: homogeneous pins realise `{0, w}` through the origin, and the quadratic target
flips on `w_i·w_j = 1`.  What remains for a `(2+c)N` quadratic bound: the layout/tuple/capacity
transfer (28b/28c `GLit` analogs) and the concentration analysis at the raised local rank.
The pins here force a single line; the drag's `Θ(N)`-tuple version needs the transversal
placement of many such origin-pinned lines at one balanced cut.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadSupply

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint

variable {v m : ℕ}

/-- Linearity of the pairing in the functional slot (local, to avoid a heavy import). -/
theorem dotp_add_left' (l l' a : Fin v → ZMod 2) :
    dotp (l + l') a = dotp l a + dotp l' a := by
  unfold dotp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  show (l k + l' k) * a k = l k * a k + l' k * a k
  ring

/-- **THE CORE (proved)**: the homogeneous system (free-direction pin `a_i + a_j = 0`, plus
`a_k = 0` off `{i,j}`) has solution set exactly the origin-line `{0, e_i + e_j}`. -/
theorem homogeneous_pair_solution (i j : Fin v) (hij : i ≠ j) (a : Fin v → ZMod 2) :
    ((a i + a j = 0) ∧ (∀ k, k ≠ i → k ≠ j → a k = 0))
    ↔ (a = 0 ∨ a = single v i + single v j) := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hsum0 : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  constructor
  · rintro ⟨hsum, hoff⟩
    have haij : a i = a j := hsum0 _ _ hsum
    rcases hz (a i) with hai | hai
    · left
      funext k
      show a k = (0 : Fin v → ZMod 2) k
      rw [Pi.zero_apply]
      by_cases hk : k = i
      · rw [hk]; exact hai
      · by_cases hk' : k = j
        · rw [hk', ← haij]; exact hai
        · exact hoff k hk hk'
    · right
      have haj : a j = 1 := by rw [← haij]; exact hai
      funext k
      show a k = (single v i + single v j) k
      rw [Pi.add_apply]
      unfold single
      by_cases hk : k = i
      · subst hk
        rw [if_pos rfl, if_neg hij, add_zero]
        exact hai
      · by_cases hk' : k = j
        · subst hk'
          rw [if_neg (Ne.symm hij), if_pos rfl, zero_add]
          exact haj
        · rw [if_neg hk, if_neg hk', add_zero]
          exact hoff k hk hk'
  · rintro (rfl | rfl)
    · exact ⟨by simp, fun k _ _ => by simp⟩
    · refine ⟨?_, ?_⟩
      · show (single v i + single v j) i + (single v i + single v j) j = 0
        rw [Pi.add_apply, Pi.add_apply]
        unfold single
        rw [if_pos rfl, if_neg hij, if_neg (Ne.symm hij), if_pos rfl]
        decide
      · intro k hk hk'
        show (single v i + single v j) k = 0
        rw [Pi.add_apply]
        unfold single
        rw [if_neg hk, if_neg hk']
        decide

/-- **The target flip (proved)**: `w = e_i + e_j` has `w_i·w_j = 1` — the `hqw` the quadratic
target monomial `[a_i·a_j = 1]` detects. -/
theorem origin_w_flip (i j : Fin v) (hij : i ≠ j) :
    (single v i + single v j) i * (single v i + single v j) j = 1 := by
  rw [Pi.add_apply, Pi.add_apply]
  unfold single
  rw [if_pos rfl, if_neg hij, if_neg (Ne.symm hij), if_pos rfl]
  decide

/-- **THE SUPPLY (proved)**: for the homogeneous pin/scaffold layout — every non-target block
the pin `{aff (e_i+e_j) 0}`, the shared scaffold the off-support singletons — the
`quad_two_point` hypothesis `hpair` holds with the witness set `{0, w}` through the origin. -/
theorem homogeneous_hpair (i j : Fin v) (hij : i ≠ j)
    (cstar c₀ : Fin m) (hc₀ : c₀ ≠ cstar)
    (Bk : Fin m → Finset (GLit v))
    (hBk : ∀ c, c ≠ cstar → Bk c = {GLit.aff (single v i + single v j) 0})
    (a : Fin v → ZMod 2) :
    ((∀ c, c ≠ cstar → gBlockSat a (Bk c))
      ∧ ∀ ℓ ∈ ((Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1)),
          ¬ gLitHolds a ℓ)
    ↔ (a = 0 ∨ a = single v i + single v j) := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  -- the pins force a_i + a_j = 0
  have hpin : (∀ c, c ≠ cstar → gBlockSat a (Bk c)) ↔ (a i + a j = 0) := by
    constructor
    · intro h
      have h0 := h c₀ hc₀
      rw [hBk c₀ hc₀] at h0
      obtain ⟨ℓ, hℓ, hlit⟩ := h0
      rw [Finset.mem_singleton] at hℓ
      subst hℓ
      change dotp (single v i + single v j) a = 0 at hlit
      rw [dotp_add_left', dotp_single, dotp_single] at hlit
      exact hlit
    · intro h c hc
      rw [hBk c hc]
      refine ⟨GLit.aff (single v i + single v j) 0, Finset.mem_singleton_self _, ?_⟩
      change dotp (single v i + single v j) a = 0
      rw [dotp_add_left', dotp_single, dotp_single]
      exact h
  -- the scaffold forces a_k = 0 off {i,j}
  have hscaf : (∀ ℓ ∈ ((Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1)),
      ¬ gLitHolds a ℓ) ↔ (∀ k, k ≠ i → k ≠ j → a k = 0) := by
    constructor
    · intro h k hki hkj
      have hmem : GLit.aff (single v k) 1
          ∈ (Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1) := by
        apply Finset.mem_image_of_mem
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hki, hkj⟩
      have hlit := h _ hmem
      change ¬ (dotp (single v k) a = 1) at hlit
      rw [dotp_single] at hlit
      rcases hz (a k) with h0 | h1
      · exact h0
      · exact absurd h1 hlit
    · intro h ℓ hℓ hlit
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hℓ
      rw [Finset.mem_sdiff] at hk
      have hki : k ≠ i := fun hc => hk.2 (by rw [hc]; exact Finset.mem_insert_self i {j})
      have hkj : k ≠ j := fun hc =>
        hk.2 (by rw [hc]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
      change dotp (single v k) a = 1 at hlit
      rw [dotp_single, h k hki hkj] at hlit
      exact absurd hlit (by decide)
  rw [hpin, hscaf]
  exact homogeneous_pair_solution i j hij a

set_option maxHeartbeats 1600000 in
/-- **THE COMPOSITION (proved)**: the origin-pinned quadratic drag runs end to end — the
homogeneous supply discharges every `quad_two_point` hypothesis for the single-insert
quadratic target `[a_i·a_j = 1]`, so the two rows' `gParityFamily` values DIFFER. -/
theorem quad_two_point_origin (i j : Fin v) (hij : i ≠ j)
    (cstar c₀ : Fin m) (hc₀ : c₀ ≠ cstar) :
    gParityFamily
        (fun c => if c = cstar
          then (Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1)
          else {GLit.aff (single v i + single v j) 0})
      ≠ gParityFamily
        (fun c => if c = cstar
          then insert (GLit.quad i j 1)
            ((Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1))
          else {GLit.aff (single v i + single v j) 0}) := by
  classical
  set Tsh : Finset (GLit v) :=
    (Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1) with hTsh
  set pin : Finset (GLit v) := {GLit.aff (single v i + single v j) 0} with hpin
  set Bk : Fin m → Finset (GLit v) := fun c => if c = cstar then Tsh else pin with hBkdef
  set Bk' : Fin m → Finset (GLit v) :=
    fun c => if c = cstar then insert (GLit.quad i j 1) Tsh else pin with hBk'def
  have hBkc : ∀ c, c ≠ cstar → Bk c = pin := fun c hc => if_neg hc
  have hBk'c : ∀ c, c ≠ cstar → Bk' c = pin := fun c hc => if_neg hc
  apply quad_two_point Bk Bk' cstar Tsh (∅ : Finset (GLit v)) {GLit.quad i j 1}
    (single v i + single v j) i j (origin_w_flip i j hij)
  · -- hT : Bk cstar = Tsh ∪ ∅
    show (if cstar = cstar then Tsh else pin) = Tsh ∪ ∅
    rw [if_pos rfl, Finset.union_empty]
  · -- hT' : Bk' cstar = Tsh ∪ {quad i j 1}
    show (if cstar = cstar then insert (GLit.quad i j 1) Tsh else pin)
      = Tsh ∪ {GLit.quad i j 1}
    rw [if_pos rfl, Finset.union_comm, Finset.insert_eq]
  · -- htar'
    exact Finset.mem_singleton_self _
  · -- h0t : ∀ ℓ ∈ ∅
    intro ℓ hℓ
    exact absurd hℓ (Finset.notMem_empty ℓ)
  · -- h0t' : ∀ ℓ ∈ {quad i j 1}, ¬ gLitHolds 0 ℓ
    intro ℓ hℓ
    rw [Finset.mem_singleton] at hℓ
    subst hℓ
    change ¬ ((0 : Fin v → ZMod 2) i * (0 : Fin v → ZMod 2) j = 1)
    simp
  · -- hkert : ∀ ℓ ∈ ∅
    intro ℓ hℓ
    exact absurd hℓ (Finset.notMem_empty ℓ)
  · -- hnt : non-target blocks agree
    intro a
    constructor
    · intro h c hc
      rw [hBk'c c hc]
      have := h c hc
      rw [hBkc c hc] at this
      exact this
    · intro h c hc
      rw [hBkc c hc]
      have := h c hc
      rw [hBk'c c hc] at this
      exact this
  · -- hpair : from the supply
    intro a
    have hsup := homogeneous_hpair i j hij cstar c₀ hc₀ Bk hBkc a
    -- hsup's scaffold set is Tsh; rewrite
    rw [← hTsh] at hsup
    exact hsup

end PallLean.Paper93.DeepMath.PathB.NFrameQuadSupply

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadSupply.homogeneous_pair_solution
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadSupply.origin_w_flip
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadSupply.homogeneous_hpair
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadSupply.quad_two_point_origin
