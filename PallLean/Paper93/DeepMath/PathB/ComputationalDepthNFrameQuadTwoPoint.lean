import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadDetect

/-!
# N-Frame: the origin-pinned quadratic two-point — a quadratic analog of `parity_two_point`

Route H drag rung (… → quadratic detection primitive → **quadratic two-point**).  The
non-affine detection primitive (`quadMonoCount_origin`) is clean only at the ORIGIN base
point.  This builds the two-point comparison there: a generalized-literal family (affine pins
+ a quadratic target monomial), with the witness cut to `{0, w}` THROUGH THE ORIGIN, whose
two rows get different family parities — the quadratic mirror of rung 28a's `parity_two_point`.

  `GLit` / `gLitHolds` — generalized literals: affine `(λ,β)` OR quadratic monomial
        `[a_i·a_j = t]`, so affine pins/kit and a quadratic target coexist in one family.
  `gParityFamily` — the `⊕#SAT` parity of the generalized family.
  `gCount_split` — **PROVED**: the additive `#sat + #(nonTarget ∧ all-false) = #nonTarget`
        ledger, generalized (verbatim mirror of `count_split`).
  `quad_two_point` — **PROVED, THE QUADRATIC TWO-POINT**: with the witness pinned to `{0, w}`,
        the shared/off-target literals invisible between `0` and `w`, and the target the
        quadratic monomial `[a_i·a_j = 1]` (false at `0`, TRUE at `w` since `w_i·w_j = 1`),
        the two rows' `gParityFamily` values DIFFER — however many positions differ, no
        evenness hypothesis, exactly as the affine two-point but with the DEGREE-2 flip
        `w_i·w_j = 1` replacing the affine `dotp l w = 1`.

## Honest scope — what this closes and what remains (Route H)

This is the origin-pinned quadratic drag CORE: the detection step now runs on a quadratic
target, at the origin base point where the cross-term vanishes.  What remains for a
`(2+c)N` quadratic bound: (i) the layout/tuple transfer and capacity feed for the generalized
family (28b/28c analogs), (ii) an ORIGIN-PINNING supply — pins forcing the witness line
through `0` (homogeneous pins), the quadratic analog of `singleton_supply`, (iii) the
concentration analysis at the raised local rank.  The witness cut `{0, w}` is taken here as a
hypothesis (`hpair`); constructing it through the origin is the supply rung.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval

variable {v m : ℕ}

/-- A generalized literal: affine `(λ, β)` (holds iff `⟨λ,a⟩ = β`) or quadratic monomial
`(i, j, t)` (holds iff `a_i·a_j = t`). -/
inductive GLit (v : ℕ) where
  | aff : (Fin v → ZMod 2) → ZMod 2 → GLit v
  | quad : Fin v → Fin v → ZMod 2 → GLit v

noncomputable instance : DecidableEq (GLit v) := Classical.decEq _

/-- Generalized-literal satisfaction. -/
def gLitHolds (a : Fin v → ZMod 2) : GLit v → Prop
  | .aff l b => dotp l a = b
  | .quad i j t => a i * a j = t

instance decGLitHolds (a : Fin v → ZMod 2) (ℓ : GLit v) : Decidable (gLitHolds a ℓ) :=
  match ℓ with
  | .aff l b => inferInstanceAs (Decidable (dotp l a = b))
  | .quad i j t => inferInstanceAs (Decidable (a i * a j = t))

/-- A generalized block is satisfied: some selected literal holds. -/
def gBlockSat (a : Fin v → ZMod 2) (T : Finset (GLit v)) : Prop :=
  ∃ ℓ ∈ T, gLitHolds a ℓ

instance (a : Fin v → ZMod 2) (T : Finset (GLit v)) : Decidable (gBlockSat a T) :=
  inferInstanceAs (Decidable (∃ ℓ ∈ T, gLitHolds a ℓ))

/-- The generalized instance is satisfied by `a`: every block is. -/
def gInstSat (a : Fin v → ZMod 2) (Bk : Fin m → Finset (GLit v)) : Prop :=
  ∀ c, gBlockSat a (Bk c)

instance (a : Fin v → ZMod 2) (Bk : Fin m → Finset (GLit v)) :
    Decidable (gInstSat a Bk) :=
  inferInstanceAs (Decidable (∀ c, gBlockSat a (Bk c)))

/-- The generalized `⊕#SAT` family. -/
noncomputable def gParityFamily (Bk : Fin m → Finset (GLit v)) : Bool :=
  decide ((Finset.univ.filter (fun a => gInstSat a Bk)).card % 2 = 1)

theorem gInstSat_split (Bk : Fin m → Finset (GLit v)) (cstar : Fin m)
    (a : Fin v → ZMod 2) :
    gInstSat a Bk ↔ (∀ c, c ≠ cstar → gBlockSat a (Bk c)) ∧ gBlockSat a (Bk cstar) := by
  constructor
  · intro h
    exact ⟨fun c _ => h c, h cstar⟩
  · rintro ⟨h1, h2⟩ c
    by_cases hc : c = cstar
    · rw [hc]; exact h2
    · exact h1 c hc

theorem not_gBlockSat_iff (a : Fin v → ZMod 2) (T : Finset (GLit v)) :
    ¬ gBlockSat a T ↔ ∀ ℓ ∈ T, ¬ gLitHolds a ℓ := by
  constructor
  · intro h ℓ hℓ hlit
    exact h ⟨ℓ, hℓ, hlit⟩
  · rintro h ⟨ℓ, hℓ, hlit⟩
    exact h ℓ hℓ hlit

theorem gCount_split (Bk : Fin m → Finset (GLit v)) (cstar : Fin m) :
    (Finset.univ.filter (fun a => gInstSat a Bk)).card
      + (Finset.univ.filter (fun a =>
          (∀ c, c ≠ cstar → gBlockSat a (Bk c))
          ∧ ∀ ℓ ∈ Bk cstar, ¬ gLitHolds a ℓ)).card
    = (Finset.univ.filter (fun a => ∀ c, c ≠ cstar → gBlockSat a (Bk c))).card := by
  classical
  have hcover := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ∀ c, c ≠ cstar → gBlockSat a (Bk c)))
    (p := fun a => gBlockSat a (Bk cstar))
  rw [Finset.filter_filter, Finset.filter_filter] at hcover
  have h1 : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → gBlockSat a (Bk c)) ∧ gBlockSat a (Bk cstar))
      = Finset.univ.filter (fun a => gInstSat a Bk) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (gInstSat_split Bk cstar a).symm
  have h2 : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → gBlockSat a (Bk c)) ∧ ¬ gBlockSat a (Bk cstar))
      = Finset.univ.filter (fun a =>
      (∀ c, c ≠ cstar → gBlockSat a (Bk c)) ∧ ∀ ℓ ∈ Bk cstar, ¬ gLitHolds a ℓ) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_right (fun _ => not_gBlockSat_iff a (Bk cstar))
  rw [h1, h2] at hcover
  exact hcover

set_option maxHeartbeats 1600000 in
/-- **THE QUADRATIC TWO-POINT (proved)**: origin-pinned witness `{0, w}`; shared/off-target
literals invisible between `0` and `w`; target the quadratic monomial `[a_i·a_j = 1]`,
false at `0` and TRUE at `w` (`w_i·w_j = 1`).  Then the two rows' family parities DIFFER. -/
theorem quad_two_point (Bk Bk' : Fin m → Finset (GLit v)) (cstar : Fin m)
    (Tsh Tt Tt' : Finset (GLit v))
    (w : Fin v → ZMod 2) (i j : Fin v)
    (hqw : w i * w j = 1)
    (hT : Bk cstar = Tsh ∪ Tt)
    (hT' : Bk' cstar = Tsh ∪ Tt')
    (htar' : GLit.quad i j 1 ∈ Tt')
    (h0t : ∀ ℓ ∈ Tt, ¬ gLitHolds 0 ℓ)
    (h0t' : ∀ ℓ ∈ Tt', ¬ gLitHolds 0 ℓ)
    (hkert : ∀ ℓ ∈ Tt, gLitHolds 0 ℓ ↔ gLitHolds w ℓ)
    (hnt : ∀ a : Fin v → ZMod 2,
      (∀ c, c ≠ cstar → gBlockSat a (Bk c)) ↔ (∀ c, c ≠ cstar → gBlockSat a (Bk' c)))
    (hpair : ∀ a : Fin v → ZMod 2,
      ((∀ c, c ≠ cstar → gBlockSat a (Bk c)) ∧ ∀ ℓ ∈ Tsh, ¬ gLitHolds a ℓ)
        ↔ (a = 0 ∨ a = w)) :
    gParityFamily Bk ≠ gParityFamily Bk' := by
  classical
  have hwne : w ≠ 0 := by
    intro hw0
    have h := hqw
    rw [hw0] at h
    simp only [Pi.zero_apply, mul_zero] at h
    exact absurd h (by decide)
  have hne : (0 : Fin v → ZMod 2) ≠ w := fun h => hwne h.symm
  have htarw : gLitHolds w (GLit.quad i j 1) := hqw
  have hp0 := (hpair 0).mpr (Or.inl rfl)
  have hpw := (hpair w).mpr (Or.inr rfl)
  have hsplit := gCount_split Bk cstar
  have hsplit' := gCount_split Bk' cstar
  -- the Z-set of the target-free row is the full pair {0, w}
  have hZ : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → gBlockSat a (Bk c)) ∧ ∀ ℓ ∈ Bk cstar, ¬ gLitHolds a ℓ)
      = {0, w} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hnta, hall⟩
      apply (hpair a).mp
      refine ⟨hnta, ?_⟩
      intro ℓ hℓ
      apply hall
      rw [hT]
      exact Finset.mem_union_left _ hℓ
    · rintro (rfl | rfl)
      · refine ⟨hp0.1, ?_⟩
        intro ℓ hℓ
        rw [hT] at hℓ
        rcases Finset.mem_union.mp hℓ with h | h
        · exact hp0.2 ℓ h
        · exact h0t ℓ h
      · refine ⟨hpw.1, ?_⟩
        intro ℓ hℓ
        rw [hT] at hℓ
        rcases Finset.mem_union.mp hℓ with h | h
        · exact hpw.2 ℓ h
        · intro hlit
          exact h0t ℓ h ((hkert ℓ h).mpr hlit)
  -- the Z-set of the target-carrying row is the single base point {0}
  have hZ' : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → gBlockSat a (Bk' c)) ∧ ∀ ℓ ∈ Bk' cstar, ¬ gLitHolds a ℓ)
      = {0} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hnta, hall⟩
      have hTsh : ∀ ℓ ∈ Tsh, ¬ gLitHolds a ℓ := by
        intro ℓ hℓ
        apply hall
        rw [hT']
        exact Finset.mem_union_left _ hℓ
      rcases (hpair a).mp ⟨(hnt a).mpr hnta, hTsh⟩ with h | h
      · exact h
      · exfalso
        apply hall (GLit.quad i j 1) (by rw [hT']; exact Finset.mem_union_right _ htar')
        rw [h]
        exact htarw
    · rintro rfl
      refine ⟨(hnt _).mp hp0.1, ?_⟩
      intro ℓ hℓ
      rw [hT'] at hℓ
      rcases Finset.mem_union.mp hℓ with h | h
      · exact hp0.2 ℓ h
      · exact h0t' ℓ h
  have hcard2 : ({0, w} : Finset (Fin v → ZMod 2)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hcard1 : ({0} : Finset (Fin v → ZMod 2)).card = 1 := Finset.card_singleton _
  rw [hZ, hcard2] at hsplit
  rw [hZ', hcard1] at hsplit'
  have hNTeq : (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ∀ c, c ≠ cstar → gBlockSat a (Bk c))).card
      = (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ∀ c, c ≠ cstar → gBlockSat a (Bk' c))).card := by
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hnt a
  intro heq
  unfold gParityFamily at heq
  have hiff := decide_eq_decide.mp heq
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint.gCount_split
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint.quad_two_point
