import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityEval

/-!
# N-Frame: the parity two-point comparison — multi-difference detection

Rung 28a of the arc (… → parity probe → **two-point comparison**).  The capacity argument
feeds `cut_row_capacity` a PRODUCT family of tuples, whose pairs differ at MANY positions —
rung 24's single-insert detection does not apply.  The pressure-test produced the fix, and it
is simpler than the single-insert form: with pins plus the SHARED target content cutting the
witness space to exactly `{a₀, a₀ + w}`, every tuple literal false at `a₀`, and every
non-target tuple literal `w`-kernel, the all-false count over the two points is `2` for the
row without the target literal and `1` for the row with it:

    Z(Bk)  = [all false at a₀] + [all false at a₀+w] = 1 + 1 = 2   (kernel literals are
             invisible at a₀+w: their value there equals their value at a₀),
    Z(Bk') = 1 + 0                                                  (the target literal is
             TRUE at a₀+w: `⟨l, a₀+w⟩ = ⟨l, a₀⟩ + 1 = (b+1)+1 = b`),

so `#sat = #nonTarget − Z` differ by one — **the parities differ REGARDLESS of the non-target
count's parity: `heven` drops out of the capacity chain entirely.**  Differences at OTHER
data blocks are kit-absorbed (their non-target predicates agree — the `hnt` hypothesis);
differences at the target block beyond the target literal are kernel-invisible.

  `parity_two_point` — **PROVED**: the two-point comparison; `parityFamily Bk ≠
        parityFamily Bk'` for any pair with the package, however many positions differ.

## Honest scope

Semantic level.  What remains: (28b) the layout-level transfer for tuple families (decode of
multi-difference mixes) and the capacity feed (`cut_row_capacity`, f-generic), and (28c) the
supply counting under an adversarial balanced cut — per-pair `w`/`a₀`/pins/shared-scaffold
packages from kill-cost liveness, per-block transversal independence, and the expander-affine
codebook.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityTwoPoint

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval

variable {v m : ℕ}

set_option maxHeartbeats 1600000 in
/-- **THE TWO-POINT COMPARISON (proved)**: pins + shared target content cut the witness space
to `{a₀, a₀ + w}`; tuple literals are false at `a₀` and (off-target) `w`-kernel; then the two
rows' family values DIFFER — however many positions differ, and with no evenness hypothesis. -/
theorem parity_two_point (Bk Bk' : Fin m → Finset (Lit v)) (cstar : Fin m)
    (Tsh Tt Tt' : Finset (Lit v))
    (w a₀ l : Fin v → ZMod 2) (b : ZMod 2)
    (hlw : dotp l w = 1)
    (hT : Bk cstar = Tsh ∪ Tt)
    (hT' : Bk' cstar = Tsh ∪ Tt')
    (htar' : (l, b) ∈ Tt')
    (h0t : ∀ ℓ ∈ Tt, ¬ litHolds a₀ ℓ)
    (h0t' : ∀ ℓ ∈ Tt', ¬ litHolds a₀ ℓ)
    (hkert : ∀ ℓ ∈ Tt, dotp ℓ.1 w = 0)
    (hnt : ∀ a : Fin v → ZMod 2,
      (∀ c, c ≠ cstar → blockSat a (Bk c)) ↔ (∀ c, c ≠ cstar → blockSat a (Bk' c)))
    (hpair : ∀ a : Fin v → ZMod 2,
      ((∀ c, c ≠ cstar → blockSat a (Bk c)) ∧ ∀ ℓ ∈ Tsh, ¬ litHolds a ℓ)
        ↔ (a = a₀ ∨ a = a₀ + w)) :
    parityFamily Bk ≠ parityFamily Bk' := by
  classical
  have hne2 : ∀ x y : ZMod 2, ¬ x = y ↔ x = y + 1 := by decide
  have hwne : w ≠ 0 := by
    intro hw0
    rw [hw0] at hlw
    have hd0 : dotp l (0 : Fin v → ZMod 2) = 0 := by
      unfold dotp
      simp
    rw [hd0] at hlw
    exact absurd hlw (by decide)
  have hne : a₀ ≠ a₀ + w := by
    intro hc
    have hc' : a₀ + 0 = a₀ + w := by
      rw [add_zero]
      exact hc
    exact hwne (add_left_cancel hc').symm
  have hp0 := (hpair a₀).mpr (Or.inl rfl)
  have hpw := (hpair (a₀ + w)).mpr (Or.inr rfl)
  -- the target literal holds at a₀ + w
  have htarw : litHolds (a₀ + w) (l, b) := by
    show dotp l (a₀ + w) = b
    rw [dotp_add_right, hlw]
    have h0 : ¬ dotp l a₀ = b := h0t' (l, b) htar'
    have h1 : dotp l a₀ = b + 1 := (hne2 _ _).mp h0
    rw [h1]
    have h2 : ∀ x : ZMod 2, x + 1 + 1 = x := by decide
    exact h2 b
  -- the F = Z reductions
  have hsplit := count_split Bk cstar
  have hsplit' := count_split Bk' cstar
  -- the Z-set of the target-free row is the full pair
  have hZ : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → blockSat a (Bk c)) ∧ ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ)
      = {a₀, a₀ + w} := by
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
        · show ¬ dotp ℓ.1 (a₀ + w) = ℓ.2
          rw [dotp_add_right, hkert ℓ h, add_zero]
          exact h0t ℓ h
  -- the Z-set of the target-carrying row is the single base point
  have hZ' : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → blockSat a (Bk' c)) ∧ ∀ ℓ ∈ Bk' cstar, ¬ litHolds a ℓ)
      = {a₀} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hnta, hall⟩
      have hTsh : ∀ ℓ ∈ Tsh, ¬ litHolds a ℓ := by
        intro ℓ hℓ
        apply hall
        rw [hT']
        exact Finset.mem_union_left _ hℓ
      rcases (hpair a).mp ⟨(hnt a).mpr hnta, hTsh⟩ with h | h
      · exact h
      · exfalso
        apply hall (l, b) (by rw [hT']; exact Finset.mem_union_right _ htar')
        rw [h]
        exact htarw
    · rintro rfl
      refine ⟨(hnt _).mp hp0.1, ?_⟩
      intro ℓ hℓ
      rw [hT'] at hℓ
      rcases Finset.mem_union.mp hℓ with h | h
      · exact hp0.2 ℓ h
      · exact h0t' ℓ h
  have hcard2 : ({a₀, a₀ + w} : Finset (Fin v → ZMod 2)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hcard1 : ({a₀} : Finset (Fin v → ZMod 2)).card = 1 :=
    Finset.card_singleton _
  rw [hZ, hcard2] at hsplit
  rw [hZ', hcard1] at hsplit'
  -- the non-target counts agree
  have hNTeq : (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ∀ c, c ≠ cstar → blockSat a (Bk c))).card
      = (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ∀ c, c ≠ cstar → blockSat a (Bk' c))).card := by
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hnt a
  -- the parities differ
  intro heq
  unfold parityFamily at heq
  have hiff := decide_eq_decide.mp heq
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameParityTwoPoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityTwoPoint.parity_two_point
