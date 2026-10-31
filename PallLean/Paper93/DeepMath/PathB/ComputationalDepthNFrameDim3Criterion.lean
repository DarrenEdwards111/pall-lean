import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameW2MajImpossible

/-!
# N-Frame: the dimension-3 criterion — hyperplane-nonaffine functions, characterized

The majority impossibility used majority only through one property: a threshold square with odd second difference
exists inside **every** hyperplane.  This file extracts that as the general criterion and proves the
characterization-grade theorem:

  `HyperplaneSquares f` — in every hyperplane `{x : x w = a}` there is a 2×2 square on which `f`'s second difference is
        odd (`xor` of the four corners is `true`).
  `affine_square_clash'` — **PROVED**: no fixed affine value can realize an odd square (the general clash).
  `w2_impossible_of_hyperplaneSquares` — **PROVED**: no one-bit-register program computes any `HyperplaneSquares`
        function — at any length.
  `needs_dim_three_of_hyperplaneSquares` / `boundaryDim_eq_three_of_hyperplaneSquares` — **PROVED**: every such
        function has boundary dimension **exactly 3**.
  `majFn_hyperplaneSquares` — **PROVED**: majority satisfies the criterion (the threshold square).

The criterion is honest about its boundary: functions affine on *some* hyperplane escape it — correctly so, since e.g.
`AND` is affine on `{x₀ = 0}` and is genuinely dimension-2 computable (the caterpillar).  The criterion is thus tight in
kind: it captures exactly the obstruction dimension-2 observers face.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-- **The criterion**: in every hyperplane `{x : x w = a}` there is a square on which `f`'s second difference is odd. -/
def HyperplaneSquares (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ (w : Fin n) (a : Bool), ∃ (z : Fin n → Bool) (i₁ i₂ : Fin n),
    i₁ ≠ i₂ ∧ i₁ ≠ w ∧ i₂ ≠ w ∧ z w = a ∧
    xor (xor (f z) (f (Function.update z i₁ true)))
      (xor (f (Function.update z i₂ true))
        (f (Function.update (Function.update z i₁ true) i₂ true))) = true

/-- **The general clash (proved)**: a fixed affine value cannot realize an odd square. -/
theorem affine_square_clash' (g : W2Prog n) (c0 : Bool) (z : Fin n → Bool) (i₁ i₂ : Fin n)
    (hij : i₁ ≠ i₂)
    (hodd : xor (xor (xor c0 (progPar g z)) (xor c0 (progPar g (Function.update z i₁ true))))
      (xor (xor c0 (progPar g (Function.update z i₂ true)))
        (xor c0 (progPar g (Function.update (Function.update z i₁ true) i₂ true)))) = true) :
    False := by
  have hsq := progPar_square g z i₁ i₂ hij
  generalize progPar g z = b1 at hodd hsq
  generalize progPar g (Function.update z i₁ true) = b2 at hodd hsq
  generalize progPar g (Function.update z i₂ true) = b3 at hodd hsq
  generalize progPar g (Function.update (Function.update z i₁ true) i₂ true) = b4 at hodd hsq
  cases c0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    first
      | exact Bool.noConfusion hodd
      | exact Bool.noConfusion hsq

/-- **The general impossibility (proved)**: no one-bit-register program computes a `HyperplaneSquares` function — at
any length. -/
theorem w2_impossible_of_hyperplaneSquares (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (hsq : HyperplaneSquares f) (r0 : Bool) (p : W2Prog n) :
    ¬ ∀ x, w2run p r0 x = f x := by
  intro hcomp
  rcases last_globally_active_split p with hall | ⟨p₁, s, p₂, heq, ⟨xw, hxw⟩, hpass⟩
  · -- globally affine
    obtain ⟨z, i₁, i₂, hij, -, -, -, hodd⟩ := hsq ⟨0, hn⟩ false
    have f00 := (hcomp z).symm.trans (w2run_allPassive p z (hall z) r0)
    have f10 := (hcomp (Function.update z i₁ true)).symm.trans
      (w2run_allPassive p (Function.update z i₁ true) (hall _) r0)
    have f01 := (hcomp (Function.update z i₂ true)).symm.trans
      (w2run_allPassive p (Function.update z i₂ true) (hall _) r0)
    have f11 := (hcomp (Function.update (Function.update z i₁ true) i₂ true)).symm.trans
      (w2run_allPassive p (Function.update (Function.update z i₁ true) i₂ true) (hall _) r0)
    rw [f00, f10, f01, f11] at hodd
    exact affine_square_clash' p r0 z i₁ i₂ hij hodd
  · -- affine on the last-activation hyperplane
    obtain ⟨z, i₁, i₂, hij, h1w, h2w, hzw, hodd⟩ := hsq s.2 (xw s.2)
    have hzw10 : Function.update z i₁ true s.2 = xw s.2 := by
      rw [Function.update_of_ne (fun hc => h1w hc.symm)]
      exact hzw
    have hzw01 : Function.update z i₂ true s.2 = xw s.2 := by
      rw [Function.update_of_ne (fun hc => h2w hc.symm)]
      exact hzw
    have hzw11 : Function.update (Function.update z i₁ true) i₂ true s.2 = xw s.2 := by
      rw [Function.update_of_ne (fun hc => h2w hc.symm)]
      exact hzw10
    have hrun : ∀ y : Fin n → Bool, y s.2 = xw s.2 →
        w2run p r0 y = xor (s.1 false (xw s.2)) (progPar p₂ y) := by
      intro y hy
      have hact : stepActive s y := (stepActive_congr s y xw hy).mpr hxw
      rw [heq, w2run_after_active p₁ s p₂ y hact (fun s' hs' => hpass y s' hs') r0, hy]
    have f00 := (hcomp z).symm.trans (hrun z hzw)
    have f10 := (hcomp (Function.update z i₁ true)).symm.trans
      (hrun (Function.update z i₁ true) hzw10)
    have f01 := (hcomp (Function.update z i₂ true)).symm.trans
      (hrun (Function.update z i₂ true) hzw01)
    have f11 := (hcomp (Function.update (Function.update z i₁ true) i₂ true)).symm.trans
      (hrun (Function.update (Function.update z i₁ true) i₂ true) hzw11)
    rw [f00, f10, f01, f11] at hodd
    exact affine_square_clash' p₂ (s.1 false (xw s.2)) z i₁ i₂ hij hodd

/-- **The dimension bound (proved)**: every `HyperplaneSquares` function needs dimension `≥ 3`. -/
theorem needs_dim_three_of_hyperplaneSquares (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (hsq : HyperplaneSquares f) (t : Trans n) (hcomp : eval t = f) :
    3 ≤ width t := by
  by_contra h
  push_neg at h
  obtain ⟨r0, q, hlen, hrun⟩ := w2_correspondence hn t (by omega)
  exact w2_impossible_of_hyperplaneSquares hn f hsq r0 q (fun x => by rw [hrun x, hcomp])

/-- **The characterization-grade headline (proved)**: every `HyperplaneSquares` function has boundary dimension
**exactly 3**. -/
theorem boundaryDim_eq_three_of_hyperplaneSquares (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (hsq : HyperplaneSquares f) :
    boundaryDim f = 3 := by
  have hle := boundaryDim_le_three f
  have hne : {w | ∃ t : Trans n, eval t = f ∧ width t = w}.Nonempty :=
    ⟨width (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, ht, hwidth⟩ := Nat.sInf_mem hne
  have h3 := needs_dim_three_of_hyperplaneSquares hn f hsq t ht
  unfold boundaryDim at hle ⊢
  omega

/-- **Majority satisfies the criterion (proved)** — the threshold square in every hyperplane. -/
theorem majFn_hyperplaneSquares (hn : 5 ≤ n) : HyperplaneSquares (majFn n) := by
  intro w a
  obtain ⟨z, i₁, i₂, hij, h1w, h2w, hzw, h1, h2, hcount⟩ := exists_threshold_square hn w a
  refine ⟨z, i₁, i₂, hij, h1w, h2w, hzw, ?_⟩
  have c10 : (onesOf (Function.update z i₁ true)).card = (n + 1) / 2 - 1 := by
    rw [card_onesOf_update_true z i₁ h1, hcount]
    omega
  have c01 : (onesOf (Function.update z i₂ true)).card = (n + 1) / 2 - 1 := by
    rw [card_onesOf_update_true z i₂ h2, hcount]
    omega
  have c11 : (onesOf (Function.update (Function.update z i₁ true) i₂ true)).card
      = (n + 1) / 2 := by
    rw [card_onesOf_update_true _ i₂ (by
      rw [Function.update_of_ne (fun hc => hij hc.symm)]
      exact h2), c10]
    omega
  have m00 : majFn n z = false := by
    rw [majFn_eq_decide, hcount]
    simp only [decide_eq_false_iff_not]
    omega
  have m10 : majFn n (Function.update z i₁ true) = false := by
    rw [majFn_eq_decide, c10]
    simp only [decide_eq_false_iff_not]
    omega
  have m01 : majFn n (Function.update z i₂ true) = false := by
    rw [majFn_eq_decide, c01]
    simp only [decide_eq_false_iff_not]
    omega
  have m11 : majFn n (Function.update (Function.update z i₁ true) i₂ true) = true := by
    rw [majFn_eq_decide, c11]
    simp
  rw [m00, m10, m01, m11]
  rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2_impossible_of_hyperplaneSquares
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boundaryDim_eq_three_of_hyperplaneSquares
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majFn_hyperplaneSquares
