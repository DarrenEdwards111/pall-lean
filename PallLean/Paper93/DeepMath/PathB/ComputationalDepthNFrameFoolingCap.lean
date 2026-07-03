import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameJointCoherence

/-!
# N-Frame: the fooling cap — multi-bit fooling families are impossible beyond `2N`

The sharpened core asked for superpolynomially many mutually non-corectangular SAT boundary pairs.  The attack
answers it **negatively, with a theorem**.

**The normal form (proved).**  Over Booleans, the four cross-difference conditions at a coordinate collapse to
`x_s i = x_t i ∧ y_s i = y_t i ∧ x_s i ≠ y_s i` (`kw_four_iff`): two pairs violate fooling at `i` exactly when
their crossing patterns *agree* there.

**The cap (proved).**  Hence in a fooling family each (coordinate, value) slot is used by at most one member: pick
any crossing coordinate of each pair and its `x`-value — the resulting map into `Fin n × Bool` is injective
(`kwFooling_card_le`):

    `KWFooling T → T.card ≤ 2n.`

**Multi-bit difference sets cannot help**: larger crossing sets only occupy *more* slots.  The `m·v ≈ N/3` selector
family already built is within a factor `6` of the absolute optimum — the fooling-set method for the SAT boundary
game is **exhausted, provably**, at the linear scale.

## Honest scope — the method ladder, fully audited

Every elementary cover lower-bound tool is now formally capped for this game: fooling `≤ 2N` (this file, an
impossibility theorem, not a failure of imagination); product/area/Khrapchenko measures `≤ ~N` on sat3's thin
boundary (proved earlier); one-sided and two-sided diversity measures die at aligned leaves (proved earlier).
A superpolynomial `χ(sat3)` therefore requires cover lower bounds *beyond all slot-counting and measure arguments* —
genuinely non-elementary methods (KRW-style inductive/lifting machinery).  That is the surviving wall, now with a
formally verified perimeter.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **The Boolean normal form (proved)**: the four cross-difference conditions collapse to agreement of crossing
patterns. -/
theorem kw_four_iff (a b a' b' : Bool) :
    (a ≠ b ∧ a ≠ b' ∧ a' ≠ b ∧ a' ≠ b') ↔ (a = a' ∧ b = b' ∧ a ≠ b) := by
  cases a <;> cases b <;> cases a' <;> cases b' <;> decide

theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b
  · exact absurd rfl h
  · rfl
  · rfl
  · exact absurd rfl h

/-- **THE FOOLING CAP (proved)**: any fooling family of genuinely differing pairs has at most `2n` members —
each (coordinate, value) slot serves at most one member's crossing pattern.  Multi-bit difference sets cannot
help; the fooling-set method is exhausted at the linear scale. -/
theorem kwFooling_card_le {n : ℕ} (T : Finset ((Fin n → Bool) × (Fin n → Bool)))
    (hfool : KWFooling T) (hdiff : ∀ e ∈ T, e.1 ≠ e.2) :
    T.card ≤ 2 * n := by
  by_cases hT : T = ∅
  · rw [hT, Finset.card_empty]
    exact Nat.zero_le _
  · obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    obtain ⟨i₀, -⟩ := Function.ne_iff.mp (hdiff e₀ he₀)
    -- pick a crossing coordinate and its x-value for each member
    set f : (Fin n → Bool) × (Fin n → Bool) → Fin n × Bool := fun e =>
      if h : e.1 ≠ e.2 then
        (Classical.choose (Function.ne_iff.mp h),
          e.1 (Classical.choose (Function.ne_iff.mp h)))
      else (i₀, true) with hf
    have hinj : Set.InjOn f T := by
      intro e he e' he' hfeq
      have hfe : f e = (Classical.choose (Function.ne_iff.mp (hdiff e he)),
          e.1 (Classical.choose (Function.ne_iff.mp (hdiff e he)))) := by
        rw [hf]
        show (if h : e.1 ≠ e.2 then _ else _) = _
        rw [dif_pos (hdiff e he)]
      have hfe' : f e' = (Classical.choose (Function.ne_iff.mp (hdiff e' he')),
          e'.1 (Classical.choose (Function.ne_iff.mp (hdiff e' he')))) := by
        rw [hf]
        show (if h : e'.1 ≠ e'.2 then _ else _) = _
        rw [dif_pos (hdiff e' he')]
      have hfeq' : (Classical.choose (Function.ne_iff.mp (hdiff e he)),
            e.1 (Classical.choose (Function.ne_iff.mp (hdiff e he))))
          = (Classical.choose (Function.ne_iff.mp (hdiff e' he')),
            e'.1 (Classical.choose (Function.ne_iff.mp (hdiff e' he')))) := by
        rw [← hfe, ← hfe']
        exact hfeq
      rw [Prod.mk.injEq] at hfeq'
      obtain ⟨hi, hv⟩ := hfeq'
      set i : Fin n := Classical.choose (Function.ne_iff.mp (hdiff e he)) with hidef
      have hspec_e : e.1 i ≠ e.2 i :=
        Classical.choose_spec (Function.ne_iff.mp (hdiff e he))
      have hspec_e' : e'.1 i ≠ e'.2 i := by
        rw [hi]
        exact Classical.choose_spec (Function.ne_iff.mp (hdiff e' he'))
      have hval : e.1 i = e'.1 i := by
        rw [hv, ← hi]
      by_contra hne
      -- the four conditions hold at i: fooling violated
      apply hfool e he e' he' hne i
      have h2 : e.2 i = !(e.1 i) := bool_eq_not_of_ne hspec_e
      have h2' : e'.2 i = !(e'.1 i) := bool_eq_not_of_ne hspec_e'
      refine ⟨hspec_e, ?_, ?_, hspec_e'⟩
      · rw [h2', ← hval]
        cases e.1 i <;> decide
      · rw [h2, hval]
        cases e'.1 i <;> decide
    have hmaps : ∀ e ∈ T, f e ∈ (Finset.univ : Finset (Fin n × Bool)) :=
      fun e _ => Finset.mem_univ _
    have hcard := Finset.card_le_card_of_injOn f hmaps hinj
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hcard
    omega

/-- **Near-optimality of the selector family (proved)**: the proven `m·v` fooling family sits within a constant
factor of the absolute `2N` cap — the method's yield for sat3 is settled up to constants. -/
theorem sat3_fooling_near_optimal (N : ℕ) (hv : 1 ≤ sat3V N) :
    ∃ T : Finset ((Fin N → Bool) × (Fin N → Bool)),
      KWFooling T ∧ sat3M N * sat3V N ≤ T.card ∧ T.card ≤ 2 * N := by
  obtain ⟨T, hfool, hval, hcard⟩ := sat3_fooling N hv
  refine ⟨T, hfool, hcard, kwFooling_card_le T hfool ?_⟩
  intro e he
  intro hcc
  have h1 := (hval e he).1
  rw [hcc, (hval e he).2] at h1
  exact Bool.noConfusion h1

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kw_four_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwFooling_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_fooling_near_optimal
