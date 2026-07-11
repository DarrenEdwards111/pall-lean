import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFpANDOR

/-!
# Razborov–Smolensky amplification: from per-input to a `1 - p^{-t}` bound

`NFrameFpANDOR` proved that for *every* input to an OR gate there is a weight vector `w` making the single
linear form `(Σᵢ wᵢ zᵢ)^{p-1}` compute OR correctly — but the good `w` depended on the input.  This file supplies
the **amplification**: a *fixed* choice of `t` weight vectors whose degree-`(p-1)·t` polynomial computes OR
correctly on a `1 - p^{-t}` fraction of inputs.

Two ingredients:

* `amplify` — the **abstract averaging lemma** (the probabilistic method).  If for every input `z` the "bad"
  weights are at most a `1/p` fraction (`p · #bad ≤ #Ω`), then some `t`-tuple `W : Fin t → Ω` has at most a
  `p^{-t}` fraction of inputs on which *all* `t` coordinates are bad: `p^t · #{z : ∀ j, bad (W j) z} ≤ #I`.
  Proof: double-count, bound each input's bad-`W` count by `(#Ω/p)^t`, and take a `W` below the average.
* `linForm_fiber_bound` — the **per-input `1/p` bound** for the OR linear form: for `z` with a `1`, the weights
  killing `Σᵢ wᵢ zᵢ` are at most `p^{k-1}` (`p · # ≤ p^k`), because translating by a fixed vector injects the
  zero-fibre into every other fibre (`linForm` is additive).

Combined (`or_amplified_error_bound`): there is `W : Fin t → (Fin k → ZMod p)` with
`p^t · #{z : ORb z ∧ ∀ j, (Σᵢ (W j)ᵢ zᵢ) = 0} ≤ 2^k` — the amplified error set is a `≤ p^{-t}` fraction.  And
`orAmp_totalDegree_le` shows the amplifying polynomial `1 - ∏ⱼ(1 - formⱼ^{p-1})` has total degree `≤ (p-1)·t`.

So OR (and dually AND) has an `F_p` polynomial of degree `(p-1)·t` and error `≤ p^{-t}` — the genuine
approximate-degree bound, degree independent of fan-in.  This is the last piece of the ACC-upper side of the
degree dynamic-SPDP for a single prime `p`; composite MOD ("Wall 1") remains the untouched obstruction.

## Honest scope

The Razborov–Smolensky averaging/amplification for the OR linear form: an existential `1 - p^{-t}`
approximate-degree bound at degree `(p-1)·t`.  No composite-MOD lower bound, no ACC⁰ lower bound.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFpAmplify

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.NFrameFpDegree
open PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR

/-! ## The abstract averaging lemma -/

set_option maxHeartbeats 1000000 in
/-- **Amplification by averaging.**  If every input's bad-weight set is at most a `1/p` fraction of the weight
space, then some `t`-tuple of weights is bad (on all `t` coordinates) for at most a `p^{-t}` fraction of
inputs. -/
theorem amplify {I Ω : Type*} [Fintype I] [Fintype Ω] (p t : Nat)
    (bad : Ω → I → Prop) [∀ w z, Decidable (bad w z)] (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ z : I, p * (univ.filter (fun w => bad w z)).card ≤ Fintype.card Ω) :
    ∃ W : Fin t → Ω,
      p ^ t * (univ.filter (fun z => ∀ j, bad (W j) z)).card ≤ Fintype.card I := by
  have hA : ∀ z : I, (univ.filter (fun W : Fin t → Ω => ∀ j, bad (W j) z)).card
      = (univ.filter (fun w => bad w z)).card ^ t := by
    intro z
    have hpi : (univ.filter (fun W : Fin t → Ω => ∀ j, bad (W j) z))
        = Fintype.piFinset (fun _ : Fin t => univ.filter (fun w => bad w z)) := by
      ext W; simp [Fintype.mem_piFinset]
    rw [hpi, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hB : (∑ W : Fin t → Ω, (univ.filter (fun z => ∀ j, bad (W j) z)).card)
      = ∑ z : I, (univ.filter (fun w => bad w z)).card ^ t := by
    have hcomm : (∑ W : Fin t → Ω, (univ.filter (fun z => ∀ j, bad (W j) z)).card)
        = ∑ z : I, (univ.filter (fun W : Fin t → Ω => ∀ j, bad (W j) z)).card := by
      simp only [Finset.card_filter]; rw [Finset.sum_comm]
    rw [hcomm]; exact Finset.sum_congr rfl (fun z _ => hA z)
  have hD : p ^ t * (∑ z : I, (univ.filter (fun w => bad w z)).card ^ t)
      ≤ Fintype.card I * (Fintype.card Ω) ^ t := by
    rw [Finset.mul_sum]
    calc ∑ z : I, p ^ t * (univ.filter (fun w => bad w z)).card ^ t
        ≤ ∑ _z : I, (Fintype.card Ω) ^ t := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          rw [← mul_pow]
          exact Nat.pow_le_pow_left (hbound z) t
      _ = Fintype.card I * (Fintype.card Ω) ^ t := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  by_contra hcon
  push_neg at hcon
  have hsum : (Fintype.card Ω) ^ t * (Fintype.card I + 1)
      ≤ p ^ t * (∑ W : Fin t → Ω, (univ.filter (fun z => ∀ j, bad (W j) z)).card) := by
    calc (Fintype.card Ω) ^ t * (Fintype.card I + 1)
        = ∑ _W : Fin t → Ω, (Fintype.card I + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]
      _ ≤ ∑ W : Fin t → Ω, p ^ t * (univ.filter (fun z => ∀ j, bad (W j) z)).card :=
          Finset.sum_le_sum (fun W _ => hcon W)
      _ = p ^ t * ∑ W : Fin t → Ω, (univ.filter (fun z => ∀ j, bad (W j) z)).card := by
          rw [Finset.mul_sum]
  rw [hB] at hsum
  have hchain := le_trans hsum hD
  have hΩt : 1 ≤ (Fintype.card Ω) ^ t := Nat.one_le_pow _ _ hΩ
  have hexp : (Fintype.card Ω) ^ t * (Fintype.card I + 1)
      = (Fintype.card Ω) ^ t * Fintype.card I + (Fintype.card Ω) ^ t := by ring
  have hcomm : Fintype.card I * (Fintype.card Ω) ^ t
      = (Fintype.card Ω) ^ t * Fintype.card I := Nat.mul_comm _ _
  rw [hexp, hcomm] at hchain
  omega

/-! ## The per-input `1/p` bound for the OR linear form -/

section
variable (p : Nat) [Fact p.Prime]

/-- The linear form `Σᵢ wᵢ zᵢ` over `F_p`. -/
def linForm {k : Nat} (w : Fin k → ZMod p) (z : Fin k → Bool) : ZMod p :=
  ∑ i, w i * boolToZMod p (z i)

theorem linForm_add {k : Nat} (w w' : Fin k → ZMod p) (z : Fin k → Bool) :
    linForm p (w + w') z = linForm p w z + linForm p w' z := by
  simp only [linForm, Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]

/-- The single-coordinate form `Σᵢ δᵢ zᵢ` with `δ = v` at a `true` coordinate `j` equals `v`. -/
theorem linForm_single {k : Nat} (z : Fin k → Bool) (j : Fin k) (hj : z j = true) (v : ZMod p) :
    linForm p (fun i => if i = j then v else 0) z = v := by
  simp only [linForm]
  rw [Finset.sum_eq_single j]
  · simp [hj, boolToZMod]
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Translating by a fixed vector injects the zero-fibre of `linForm` into any other fibre. -/
theorem fiber_card_le {k : Nat} (z : Fin k → Bool) (j : Fin k) (hj : z j = true) (v : ZMod p) :
    (univ.filter (fun w : Fin k → ZMod p => linForm p w z = 0)).card
      ≤ (univ.filter (fun w : Fin k → ZMod p => linForm p w z = v)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun w => w + (fun i => if i = j then v else 0))
  · intro w hw
    have hw' : linForm p w z = 0 := (Finset.mem_filter.mp hw).2
    have hval : linForm p (w + (fun i => if i = j then v else 0)) z = v := by
      rw [linForm_add, hw', linForm_single p z j hj, zero_add]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval⟩
  · intro w1 _ w2 _ h
    exact add_right_cancel h

/-- **The per-input `1/p` bound.**  For `z` with a `1` at coordinate `j`, the weights killing `Σᵢ wᵢ zᵢ` are at
most a `1/p` fraction. -/
theorem linForm_fiber_bound {k : Nat} (z : Fin k → Bool) (j : Fin k) (hj : z j = true) :
    p * (univ.filter (fun w : Fin k → ZMod p => linForm p w z = 0)).card ≤ p ^ k := by
  classical
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hcard : (∑ v : ZMod p, (univ.filter (fun w : Fin k → ZMod p => linForm p w z = v)).card)
      = p ^ k := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin k → ZMod p))) (t := (Finset.univ : Finset (ZMod p)))
      (f := fun w => linForm p w z) (fun w _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h
    exact h.symm
  calc p * (univ.filter (fun w : Fin k → ZMod p => linForm p w z = 0)).card
      = ∑ _v : ZMod p, (univ.filter (fun w : Fin k → ZMod p => linForm p w z = 0)).card := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    _ ≤ ∑ v : ZMod p, (univ.filter (fun w : Fin k → ZMod p => linForm p w z = v)).card :=
        Finset.sum_le_sum (fun v _ => fiber_card_le p z j hj v)
    _ = p ^ k := hcard

/-! ## The OR amplification bound -/

/-- **Amplified OR error bound.**  There is a fixed `t`-tuple of weight vectors for which the amplified OR
detector fails (all `t` forms vanish on a `true` input) on at most a `p^{-t}` fraction of the `2^k` inputs. -/
theorem or_amplified_error_bound (t k : Nat) :
    ∃ W : Fin t → (Fin k → ZMod p),
      p ^ t * (univ.filter
        (fun z : Fin k → Bool => ∀ j, ORb z = true ∧ linForm p (W j) z = 0)).card ≤ 2 ^ k := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hΩ : 0 < Fintype.card (Fin k → ZMod p) := Fintype.card_pos
  obtain ⟨W, hW⟩ := amplify (I := Fin k → Bool) (Ω := Fin k → ZMod p) p t
    (fun w z => ORb z = true ∧ linForm p w z = 0) hΩ (by
      intro z
      show p * (univ.filter (fun w : Fin k → ZMod p => ORb z = true ∧ linForm p w z = 0)).card
        ≤ Fintype.card (Fin k → ZMod p)
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
      by_cases hz : ORb z = true
      · obtain ⟨j, hj⟩ : ∃ j, z j = true := by
          simpa only [ORb, decide_eq_true_eq] using hz
        have hfe : (univ.filter (fun w : Fin k → ZMod p => ORb z = true ∧ linForm p w z = 0))
            = (univ.filter (fun w : Fin k → ZMod p => linForm p w z = 0)) := by
          apply Finset.filter_congr; intro w _; simp [hz]
        rw [hfe]
        exact linForm_fiber_bound p z j hj
      · have hfe : (univ.filter (fun w : Fin k → ZMod p => ORb z = true ∧ linForm p w z = 0)) = ∅ := by
          apply Finset.filter_false_of_mem; intro w _; simp [hz]
        rw [hfe]; simp)
  refine ⟨W, ?_⟩
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hW

/-! ## The amplifying polynomial has degree `(p-1)·t` -/

/-- The amplifying polynomial `1 - ∏ⱼ (1 - (Σᵢ C(Wⱼᵢ)·Xᵢ)^{p-1})`. -/
noncomputable def orAmp {t k : Nat} (W : Fin t → (Fin k → ZMod p)) : MvPolynomial (Fin k) (ZMod p) :=
  1 - ∏ j, (1 - (∑ i, C (W j i) * X i) ^ (p - 1))

/-- **The amplifying polynomial has total degree `≤ (p-1)·t`** — degree grows by `p-1` per amplification round,
independent of fan-in. -/
theorem orAmp_totalDegree_le {t k : Nat} (W : Fin t → (Fin k → ZMod p)) :
    (orAmp p W).totalDegree ≤ (p - 1) * t := by
  rw [orAmp]
  refine le_trans (MvPolynomial.totalDegree_sub _ _)
    (max_le (by rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _) ?_)
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  calc ∑ j : Fin t, (1 - (∑ i, C (W j i) * X i) ^ (p - 1)).totalDegree
      ≤ ∑ _j : Fin t, (p - 1) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        refine le_trans (MvPolynomial.totalDegree_sub _ _)
          (max_le (by rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _) ?_)
        refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
        have hs : (∑ i, C (W j i) * X i : MvPolynomial (Fin k) (ZMod p)).totalDegree ≤ 1 := by
          refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le ?_)
          intro i _
          refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
          rw [MvPolynomial.totalDegree_C, zero_add]
          exact le_of_eq (MvPolynomial.totalDegree_X i)
        calc (p - 1) * (∑ i, C (W j i) * X i : MvPolynomial (Fin k) (ZMod p)).totalDegree
            ≤ (p - 1) * 1 := Nat.mul_le_mul (le_refl _) hs
          _ = p - 1 := Nat.mul_one _
    _ = (p - 1) * t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

end

end PallLean.Paper93.DeepMath.PathB.NFrameFpAmplify

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpAmplify.amplify
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpAmplify.linForm_fiber_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpAmplify.or_amplified_error_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpAmplify.orAmp_totalDegree_le
