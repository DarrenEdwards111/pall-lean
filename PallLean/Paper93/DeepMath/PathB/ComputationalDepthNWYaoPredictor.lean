import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWHybridInstance

/-!
# Socket-2 (IKW): Yao's next-bit conversion

Rung 9 showed consecutive NW hybrids differ in exactly one coordinate `j`, whose value flips between a fresh uniform bit
and the generator's bit `nwGen f z (poly j)`.  Yao's theorem converts a distinguisher of that single-coordinate step into
a **next-bit predictor**: something that, given the other coordinates, guesses the target bit better than chance.  This
file proves Yao's identity — the genuine probabilistic core — in the finite `Prob` framework.

Model the step abstractly: `E : Ω → Bool → Bool` is the distinguisher with the target coordinate *plugged* by a bit
(`E ω b` = "accept, when the target bit is `b` and the other coordinates come from the sample `ω`"), and `g : Ω → Bool` is
the generator's true bit.  Then:

  `accGen E g` — acceptance probability on the *real* generator bit (`= distinguish` on the generator-side hybrid).
  `accUnif E` — acceptance probability on a *uniform* target bit (`= distinguish` on the uniform-side hybrid).
  `yaoPredict` / `predSucc` — the predictor "echo the guess iff `E` accepts", and its success probability over a uniform
        guess bit.
  `yao_identity` — **PROVED, Yao's next-bit identity**: `predSucc E g = 1/2 + (accGen E g - accUnif E)`.  A distinguishing
        gap of `δ` becomes prediction *exactly* `δ` above chance.
  `yao_two_sided` — **PROVED**: with signed advantage replaced by `|accGen − accUnif| ≥ δ`, one of the predictor or its
        flip predicts correctly with probability `≥ 1/2 + δ`.

So the single-step distinguishing advantage of rung 9 becomes a next-bit predictor with the same advantage — the object
that, fed the *other* coordinates (each a small circuit by rung 7), yields a small circuit computing the hard function `f`
better than chance.

## Honest scope — Yao's conversion, not the fusion or the collapse

This proves Yao's next-bit identity and its two-sided form: distinguishing advantage `⇒` prediction advantage, in a genuine
finite-probability model.  It does **not** fuse this with rung 9's NW hybrids (expressing `E`, `g` in terms of a
distinguisher `D` acting on `nwHybrid`, which needs integrating out the one fresh coordinate bit), nor with rung 7's
circuit for the other coordinates and `f`'s average-case hardness to reach the contradiction, nor the IKW easy-witness
collapse.  Those are the deep `NEXP`-strength content of socket 2, not established here.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Prob

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ### Linearity of the finite uniform expectation -/

theorem expect_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : expect f = expect g := by
  unfold expect
  rw [Finset.sum_congr rfl (fun x _ => h x)]

theorem expect_add (f g : Ω → ℝ) : expect (fun x => f x + g x) = expect f + expect g := by
  unfold expect
  rw [Finset.sum_add_distrib, add_div]

theorem expect_sub (f g : Ω → ℝ) : expect (fun x => f x - g x) = expect f - expect g := by
  unfold expect
  rw [Finset.sum_sub_distrib, sub_div]

theorem expect_const [Nonempty Ω] (c : ℝ) : expect (fun _ : Ω => c) = c := by
  unfold expect
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, mul_div_assoc,
    div_self (by exact_mod_cast (Fintype.card_ne_zero (α := Ω))), mul_one]

/-! ### The pointwise Boolean core of Yao's identity -/

/-- The pointwise identity behind the predictor "echo the guess iff `E` accepts", averaged over the guess bit. -/
theorem yaoPointwise (Et Ef gb : Bool) :
    (boolToReal ((if Et then true else !true) == gb)
        + boolToReal ((if Ef then false else !false) == gb)) / 2
      = 1 / 2 + (boolToReal (if gb then Et else Ef) - (boolToReal Et + boolToReal Ef) / 2) := by
  cases Et <;> cases Ef <;> cases gb <;> norm_num [boolToReal]

/-- The pointwise identity for the *flipped* predictor "echo the negated guess iff `E` accepts". -/
theorem yaoPointwiseFlip (Et Ef gb : Bool) :
    (boolToReal ((if Et then !true else true) == gb)
        + boolToReal ((if Ef then !false else false) == gb)) / 2
      = 1 / 2 - (boolToReal (if gb then Et else Ef) - (boolToReal Et + boolToReal Ef) / 2) := by
  cases Et <;> cases Ef <;> cases gb <;> norm_num [boolToReal]

/-! ### The predictor, its success probability, and the acceptance probabilities -/

/-- The next-bit predictor with guess bit `b`: echo the guess iff `E` accepts the plugged string. -/
def yaoPredict (E : Ω → Bool → Bool) (ω : Ω) (b : Bool) : Bool := if E ω b then b else !b

/-- The flipped predictor: echo the *negated* guess iff `E` accepts. -/
def yaoPredictFlip (E : Ω → Bool → Bool) (ω : Ω) (b : Bool) : Bool := if E ω b then !b else b

/-- Predictor success probability, averaged over a uniform guess bit. -/
noncomputable def predSucc (E : Ω → Bool → Bool) (g : Ω → Bool) : ℝ :=
  expect (fun ω => (boolToReal (yaoPredict E ω true == g ω)
    + boolToReal (yaoPredict E ω false == g ω)) / 2)

/-- Flipped-predictor success probability, averaged over a uniform guess bit. -/
noncomputable def predSuccFlip (E : Ω → Bool → Bool) (g : Ω → Bool) : ℝ :=
  expect (fun ω => (boolToReal (yaoPredictFlip E ω true == g ω)
    + boolToReal (yaoPredictFlip E ω false == g ω)) / 2)

/-- Acceptance probability when the target coordinate carries the *real* generator bit `g`. -/
noncomputable def accGen (E : Ω → Bool → Bool) (g : Ω → Bool) : ℝ := prob (fun ω => E ω (g ω))

/-- Acceptance probability when the target coordinate carries a *uniform* bit (averaged over the two values). -/
noncomputable def accUnif (E : Ω → Bool → Bool) : ℝ :=
  expect (fun ω => (boolToReal (E ω true) + boolToReal (E ω false)) / 2)

/-! ### Yao's next-bit identity -/

/-- **Yao's next-bit identity (proved)**: the predictor's success probability is exactly `1/2` plus the distinguishing
advantage `accGen − accUnif`.  Distinguishing the real bit from a uniform one with advantage `δ` yields prediction `δ`
above chance. -/
theorem yao_identity [Nonempty Ω] (E : Ω → Bool → Bool) (g : Ω → Bool) :
    predSucc E g = 1 / 2 + (accGen E g - accUnif E) := by
  have hpt : ∀ ω, (boolToReal (yaoPredict E ω true == g ω)
      + boolToReal (yaoPredict E ω false == g ω)) / 2
      = 1 / 2 + (boolToReal (E ω (g ω)) - (boolToReal (E ω true) + boolToReal (E ω false)) / 2) := by
    intro ω
    have hE : E ω (g ω) = if g ω then E ω true else E ω false := by cases h : g ω <;> rfl
    rw [hE]
    simp only [yaoPredict]
    exact yaoPointwise (E ω true) (E ω false) (g ω)
  unfold predSucc
  rw [expect_congr hpt]
  rw [expect_add (fun _ => (1 : ℝ) / 2)
      (fun ω => boolToReal (E ω (g ω)) - (boolToReal (E ω true) + boolToReal (E ω false)) / 2)]
  rw [expect_const]
  rw [expect_sub (fun ω => boolToReal (E ω (g ω)))
      (fun ω => (boolToReal (E ω true) + boolToReal (E ω false)) / 2)]
  rfl

/-- **Flipped-predictor identity (proved)**: the flipped predictor's success is `1/2` minus the advantage. -/
theorem yao_identity_flip [Nonempty Ω] (E : Ω → Bool → Bool) (g : Ω → Bool) :
    predSuccFlip E g = 1 / 2 - (accGen E g - accUnif E) := by
  have hpt : ∀ ω, (boolToReal (yaoPredictFlip E ω true == g ω)
      + boolToReal (yaoPredictFlip E ω false == g ω)) / 2
      = 1 / 2 - (boolToReal (E ω (g ω)) - (boolToReal (E ω true) + boolToReal (E ω false)) / 2) := by
    intro ω
    have hE : E ω (g ω) = if g ω then E ω true else E ω false := by cases h : g ω <;> rfl
    rw [hE]
    simp only [yaoPredictFlip]
    exact yaoPointwiseFlip (E ω true) (E ω false) (g ω)
  unfold predSuccFlip
  rw [expect_congr hpt]
  rw [expect_sub (fun _ => (1 : ℝ) / 2)
      (fun ω => boolToReal (E ω (g ω)) - (boolToReal (E ω true) + boolToReal (E ω false)) / 2)]
  rw [expect_const]
  rw [expect_sub (fun ω => boolToReal (E ω (g ω)))
      (fun ω => (boolToReal (E ω true) + boolToReal (E ω false)) / 2)]
  rfl

/-- **Yao's two-sided conversion (proved)**: if the distinguishing advantage `|accGen − accUnif|` is at least `δ`, then one
of the predictor or its flip predicts the generator's bit with probability at least `1/2 + δ`. -/
theorem yao_two_sided [Nonempty Ω] (E : Ω → Bool → Bool) (g : Ω → Bool) (δ : ℝ)
    (hδ : δ ≤ |accGen E g - accUnif E|) :
    1 / 2 + δ ≤ predSucc E g ∨ 1 / 2 + δ ≤ predSuccFlip E g := by
  rcases abs_cases (accGen E g - accUnif E) with ⟨he, _⟩ | ⟨he, _⟩
  · left; rw [yao_identity]; rw [he] at hδ; linarith
  · right; rw [yao_identity_flip]; rw [he] at hδ; linarith

end PallLean.Paper93.DeepMath.PathB.Prob

#print axioms PallLean.Paper93.DeepMath.PathB.Prob.yao_identity
#print axioms PallLean.Paper93.DeepMath.PathB.Prob.yao_identity_flip
#print axioms PallLean.Paper93.DeepMath.PathB.Prob.yao_two_sided
