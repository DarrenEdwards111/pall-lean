import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaContinuous
import PallLean.Paper93.DeepMath.NFrame.SNFBetaContinuous
import PallLean.Paper93.DeepMath.NFrame.BarrierContinuous

namespace PallLean.Paper93.DeepMath.NFrame

/-- `S_NF` is continuous at `(Φ, A)` whenever Φ has no zero entries and `A.det > 0`. -/
theorem S_NF_continuousAt_smooth {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hphi : ∀ i, phi i ≠ 0) (hA : 0 < A.det) :
    ContinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
      S_NF α β lam adj p.1 chi p.2) (phi, A) := by
  -- We write `S_NF` as the sum of its three term functions in `p = (phi, A)`,
  -- each of which is a composition `{α,β,λ}-term ∘ (fst or snd)`.
  have hfst : ContinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => p.1)
      (phi, A) := continuousAt_fst
  have hsnd : ContinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => p.2)
      (phi, A) := continuousAt_snd
  have hαAt : ContinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
      S_NF_alpha α adj p.1) (phi, A) := by
    have hα : ContinuousAt (fun q : Fin n → ℝ => S_NF_alpha α adj q) phi :=
      (S_NF_alpha_continuous_in_phi α adj).continuousAt
    exact ContinuousAt.comp (g := fun q : Fin n → ℝ => S_NF_alpha α adj q)
      (f := fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => p.1)
      hα hfst
  have hβAt : ContinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
      S_NF_beta β chi p.1) (phi, A) := by
    have hβ : ContinuousAt (fun q : Fin n → ℝ => S_NF_beta β chi q) phi :=
      S_NF_beta_continuousAt_no_zero β chi phi hphi
    exact ContinuousAt.comp (g := fun q : Fin n → ℝ => S_NF_beta β chi q)
      (f := fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => p.1)
      hβ hfst
  have hlamAt : ContinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
      S_NF_lambda lam p.2) (phi, A) := by
    have hbarrier : ContinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
        barrier p.2) (phi, A) :=
      ContinuousAt.comp (g := fun M : Matrix (Fin n) (Fin n) ℝ => barrier M)
        (f := fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => p.2)
        (barrier_continuousAt_of_det_pos A hA) hsnd
    have hdef : (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
        S_NF_lambda lam p.2) =
        (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => lam * barrier p.2) := rfl
    rw [hdef]
    exact continuousAt_const.mul hbarrier
  have hsum : ContinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
      S_NF_alpha α adj p.1 + S_NF_beta β chi p.1 + S_NF_lambda lam p.2) (phi, A) :=
    (hαAt.add hβAt).add hlamAt
  -- `S_NF = alpha + beta + lambda` by `S_NF_decompose`; rewrite and conclude.
  have hrewrite : (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
        S_NF α β lam adj p.1 chi p.2) =
      (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
        S_NF_alpha α adj p.1 + S_NF_beta β chi p.1 + S_NF_lambda lam p.2) := by
    funext p
    exact S_NF_decompose α β lam adj p.1 chi p.2
  rw [hrewrite]
  exact hsum

end PallLean.Paper93.DeepMath.NFrame
