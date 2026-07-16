import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitClockBounds2

/-!
# Cook–Levin M2 emitter — E6 step 21: THE CLOSER'S INGREDIENTS

Everything the final assembly composes from: the `PolyBounded` closure kit (constants,
identity, pointwise domination, sums, products — so the explicit `coreClock` majorant is
polynomial by construction), the three remaining stream-length bounds
(`cellEmitOut`/`triRowOut`/`headEmitOut`), the pass-bound `t`-monotonicity (so per-round
bounds lift to the grand loop's worst round), and the `run_stable` freeze lift
(`pipeline_at`: the pipeline's `HaltsBy`/`transOut` hold at ANY clock above the exact one).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds3

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCellFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCore
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPipeline
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds2

/-! ## The `PolyBounded` closure kit -/

theorem PB_const (c : ℕ) : PolyBounded (fun _ => c) :=
  ⟨c, 0, fun n => by simp⟩

theorem PB_id : PolyBounded (fun n => n) :=
  ⟨1, 1, fun n => by simp⟩

theorem PB_le {f g : ℕ → ℕ} (h : ∀ n, g n ≤ f n) (hf : PolyBounded f) :
    PolyBounded g := by
  obtain ⟨c, k, hck⟩ := hf
  exact ⟨c, k, fun n => le_trans (h n) (hck n)⟩

theorem PB_add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n + g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, max k1 k2, fun n => ?_⟩
  show f n + g n ≤ (c1 + c2) * (n + 1) ^ max k1 k2
  have e1 : (n + 1) ^ k1 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e2 : (n + 1) ^ k2 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have := h1 n
  have := h2 n
  have m1 : c1 * (n + 1) ^ k1 ≤ c1 * (n + 1) ^ max k1 k2 := Nat.mul_le_mul_left _ e1
  have m2 : c2 * (n + 1) ^ k2 ≤ c2 * (n + 1) ^ max k1 k2 := Nat.mul_le_mul_left _ e2
  have : (c1 + c2) * (n + 1) ^ max k1 k2
      = c1 * (n + 1) ^ max k1 k2 + c2 * (n + 1) ^ max k1 k2 := by ring
  omega

theorem PB_mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n * g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 * c2, k1 + k2, fun n => ?_⟩
  show f n * g n ≤ c1 * c2 * (n + 1) ^ (k1 + k2)
  have := Nat.mul_le_mul (h1 n) (h2 n)
  have e : c1 * (n + 1) ^ k1 * (c2 * (n + 1) ^ k2)
      = c1 * c2 * (n + 1) ^ (k1 + k2) := by
    rw [pow_add]; ring
  omega

/-! ## The remaining stream-length bounds -/

theorem cellEmitOut_length_le (P : ℕ) : ∀ T,
    (cellEmitOut P T).length
      ≤ T * ((P + 1) * (cellCopyRowBody.length * (T + P + 3)))
  | 0 => by simp [cellEmitOut]
  | T + 1 => by
    rw [show cellEmitOut P (T + 1)
        = cellEmitOut P T ++ loop3Out cellCopyRowBody T 1 (P + 1) from rfl,
      List.length_append]
    have h1 := cellEmitOut_length_le P T
    have h2 := CookLevinEmitClockBounds.loop3Out_length_le cellCopyRowBody T 1 (P + 1)
    have h2' : (P + 1) * (cellCopyRowBody.length * (T + 1 + (P + 1) + 1))
        ≤ (P + 1) * (cellCopyRowBody.length * ((T + 1) + P + 3)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : T * ((P + 1) * (cellCopyRowBody.length * (T + P + 3)))
        ≤ T * ((P + 1) * (cellCopyRowBody.length * ((T + 1) + P + 3))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (by omega)))
    have h4 : (T + 1) * ((P + 1) * (cellCopyRowBody.length * ((T + 1) + P + 3)))
        = T * ((P + 1) * (cellCopyRowBody.length * ((T + 1) + P + 3)))
          + (P + 1) * (cellCopyRowBody.length * ((T + 1) + P + 3)) := by ring
    omega

theorem triRowOut_length_le (body : List L3Instr) (t : ℕ) : ∀ R,
    (triRowOut body t R).length ≤ R * (R * (body.length * (t + 2 * R + 3)))
  | 0 => by simp [triRowOut]
  | R + 1 => by
    rw [show triRowOut body t (R + 1)
        = triRowOut body t R ++ loop3Out body t (R + 1) (R + 1) from rfl,
      List.length_append]
    have h1 := triRowOut_length_le body t R
    have h2 := CookLevinEmitClockBounds.loop3Out_length_le body t (R + 1) (R + 1)
    have h2' : (R + 1) * (body.length * (t + (R + 1) + (R + 1) + 1))
        ≤ (R + 1) * (body.length * (t + 2 * (R + 1) + 3)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : R * (R * (body.length * (t + 2 * R + 3)))
        ≤ R * (R * (body.length * (t + 2 * (R + 1) + 3))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (by omega)))
    have h5 : R * (R * (body.length * (t + 2 * (R + 1) + 3)))
        ≤ R * ((R + 1) * (body.length * (t + 2 * (R + 1) + 3))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    have h4 : (R + 1) * ((R + 1) * (body.length * (t + 2 * (R + 1) + 3)))
        = R * ((R + 1) * (body.length * (t + 2 * (R + 1) + 3)))
          + (R + 1) * (body.length * (t + 2 * (R + 1) + 3)) := by ring
    omega

/-- The head grand loop's per-round emission bound. -/
def headRoundOut (P T : ℕ) : ℕ :=
  P * (P * (amoPairRowHeadBody.length * (T + 2 * P + 3))) + (P + 1) + 1
    + (P + 1) * (aloRowHeadBody.length * (T + 2 * P + 3))

theorem headRoundOut_mono (P : ℕ) {T T' : ℕ} (h : T ≤ T') :
    headRoundOut P T ≤ headRoundOut P T' := by
  rw [headRoundOut, headRoundOut]
  have a1 : P * (P * (amoPairRowHeadBody.length * (T + 2 * P + 3)))
      ≤ P * (P * (amoPairRowHeadBody.length * (T' + 2 * P + 3))) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ (by omega)))
  have a2 : (P + 1) * (aloRowHeadBody.length * (T + 2 * P + 3))
      ≤ (P + 1) * (aloRowHeadBody.length * (T' + 2 * P + 3)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  omega

theorem headEmitOut_length_le (P : ℕ) : ∀ T,
    (headEmitOut P T).length ≤ T * headRoundOut P T
  | 0 => by simp [headEmitOut]
  | T + 1 => by
    rw [show headEmitOut P (T + 1)
        = headEmitOut P T ++ (triRowOut amoPairRowHeadBody T P
          ++ (List.replicate (P + 1) true
            ++ ([false] ++ loop3Out aloRowHeadBody T (P + 1) (P + 1)))) from rfl]
    simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    have h1 := headEmitOut_length_le P T
    have h2 := triRowOut_length_le amoPairRowHeadBody T P
    have h2' : P * (P * (amoPairRowHeadBody.length * (T + 2 * P + 3)))
        ≤ P * (P * (amoPairRowHeadBody.length * ((T + 1) + 2 * P + 3))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (by omega)))
    have h3 := CookLevinEmitClockBounds.loop3Out_length_le aloRowHeadBody T (P + 1) (P + 1)
    have h3' : (P + 1) * (aloRowHeadBody.length * (T + (P + 1) + (P + 1) + 1))
        ≤ (P + 1) * (aloRowHeadBody.length * ((T + 1) + 2 * P + 3)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have hmono := headRoundOut_mono P (show T ≤ T + 1 by omega)
    have hT : T * headRoundOut P T ≤ T * headRoundOut P (T + 1) :=
      Nat.mul_le_mul_left _ hmono
    have h4 : (T + 1) * headRoundOut P (T + 1)
        = T * headRoundOut P (T + 1) + headRoundOut P (T + 1) := by ring
    have hunf : headRoundOut P (T + 1)
        = P * (P * (amoPairRowHeadBody.length * ((T + 1) + 2 * P + 3))) + (P + 1) + 1
          + (P + 1) * (aloRowHeadBody.length * ((T + 1) + 2 * P + 3)) := rfl
    omega

/-! ## Pass-bound monotonicity in `t` -/

theorem qcPassBound_mono_t (SG SR CB C1 C2 NV Q BD LM : ℕ) {t t' : ℕ} (h : t ≤ t') :
    qcPassBound SG SR CB C1 C2 NV t Q BD LM
      ≤ qcPassBound SG SR CB C1 C2 NV t' Q BD LM := by
  rw [qcPassBound, qcPassBound]
  have hin : (t + 1 + (Q + 1) + 2) * (2 * (SG + SR + CB + C1 + C2 + NV)
      + 2 * (LM + BD * (t + 1 + (Q + 1) + 1)) + 2 * (t + 1 + (Q + 1)) + 26)
      ≤ (t' + 1 + (Q + 1) + 2) * (2 * (SG + SR + CB + C1 + C2 + NV)
        + 2 * (LM + BD * (t' + 1 + (Q + 1) + 1)) + 2 * (t' + 1 + (Q + 1)) + 26) := by
    apply Nat.mul_le_mul (by omega)
    have := Nat.mul_le_mul_left BD (show t + 1 + (Q + 1) + 1 ≤ t' + 1 + (Q + 1) + 1 by
      omega)
    omega
  have h2 : (BD + 1) * ((t + 1 + (Q + 1) + 2) * (2 * (SG + SR + CB + C1 + C2 + NV)
      + 2 * (LM + BD * (t + 1 + (Q + 1) + 1)) + 2 * (t + 1 + (Q + 1)) + 26))
      ≤ (BD + 1) * ((t' + 1 + (Q + 1) + 2) * (2 * (SG + SR + CB + C1 + C2 + NV)
        + 2 * (LM + BD * (t' + 1 + (Q + 1) + 1)) + 2 * (t' + 1 + (Q + 1)) + 26)) :=
    Nat.mul_le_mul_left _ hin
  have h3 := Nat.mul_le_mul_left (Q + 1) (Nat.add_le_add h2 (le_refl
    (4 * (SG + SR + CB + C1 + C2) + 4 * (Q + 1) + 27)))
  omega

/-! ## The freeze lift -/

/-- **The pipeline at ANY clock above the exact one** — the `run_stable` lift: the majorant
clock inherits `HaltsBy` and the exact output tape. -/
theorem pipeline_at (M : Machine) (clock : ℕ → ℕ) (x : List Bool) (T : ℕ)
    (hB0 : 0 < clock x.length) (hT : coreClock M clock x ≤ T) :
    HaltsBy (emitterCoreMachine M) (encTape clock x) T
    ∧ transOut (emitterCoreMachine M) (encTape clock x) T
      = transOut (emitterCoreMachine M) (encTape clock x) (coreClock M clock x) := by
  obtain ⟨hH, _⟩ := pipeline_run M clock x hB0
  have hrs := run_stable (emitterCoreMachine M) (encTape clock x) hT hH
  constructor
  · unfold HaltsBy at hH ⊢
    rw [hrs]
    exact hH
  · unfold transOut
    rw [hrs]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds3
