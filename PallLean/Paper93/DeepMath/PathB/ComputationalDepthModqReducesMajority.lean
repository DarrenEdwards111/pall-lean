import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4PadSubcircuits
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMajorityAC0pScope

/-!
# Building the `MOD_q ≤ Majority` reduction — Stage 1: the threshold gadget

To discharge `AC0pReduction (modqLang q) majorityLang p` unconditionally we build the classical
`MOD_q ≤_{AC⁰} Majority` reduction circuit.  Stage 1 here is the reusable core: the **threshold gadget**
`[#ones ≥ k]`, obtained from a `Majority` circuit on `2m+1` inputs by `padInputs` — feeding the `m` real inputs
plus `m+1-k` hardwired `true`s and `k` hardwired `false`s.  Majority on `2m+1` bits (threshold `m+1`) of that
padded assignment is exactly `[#ones(x) + (m+1-k) ≥ m+1] = [#ones(x) ≥ k]`.

## Proved (clean axioms, no `sorry`)

* `trueCount_padBits` — the count of the padded assignment is `#ones(x) + (m+1-k)`.
* `thresholdCirc_eval` — `(thresholdCirc m k Maj).eval x = [#ones(x) ≥ k]`, when `Maj` computes Majority on
  `2m+1` inputs.
* `thresholdCirc_isAC0p` / `thresholdCirc_depth` — the gadget is `AC⁰[p]` and has the same depth as `Maj`.

Stage 2 (the `MOD_q` OR‑combination, its correctness, the polynomial size bound, and the `AC0pReduction`
conclusion) builds on this gadget.
-/

namespace PallLean.Paper93.DeepMath.PathB.ModqReducesMajority

open Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.BoolCircuitSyntax

/-- The input selector: real inputs `0..m-1`, then `m+1-k` hardwired `true`s, then `k` hardwired `false`s. -/
def selector (m k : ℕ) : Fin (2 * m + 1) → BoolCircuitSyntax m :=
  fun i => if h : (i : ℕ) < m then .input ⟨i, h⟩
           else if (i : ℕ) < 2 * m + 1 - k then .const true else .const false

/-- The padded Boolean assignment that `selector` realizes. -/
def padBits (m k : ℕ) (x : Fin m → Bool) : Fin (2 * m + 1) → Bool :=
  fun i => if h : (i : ℕ) < m then x ⟨i, h⟩ else decide ((i : ℕ) < 2 * m + 1 - k)

theorem selector_eval (m k : ℕ) (x : Fin m → Bool) (i : Fin (2 * m + 1)) :
    (selector m k i).eval x = padBits m k x i := by
  unfold selector padBits
  by_cases h : (i : ℕ) < m
  · simp [h, BoolCircuitSyntax.eval]
  · by_cases h2 : (i : ℕ) < 2 * m + 1 - k <;> simp [h, h2, BoolCircuitSyntax.eval]

/-- **The padded count.**  `#ones(padBits x) = #ones(x) + (m+1-k)` for `k ≤ m+1`. -/
theorem trueCount_padBits (m k : ℕ) (hk : k ≤ m + 1) (x : Fin m → Bool) :
    (univ.filter (fun i : Fin (2 * m + 1) => padBits m k x i = true)).card
      = (univ.filter (fun j : Fin m => x j = true)).card + (m + 1 - k) := by
  classical
  set xb : ℕ → Bool := fun a => if h : a < m then x ⟨a, h⟩ else false with hxb
  set g : ℕ → ℕ := fun a => if a < m then (if xb a = true then 1 else 0)
                            else (if a < 2 * m + 1 - k then 1 else 0) with hg
  have hLHS : (univ.filter (fun i : Fin (2 * m + 1) => padBits m k x i = true)).card
      = ∑ i ∈ range (2 * m + 1), g i := by
    rw [Finset.card_filter]
    rw [show (∑ i : Fin (2 * m + 1), if padBits m k x i = true then 1 else 0)
          = ∑ i : Fin (2 * m + 1), g ↑i from ?_]
    · exact Fin.sum_univ_eq_sum_range g (2 * m + 1)
    · apply Finset.sum_congr rfl
      intro i _
      by_cases h : (↑i : ℕ) < m
      · simp only [padBits, hg, hxb, h, dif_pos, if_pos]
      · simp only [padBits, hg, hxb, h, dif_neg, if_neg, not_false_iff,
          decide_eq_true_eq]
  have hRHS1 : (univ.filter (fun j : Fin m => x j = true)).card = ∑ i ∈ range m, g i := by
    rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range g m]
    apply Finset.sum_congr rfl
    intro j _
    have hjm : (↑j : ℕ) < m := j.isLt
    simp only [hg, hxb, hjm, if_pos, dif_pos]
  rw [hLHS, hRHS1, show 2 * m + 1 = m + (m + 1) from by ring, Finset.sum_range_add]
  congr 1
  rw [show (∑ i ∈ range (m + 1), g (m + i)) = ∑ i ∈ range (m + 1), (if i < m + 1 - k then 1 else 0)
        from ?_]
  · rw [Finset.sum_boole]
    have hf : (range (m + 1)).filter (fun i => i < m + 1 - k) = range (m + 1 - k) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hf, Finset.card_range, Nat.cast_id]
  · apply Finset.sum_congr rfl
    intro i _
    have hnm : ¬ (m + i < m) := by omega
    have hcond : (m + i < 2 * m + 1 - k) = (i < m + 1 - k) := by rw [eq_iff_iff]; omega
    simp only [hg, hnm, if_neg, not_false_iff, hcond]

/-- The threshold gadget `[#ones ≥ k]` built from a Majority circuit on `2m+1` inputs. -/
def thresholdCirc (m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) : BoolCircuitSyntax m :=
  Layer4.padInputs (selector m k) Maj

theorem selector_isAC0p (p m k : ℕ) (i : Fin (2 * m + 1)) :
    IsAC0pSyntax p (selector m k i) := by
  unfold selector
  by_cases h : (i : ℕ) < m
  · simp [h, IsAC0pSyntax]
  · by_cases h2 : (i : ℕ) < 2 * m + 1 - k <;> simp [h, h2, IsAC0pSyntax]

theorem selector_depth (m k : ℕ) (i : Fin (2 * m + 1)) : (selector m k i).depth = 0 := by
  unfold selector
  by_cases h : (i : ℕ) < m
  · simp [h, BoolCircuitSyntax.depth]
  · by_cases h2 : (i : ℕ) < 2 * m + 1 - k <;> simp [h, h2, BoolCircuitSyntax.depth]

/-- **The gadget computes the threshold (proved).**  If `Maj` is Majority on `2m+1` inputs, the padded gadget
computes `[#ones(x) ≥ k]`. -/
theorem thresholdCirc_eval (m k : ℕ) (hk : k ≤ m + 1) (Maj : BoolCircuitSyntax (2 * m + 1))
    (hMaj : ∀ y, Maj.eval y
      = decide ((2 * m + 1 + 1) / 2 ≤ (univ.filter (fun i => y i = true)).card))
    (x : Fin m → Bool) :
    (thresholdCirc m k Maj).eval x = decide (k ≤ (univ.filter (fun j : Fin m => x j = true)).card) := by
  rw [thresholdCirc, Layer4.padInputs_eval]
  rw [show (fun i => (selector m k i).eval x) = padBits m k x from funext (selector_eval m k x)]
  rw [hMaj, trueCount_padBits m k hk x, decide_eq_decide]
  omega

/-- The gadget is `AC⁰[p]` whenever `Maj` is. -/
theorem thresholdCirc_isAC0p (p m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1))
    (hMaj : IsAC0pSyntax p Maj) : IsAC0pSyntax p (thresholdCirc m k Maj) :=
  Layer4.padInputs_isAC0pSyntax p (selector m k) (selector_isAC0p p m k) Maj hMaj

/-- The gadget has the same depth as `Maj` (padding substitutes only depth‑`0` leaves). -/
theorem thresholdCirc_depth (m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) :
    (thresholdCirc m k Maj).depth = Maj.depth :=
  Layer4.padInputs_depth (selector m k) (selector_depth m k) Maj

end PallLean.Paper93.DeepMath.PathB.ModqReducesMajority

#print axioms PallLean.Paper93.DeepMath.PathB.ModqReducesMajority.trueCount_padBits
#print axioms PallLean.Paper93.DeepMath.PathB.ModqReducesMajority.thresholdCirc_eval
