import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWPredictorCircuit

/-!
# Socket-2 (IKW): the probability / hybrid layer for the Nisan–Wigderson predictor

Rung 7 realised each *other* coordinate of the NW generator as a small circuit (`< 7·2^k`).  The next-bit predictor that
consumes those components rests on the **hybrid argument**: a distinguisher telling the generator's output from uniform,
with advantage `ε`, must distinguish two *consecutive* hybrids (differing in one coordinate) with advantage `≥ ε/m`.  This
file supplies the missing probability framework HAL flagged as step 2, and proves that reduction — the genuine analytic
core of Yao's argument.

  `Prob.expect` / `Prob.prob` / `Prob.distinguish` — a finite uniform-probability scaffold: expectation over a finite
        sample space, the probability of a Boolean event, and a distinguisher's acceptance probability on a sampled
        distribution.  `prob_nonneg` / `prob_le_one` — **PROVED**: it is a genuine probability in `[0,1]`.
  `Prob.exists_consecutive_gap` — **PROVED, the analytic core**: for reals `b : ℕ → ℝ` with `|b 0 - b m| ≥ ε`, some
        consecutive pair has `|b i - b (i+1)| ≥ ε/m` (telescoping + triangle inequality + averaging).
  `Prob.hybrid_argument` — **PROVED, the hybrid reduction**: a distinguisher `D` with advantage `≥ ε` between the endpoint
        hybrids `H 0` and `H m` distinguishes some consecutive pair `H i`, `H (i+1)` with advantage `≥ ε/m`.

So global distinguishing advantage is reduced to single-step advantage — the step that lets the next-bit predictor focus on
one coordinate, where rung 7's small circuit for the *other* coordinates turns it into a small circuit for the hard
function `f`.

## Honest scope — the hybrid reduction, not the full predictor or the collapse

This builds a real finite-probability scaffold and proves the hybrid/averaging reduction — the analytic heart of Yao's
next-bit argument.  It does **not** instantiate the hybrid family `H` as the NW generator's coordinate-hybrids (which needs
an enumeration of the `q^k` design polynomials and an independent uniform-bit source), nor carry out **Yao's next-bit
conversion** (single-step distinguishing advantage `⇒` next-bit prediction advantage) or its combination with rung 7's
circuit and `f`'s average-case hardness to reach a contradiction, nor the IKW easy-witness collapse.  Those are the deep
`NEXP`-strength content of socket 2, not established here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Prob

open Finset

/-- The analytic core of the hybrid argument, stated for a real sequence.  If the endpoints of `b : ℕ → ℝ` differ by at
least `ε` over `m` steps, then some single step accounts for at least `ε/m` of the gap. -/
theorem exists_consecutive_gap (m : ℕ) (hm : 0 < m) (b : ℕ → ℝ) (ε : ℝ)
    (hε : ε ≤ |b 0 - b m|) :
    ∃ i, i < m ∧ ε / m ≤ |b i - b (i + 1)| := by
  by_contra hcon
  push_neg at hcon
  -- Each step is smaller than the average `ε/m`.
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Triangle inequality against the telescoping sum.
  have h1 : |b 0 - b m| ≤ ∑ i ∈ range m, |b i - b (i + 1)| := by
    rw [abs_sub_comm, ← Finset.sum_range_sub b m]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun i _ => abs_sub_comm (b (i + 1)) (b i))
  -- Averaging: the sum of sub-average terms is below `ε`.
  have h2 : ∑ i ∈ range m, |b i - b (i + 1)| < ε := by
    calc ∑ i ∈ range m, |b i - b (i + 1)|
        < ∑ _i ∈ range m, ε / (m : ℝ) :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
            (fun i hi => hcon i (Finset.mem_range.mp hi))
      _ = ε := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm,
            div_mul_cancel₀ ε hm0]
  linarith [hε, h1, h2]

variable {Ω : Type*} [Fintype Ω]

/-- The real value of a Boolean: `1` for `true`, `0` for `false`. -/
def boolToReal (b : Bool) : ℝ := if b then 1 else 0

theorem boolToReal_nonneg (b : Bool) : 0 ≤ boolToReal b := by
  unfold boolToReal; split <;> norm_num

theorem boolToReal_le_one (b : Bool) : boolToReal b ≤ 1 := by
  unfold boolToReal; split <;> norm_num

/-- Uniform expectation of a real-valued function over a finite sample space. -/
noncomputable def expect (f : Ω → ℝ) : ℝ := (∑ x, f x) / (Fintype.card Ω : ℝ)

theorem expect_nonneg {f : Ω → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ expect f :=
  div_nonneg (Finset.sum_nonneg (fun x _ => h x)) (Nat.cast_nonneg _)

/-- The probability that a Boolean event `D` holds under the uniform distribution. -/
noncomputable def prob (D : Ω → Bool) : ℝ := expect (fun x => boolToReal (D x))

theorem prob_nonneg (D : Ω → Bool) : 0 ≤ prob D :=
  expect_nonneg (fun x => boolToReal_nonneg (D x))

theorem prob_le_one [Nonempty Ω] (D : Ω → Bool) : prob D ≤ 1 := by
  unfold prob expect
  rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
  calc ∑ x, boolToReal (D x)
      ≤ ∑ _x : Ω, (1 : ℝ) := Finset.sum_le_sum (fun x _ => boolToReal_le_one (D x))
    _ = (Fintype.card Ω : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- A distinguisher `D`'s acceptance probability on the distribution `samp` sampled uniformly over `Ω`. -/
noncomputable def distinguish {m : ℕ} (D : (Fin m → Bool) → Bool)
    (samp : Ω → (Fin m → Bool)) : ℝ :=
  prob (fun x => D (samp x))

/-- **The hybrid argument (proved)**: if a distinguisher `D` separates the endpoint hybrids `H 0` and `H m` with advantage
at least `ε`, then it separates some *consecutive* pair `H i`, `H (i+1)` with advantage at least `ε/m`.  This is the
reduction that lets a next-bit predictor localise to a single coordinate. -/
theorem hybrid_argument {m : ℕ} (hm : 0 < m)
    (D : (Fin m → Bool) → Bool) (H : ℕ → Ω → (Fin m → Bool)) (ε : ℝ)
    (hε : ε ≤ |distinguish D (H 0) - distinguish D (H m)|) :
    ∃ i, i < m ∧ ε / m ≤ |distinguish D (H i) - distinguish D (H (i + 1))| :=
  exists_consecutive_gap m hm (fun i => distinguish D (H i)) ε hε

end PallLean.Paper93.DeepMath.PathB.Prob

#print axioms PallLean.Paper93.DeepMath.PathB.Prob.exists_consecutive_gap
#print axioms PallLean.Paper93.DeepMath.PathB.Prob.prob_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.Prob.hybrid_argument
