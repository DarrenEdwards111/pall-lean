import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEqInP

/-!
# Randomized communication complexity via the discrepancy method

The fourth communication regime: *randomized* (bounded-error) deterministic-distributional
complexity, lower-bounded by **discrepancy**.  Under a distribution `μ` on `X × Y`, the
discrepancy of `f` is the largest signed mass `|μ(R ∩ f⁻¹1) − μ(R ∩ f⁻¹0)|` over combinatorial
rectangles `R`.  Small discrepancy forces large error for *every* low-communication protocol —
because a `c`-bit protocol partitions the matrix into `≤ 2^c` rectangles, on each of which its
output is constant, so its `μ`-advantage is a sum of `≤ 2^c` rectangle discrepancies.

`disc_method` (**the discrepancy method**): for any distribution `μ`, any `k`-leaf protocol `P`,
and any `δ` bounding every rectangle's discrepancy,
`1 − 2·errμ ≤ k·δ`.
So a protocol with few leaves and small discrepancy cannot beat random guessing
(`disc_error_ge`: `errμ ≥ 1/2 − kδ/2`); to get advantage `> 0` one needs `k > 1/δ` leaves,
i.e. `> log₂(1/δ)` bits.

This is the *reduction*, proven in full — an unconditional real-analytic identity plus the
triangle inequality, via the rectangle structure of protocol leaves.  Its canonical witness is
INNER PRODUCT `⟨x,y⟩ mod 2`, whose discrepancy is `2^{-n/2}` (**Lindsey's lemma**: the sign matrix
is Hadamard, `‖H‖ = 2^{n/2}`), giving `R(IP) = Ω(n)`.  That spectral bound (character orthogonality
+ Cauchy–Schwarz) is a separate input, not formalized here — so no unconditional randomized
separation is *claimed*; the reusable engine is.  (Note EQUALITY is the *wrong* witness here: it
has `O(1)` public-coin randomized complexity — its discrepancy is close to `1`.)

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RandCommDisc

open Finset

/-- The `±1` sign of a Boolean value. -/
noncomputable def sgn (b : Bool) : ℝ := if b then 1 else -1

theorem sgn_mul_sgn (a b : Bool) : sgn a * sgn b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> simp [sgn]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

/-- A deterministic protocol as a partition into `k` rectangular leaves, each with a fixed output.
Unlike `RectPartition`, the value `f` need NOT be constant on a leaf — this is the distributional /
randomized setting, where the leaf output is merely the protocol's guess. -/
structure DistProtocol (X Y : Type) (k : ℕ) where
  /-- The leaf reached on `(u, v)`. -/
  leaf : X → Y → Fin k
  /-- Rectangle property: a shared leaf closes to a rectangle. -/
  rect : ∀ u v u' v', leaf u v = leaf u' v' → leaf u v' = leaf u v ∧ leaf u' v = leaf u v
  /-- The protocol's output at each leaf. -/
  out : Fin k → Bool

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- The signed mass of the rectangle `a × b` under `μ` (its discrepancy contribution). -/
noncomputable def bias (μ : X × Y → ℝ) (f : X → Y → Bool) (a : X → Bool) (b : Y → Bool) : ℝ :=
  ∑ p ∈ univ.filter (fun p : X × Y => a p.1 = true ∧ b p.2 = true), μ p * sgn (f p.1 p.2)

/-- The signed mass of leaf `i` under `μ`. -/
noncomputable def leafBias {k : ℕ} (P : DistProtocol X Y k) (f : X → Y → Bool) (μ : X × Y → ℝ)
    (i : Fin k) : ℝ :=
  ∑ p ∈ univ.filter (fun p : X × Y => P.leaf p.1 p.2 = i), μ p * sgn (f p.1 p.2)

/-- The `μ`-error of a protocol: the `μ`-mass of the inputs on which it errs. -/
noncomputable def errμ {k : ℕ} (P : DistProtocol X Y k) (f : X → Y → Bool) (μ : X × Y → ℝ) : ℝ :=
  ∑ p : X × Y, if f p.1 p.2 = P.out (P.leaf p.1 p.2) then 0 else μ p

/-- Each leaf is a rectangle, so its signed mass is bounded by the discrepancy `δ`. -/
theorem leafBias_le {k : ℕ} (P : DistProtocol X Y k) (f : X → Y → Bool) (μ : X × Y → ℝ)
    (δ : ℝ) (hdisc : ∀ (a : X → Bool) (b : Y → Bool), |bias μ f a b| ≤ δ) (i : Fin k) :
    |leafBias P f μ i| ≤ δ := by
  classical
  have hδ0 : 0 ≤ δ := by
    have h := hdisc (fun _ => false) (fun _ => false)
    simp only [bias, Bool.false_eq_true, false_and, filter_false, sum_empty, abs_zero] at h
    exact h
  rcases (univ.filter (fun p : X × Y => P.leaf p.1 p.2 = i)).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
  · rw [leafBias, he, sum_empty, abs_zero]; exact hδ0
  · rw [mem_filter] at hp₀
    obtain ⟨_, hp₀i⟩ := hp₀
    have hfeq : univ.filter (fun p : X × Y => P.leaf p.1 p.2 = i)
        = univ.filter (fun p : X × Y =>
            decide (P.leaf p.1 p₀.2 = i) = true ∧ decide (P.leaf p₀.1 p.2 = i) = true) := by
      apply filter_congr
      intro p _
      simp only [decide_eq_true_eq]
      constructor
      · intro hlp
        have hrp := P.rect p.1 p.2 p₀.1 p₀.2 (by rw [hlp, hp₀i])
        exact ⟨by rw [hrp.1, hlp], by rw [hrp.2, hlp]⟩
      · rintro ⟨h1, h2⟩
        have hrp := P.rect p.1 p₀.2 p₀.1 p.2 (by rw [h1, h2])
        rw [hrp.1, h1]
    rw [leafBias, hfeq]
    exact hdisc (fun x => decide (P.leaf x p₀.2 = i)) (fun y => decide (P.leaf p₀.1 y = i))

/-- **The discrepancy method.**  For any distribution `μ`, any `k`-leaf protocol `P`, and any `δ`
bounding every rectangle's discrepancy, the `μ`-advantage `1 − 2·errμ` is at most `k·δ`.  Hence a
protocol with few leaves and small discrepancy cannot beat random guessing. -/
theorem disc_method {k : ℕ} (f : X → Y → Bool) (μ : X × Y → ℝ) (hμ1 : ∑ p : X × Y, μ p = 1)
    (P : DistProtocol X Y k) (δ : ℝ)
    (hdisc : ∀ (a : X → Bool) (b : Y → Bool), |bias μ f a b| ≤ δ) :
    1 - 2 * errμ P f μ ≤ k * δ := by
  classical
  -- (1) advantage identity
  have step1 : ∑ p : X × Y, sgn (P.out (P.leaf p.1 p.2)) * (μ p * sgn (f p.1 p.2))
      = 1 - 2 * errμ P f μ := by
    have h1 : (1 : ℝ) - 2 * errμ P f μ
        = ∑ p : X × Y, (μ p - 2 * (if f p.1 p.2 = P.out (P.leaf p.1 p.2) then 0 else μ p)) := by
      rw [errμ, mul_sum, ← hμ1, ← sum_sub_distrib]
    rw [h1]
    apply sum_congr rfl
    intro p _
    rw [mul_comm (sgn (P.out (P.leaf p.1 p.2))) (μ p * sgn (f p.1 p.2)), mul_assoc, sgn_mul_sgn]
    by_cases h : f p.1 p.2 = P.out (P.leaf p.1 p.2)
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  -- (2) regroup by leaf
  have hgroup : ∑ p : X × Y, sgn (P.out (P.leaf p.1 p.2)) * (μ p * sgn (f p.1 p.2))
      = ∑ i : Fin k, sgn (P.out i) * leafBias P f μ i := by
    rw [← sum_fiberwise univ (fun p : X × Y => P.leaf p.1 p.2)
      (fun p => sgn (P.out (P.leaf p.1 p.2)) * (μ p * sgn (f p.1 p.2)))]
    apply sum_congr rfl
    intro i _
    rw [leafBias, mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [mem_filter] at hp
    rw [hp.2]
  -- (3) assemble
  calc 1 - 2 * errμ P f μ
      = ∑ i : Fin k, sgn (P.out i) * leafBias P f μ i := by rw [← step1, hgroup]
    _ ≤ ∑ i : Fin k, |leafBias P f μ i| := by
        apply sum_le_sum
        intro i _
        calc sgn (P.out i) * leafBias P f μ i ≤ |sgn (P.out i) * leafBias P f μ i| := le_abs_self _
          _ = |leafBias P f μ i| := by rw [abs_mul, abs_sgn, one_mul]
    _ ≤ ∑ _i : Fin k, δ := by
        apply sum_le_sum
        intro i _
        exact leafBias_le P f μ δ hdisc i
    _ = k * δ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Advantage bound.**  A protocol with `k` leaves against discrepancy `δ` errs on `μ`-mass at
least `1/2 − kδ/2`; it cannot beat random guessing unless `k > 1/δ`, i.e. it uses `> log₂(1/δ)`
bits.  This is the randomized lower bound in error form. -/
theorem disc_error_ge {k : ℕ} (f : X → Y → Bool) (μ : X × Y → ℝ) (hμ1 : ∑ p : X × Y, μ p = 1)
    (P : DistProtocol X Y k) (δ : ℝ)
    (hdisc : ∀ (a : X → Bool) (b : Y → Bool), |bias μ f a b| ≤ δ) :
    errμ P f μ ≥ 1 / 2 - k * δ / 2 := by
  have := disc_method f μ hμ1 P δ hdisc
  linarith

/-- **Bit form.**  A `c`-bit protocol (`2^c` leaves) with `μ`-error `≤ ε` against discrepancy `δ`
forces `1 − 2ε ≤ 2^c · δ`; so `2^c ≥ (1−2ε)/δ` — small discrepancy demands many bits. -/
theorem disc_bits {c : ℕ} (f : X → Y → Bool) (μ : X × Y → ℝ) (hμ1 : ∑ p : X × Y, μ p = 1)
    (P : DistProtocol X Y (2 ^ c)) (δ : ℝ)
    (hdisc : ∀ (a : X → Bool) (b : Y → Bool), |bias μ f a b| ≤ δ)
    (ε : ℝ) (hε : errμ P f μ ≤ ε) :
    1 - 2 * ε ≤ (2 ^ c : ℕ) * δ := by
  have h := disc_method f μ hμ1 P δ hdisc
  have : (1 : ℝ) - 2 * ε ≤ 1 - 2 * errμ P f μ := by linarith
  linarith

end PallLean.Paper93.DeepMath.PathB.RandCommDisc
