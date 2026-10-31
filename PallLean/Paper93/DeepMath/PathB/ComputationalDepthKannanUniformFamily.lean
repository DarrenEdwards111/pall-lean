import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKannanTruthTableOrder

/-!
# The Kannan arc, stage 4: the uniform family — one object across all input lengths

Stages 1–3 worked at a single input length.  Kannan's theorem is about a **family**: one function per
input length `n`, hard at size `n^k` for almost all `n`.  This file builds the family as a single
object and proves its uniform hardness — unconditionally for the linear threshold, with the
`k`-general threshold isolated as a named, true, purely-arithmetic remaining obligation.

## What is proved

* **`kannanF k n`** — the family: at each `n`, *the* canonical truth-table-first function hard at
  size `n^k` (extracted from stage 3's `∃!`; junk value below threshold).  One definition, all `n`.
* **`kannanF_spec` / `kannanF_hard` / `kannanF_canonical`** — wherever a hard function exists, the
  family member is first-hard, hard, and canonical (any first-hard function *is* `kannanF k n`).
* **`four_n_le` / `quad_le`** — the arithmetic engine: `4n + 9 ≤ 2^n` (n ≥ 5) and
  `2n² + 7n ≤ 2^n` (n ≥ 8), by clean `Nat.le_induction`.
* **`linear_threshold`** — the Shannon threshold fires at `L = n` for every `n ≥ 8`:
  `|Code n n| < 2^{2ⁿ}`.
* **`kannanF_linear_hard`** — **the uniform theorem**: for every `n ≥ 8`, no circuit with at most
  `n` gates computes `kannanF 1 n`.  A genuinely uniform, eventually-everywhere, superlinear-threshold
  lower bound for one canonically-named family — the first in this corpus.
* **`PolyThresholdEventually` / `kannanF_eventually_hard_of_threshold`** — the `k`-general
  threshold, named as the remaining stage-4b obligation (TRUE, pure ℕ-asymptotics — polynomial vs
  double exponential — no barrier, only bookkeeping), with the conditional hardness wired.

## Honest scope — uniform hardness is real; the machine translation is the mountain

`kannanF 1` is a single family, canonically defined (the `∃!` of stage 3 over the algorithmic
truth-table order), hard at size `n` for **every** `n ≥ 8` — machine-checked, unconditional.  Two
honest boundaries: (i) the `k`-general threshold is left as `PolyThresholdEventually` — true and
barrier-free, but real ℕ-asymptotics; (ii) the family is *defined by minimization over truth tables*,
not yet shown computable at Σ₂ — translating its Π₂ circuit-space definability into Σ₂ **machine**
semantics over `ComposableMachine` is stage 5, the real mountain, followed by Karp–Lipton and
assembly.  Ceiling unchanged: fixed-polynomial bounds at Σ₂ altitude — not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KannanUniform

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SharingModelShannon
open PallLean.Paper93.DeepMath.PathB.KannanNaming
open PallLean.Paper93.DeepMath.PathB.KannanTT

/-! ### The family -/

open Classical in
/-- **The Kannan family.**  At each input length `n`, *the* canonical truth-table-first function hard
at size `n^k` (from stage 3's `∃!`); constant-false below threshold. -/
noncomputable def kannanF (k n : ℕ) : BF n :=
  if h : ∃ f : BF n, IsHard n (n ^ k) f then (named_of_exists_tt n (n ^ k) h).exists.choose
  else fun _ => false

/-- Wherever a hard function exists, the family member is the first-hard function. -/
theorem kannanF_spec (k n : ℕ) (h : ∃ f : BF n, IsHard n (n ^ k) f) :
    IsFirstHardTT n (n ^ k) (kannanF k n) := by
  simp only [kannanF]
  rw [dif_pos h]
  exact (named_of_exists_tt n (n ^ k) h).exists.choose_spec

/-- The family member is hard wherever hardness is possible. -/
theorem kannanF_hard (k n : ℕ) (h : ∃ f : BF n, IsHard n (n ^ k) f) :
    IsHard n (n ^ k) (kannanF k n) :=
  (kannanF_spec k n h).1

/-- **Canonicity (proved).**  Any first-hard function *is* the family member. -/
theorem kannanF_canonical (k n : ℕ) (h : ∃ f : BF n, IsHard n (n ^ k) f)
    (g : BF n) (hg : IsFirstHardTT n (n ^ k) g) : g = kannanF k n :=
  (named_of_exists_tt n (n ^ k) h).unique hg (kannanF_spec k n h)

/-- Hardness from the counting threshold. -/
theorem kannanF_hard_of_card (k n : ℕ) (hcard : Fintype.card (Code n (n ^ k)) < 2 ^ 2 ^ n) :
    IsHard n (n ^ k) (kannanF k n) :=
  kannanF_hard k n (shannon_exists n (n ^ k) hcard)

/-! ### The arithmetic engine: fixed polynomials fall below `2^n` -/

theorem four_n_le (n : ℕ) (hn : 5 ≤ n) : 4 * n + 9 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h5 : (2 : ℕ) ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    have h5' : (2 : ℕ) ^ 5 = 32 := by norm_num
    rw [Nat.pow_succ]
    omega

theorem quad_le (n : ℕ) (hn : 8 ≤ n) : 2 * (n * n) + 7 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h49 := four_n_le n (by omega)
    have hexp : 2 * ((n + 1) * (n + 1)) + 7 * (n + 1) = 2 * (n * n) + 7 * n + (4 * n + 9) := by
      ring
    rw [Nat.pow_succ]
    omega

/-! ### The linear threshold fires for all `n ≥ 8` -/

theorem linear_threshold (n : ℕ) (hn : 8 ≤ n) :
    Fintype.card (Code n (n ^ 1)) < 2 ^ 2 ^ n := by
  rw [card_code, pow_one]
  have h1 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hA : n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_of_pos_left (n + 1) (by omega)
  have hq : n + 2 + 4 * (n + 1) + 16 * ((n + 1) * (n + 1)) ≤ 23 * ((n + 1) * (n + 1)) := by
    omega
  have hX : (n + 1) * (n + 1) ≤ 2 ^ (n + 1) * 2 ^ (n + 1) :=
    Nat.mul_le_mul h1.le h1.le
  have hpos : 1 ≤ 2 ^ (n + 1) * 2 ^ (n + 1) :=
    Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have h3 : (2 : ℕ) ^ (2 * (n + 1) + 5) = 2 ^ (n + 1) * 2 ^ (n + 1) * 32 := by
    rw [pow_add, two_mul, pow_add]
    norm_num
  have hm : n + 2 + 4 * (n + 1) + 16 * ((n + 1) * (n + 1)) < 2 ^ (2 * (n + 1) + 5) := by
    calc n + 2 + 4 * (n + 1) + 16 * ((n + 1) * (n + 1))
        ≤ 23 * ((n + 1) * (n + 1)) := hq
      _ ≤ 23 * (2 ^ (n + 1) * 2 ^ (n + 1)) := Nat.mul_le_mul_left 23 hX
      _ < 32 * (2 ^ (n + 1) * 2 ^ (n + 1)) := by omega
      _ = 2 ^ (2 * (n + 1) + 5) := by rw [h3, Nat.mul_comm]
  calc (n + 2 + 4 * (n + 1) + 16 * ((n + 1) * (n + 1))) ^ n
      < (2 ^ (2 * (n + 1) + 5)) ^ n := Nat.pow_lt_pow_left hm (by omega)
    _ = 2 ^ ((2 * (n + 1) + 5) * n) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 ^ n) := by
        apply Nat.pow_le_pow_right (by omega)
        have hq2 := quad_le n hn
        have hexp : (2 * (n + 1) + 5) * n = 2 * (n * n) + 7 * n := by ring
        omega

/-! ### The uniform theorem -/

/-- **The uniform hardness theorem (proved).**  For every input length `n ≥ 8`, no circuit with at
most `n` gates computes the family member `kannanF 1 n`.  One canonically-named family, hard
eventually everywhere — uniform, unconditional. -/
theorem kannanF_linear_hard (n : ℕ) (hn : 8 ≤ n) :
    ∀ c : List (CGate n), computes c (kannanF 1 n) → n < c.length := by
  have h := kannanF_hard_of_card 1 n (linear_threshold n hn)
  unfold IsHard at h
  rwa [pow_one] at h

/-- The `k`-general threshold — TRUE (polynomial vs double exponential), pure ℕ-asymptotics, the
named remaining obligation of stage 4b.  No barrier stands here, only bookkeeping. -/
def PolyThresholdEventually : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → Fintype.card (Code n (n ^ k)) < 2 ^ 2 ^ n

/-- **Conditional `k`-general uniform hardness (proved).**  Given the threshold, the family escapes
size `n^k` for almost all `n` — the function-family skeleton of Kannan's theorem. -/
theorem kannanF_eventually_hard_of_threshold (h : PolyThresholdEventually) (k : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → IsHard n (n ^ k) (kannanF k n) := by
  obtain ⟨N, hN⟩ := h k
  exact ⟨N, fun n hn => kannanF_hard_of_card k n (hN n hn)⟩

end PallLean.Paper93.DeepMath.PathB.KannanUniform

#print axioms PallLean.Paper93.DeepMath.PathB.KannanUniform.kannanF_spec
#print axioms PallLean.Paper93.DeepMath.PathB.KannanUniform.linear_threshold
#print axioms PallLean.Paper93.DeepMath.PathB.KannanUniform.kannanF_linear_hard
#print axioms PallLean.Paper93.DeepMath.PathB.KannanUniform.kannanF_eventually_hard_of_threshold
