import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPInteractiveCoupling
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The algebraic (log-)rank communication lower bound

The interactive coupling proved a communication lower bound for the equality family via **fooling sets**.  This
file adds the **algebraic-rank** method — the sharpest of the classical deterministic communication lower-bound
techniques, and the one where SPDP/matrix rank genuinely applies.

Over a field, the communication matrix `M_f` of a two-party function decomposes, along the leaves of any
protocol, into one **combinatorial rectangle** per transcript.  On each rectangle `M_f` is monochromatic, so the
corresponding block is an **outer product** (`Matrix.vecMulVec`) of rank `≤ 1`.  Rank is subadditive, so

```text
  rank(M_f)  ≤  #transcripts.
```

Hence any protocol computing `f` has at least `rank_𝔽(M_f)` transcripts, and a `c`-bit protocol needs
`c ≥ log₂ rank_𝔽(M_f)`.  For the equality family the communication matrix is the **identity**, whose rank is
`2^n` (`Matrix.rank_one`), recovering the `2^n`-transcript bound through a purely algebraic route.

The rank method **strictly dominates** the fooling-set method in reach: it is a lower bound on rank over a
field, which for functions such as inner product exceeds every fooling set.  This is the genuine strengthening —
the same ladder, now with the algebraic technique.

## What is new here

* `matrix_rank_add_le` / `matrix_rank_sum_le` — `ℕ`-valued matrix-rank subadditivity (not in Mathlib for the
  `Matrix.rank` `finrank` form).
* `rank_le_card_transcript` — **the algebraic communication lower bound**: `rank(M_f) ≤ #transcripts` for any
  protocol computing `f`, via the rectangle/outer-product decomposition.
* `eq_rank_lower_bound` / `equalitySAT_rank_lower_bound` — the equality (and `equalityCNF`-SAT) `2^n` bound,
  obtained from `Matrix.rank_one` instead of a fooling set.

## Honest scope

Deterministic two-party communication complexity for concrete families, via the field-rank method — a genuine,
faithful strengthening of the streaming/fooling bound to the strongest classical technique.  It does **not**
reach `P` (a `P`-time machine is not a bounded-communication protocol; `EQ ∈ P`).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPLogRankLowerBound

open PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPMultiPassCoupling
open PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling
open SATDepthMachine

/-- The `CommProtocol.fintype` field, exposed as an instance so sums and `Fintype.card` over the transcript
type resolve. -/
instance instFintypeTranscript {p q : Nat} (P : CommProtocol p q) : Fintype P.Transcript := P.fintype

/-! ## `ℕ`-valued matrix-rank subadditivity -/

/-- Subadditivity of the (`finrank`-valued) matrix rank under addition. -/
theorem matrix_rank_add_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {F : Type*} [Field F] (A B : Matrix m n F) : (A + B).rank ≤ A.rank + B.rank := by
  show Module.finrank F (LinearMap.range (A + B).mulVecLin) ≤
      Module.finrank F (LinearMap.range A.mulVecLin) + Module.finrank F (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_add]
  refine le_trans (Submodule.finrank_mono (LinearMap.range_add_le _ _)) ?_
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

/-- Subadditivity over a finite sum of matrices. -/
theorem matrix_rank_sum_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {F : Type*} [Field F] {ι : Type*} (s : Finset ι) (A : ι → Matrix m n F) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp [Matrix.rank_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (matrix_rank_add_le _ _) (Nat.add_le_add_left ih _)

/-! ## The communication matrix and its per-transcript blocks -/

/-- The communication matrix of `f` over `ℚ`: entry `(a, b)` is `1` if `f a b` else `0`. -/
noncomputable def commMatrix {p q : Nat} (f : (Fin p → Bool) → (Fin q → Bool) → Bool) :
    Matrix (Fin p → Bool) (Fin q → Bool) ℚ :=
  fun a b => if f a b then 1 else 0

open Classical in
/-- The block of the communication matrix supported on the rectangle of transcript `τ`. -/
noncomputable def block {p q : Nat} (P : CommProtocol p q)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool) (τ : P.Transcript) :
    Matrix (Fin p → Bool) (Fin q → Bool) ℚ :=
  fun a b => if P.transcript a b = τ then commMatrix f a b else 0

/-- The communication matrix is the sum of its per-transcript blocks. -/
theorem commMatrix_eq_sum {p q : Nat} (P : CommProtocol p q)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool) :
    commMatrix f = ∑ τ : P.Transcript, block P f τ := by
  classical
  letI := P.fintype
  funext a b
  rw [Matrix.sum_apply]
  simp only [block]
  rw [Finset.sum_ite_eq Finset.univ (P.transcript a b) (fun _ => commMatrix f a b)]
  simp

/-- **Each transcript block has rank `≤ 1`.**  On the transcript's rectangle the matrix is monochromatic, so the
block is an outer product `vecMulVec w u`. -/
theorem block_rank_le_one {p q : Nat} (P : CommProtocol p q)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool) (hcomp : ∀ a b, P.eval a b = f a b)
    (τ : P.Transcript) : (block P f τ).rank ≤ 1 := by
  classical
  set v : ℚ := if P.out τ then 1 else 0 with hv
  set w : (Fin p → Bool) → ℚ := fun a => if ∃ b, P.transcript a b = τ then v else 0 with hw
  set u : (Fin q → Bool) → ℚ := fun b => if ∃ a, P.transcript a b = τ then (1 : ℚ) else 0 with hu
  have hblock : block P f τ = Matrix.vecMulVec w u := by
    funext a b
    simp only [block, Matrix.vecMulVec_apply, hw, hu]
    by_cases hτ : P.transcript a b = τ
    · rw [if_pos hτ, if_pos ⟨b, hτ⟩, if_pos ⟨a, hτ⟩, mul_one]
      have hf : f a b = P.out τ := by
        rw [← hcomp a b]; show P.out (P.transcript a b) = P.out τ; rw [hτ]
      simp only [commMatrix]
      rw [hf, ← hv]
    · rw [if_neg hτ]
      by_cases hxb : ∃ b', P.transcript a b' = τ
      · by_cases hxa : ∃ a', P.transcript a' b = τ
        · exfalso
          apply hτ
          obtain ⟨b', hb'⟩ := hxb
          obtain ⟨a', ha'⟩ := hxa
          have hmid : P.transcript a b' = P.transcript a' b := hb'.trans ha'.symm
          have hr := P.rectangle a a' b' b hmid
          rw [hr]; exact hb'
        · rw [if_neg hxa, mul_zero]
      · rw [if_neg hxb, zero_mul]
  rw [hblock]
  exact Matrix.rank_vecMulVec_le w u

/-- **The algebraic communication lower bound.**  Any protocol computing `f` has at least `rank_ℚ(M_f)`
transcripts. -/
theorem rank_le_card_transcript {p q : Nat} (P : CommProtocol p q)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool) (hcomp : ∀ a b, P.eval a b = f a b) :
    (commMatrix f).rank ≤ Fintype.card P.Transcript := by
  classical
  letI := P.fintype
  rw [commMatrix_eq_sum P f]
  calc (∑ τ : P.Transcript, block P f τ).rank
      ≤ ∑ τ : P.Transcript, (block P f τ).rank := matrix_rank_sum_le _ _
    _ ≤ ∑ _τ : P.Transcript, 1 := Finset.sum_le_sum (fun τ _ => block_rank_le_one P f hcomp τ)
    _ = Fintype.card P.Transcript := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-! ## The equality family via the identity matrix -/

/-- The equality communication matrix is the identity matrix. -/
theorem commMatrix_EQ_eq_one (n : Nat) :
    commMatrix (EQ n) = (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℚ) := by
  funext a b
  by_cases h : a = b <;> simp [commMatrix, EQ, Matrix.one_apply, h]

/-- **Equality lower bound via rank.**  Any protocol computing `EQ` has `≥ 2^n` transcripts — obtained from
`Matrix.rank_one` (the identity has full rank), not from a fooling set. -/
theorem eq_rank_lower_bound (n : Nat) (P : CommProtocol n n)
    (hcomp : ∀ a b, P.eval a b = EQ n a b) :
    2 ^ n ≤ Fintype.card P.Transcript := by
  have h := rank_le_card_transcript P (EQ n) hcomp
  rw [commMatrix_EQ_eq_one, Matrix.rank_one, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at h
  exact h

/-- **Algebraic SAT lower bound.**  Any two-way protocol deciding the `equalityCNF` SAT family has `≥ 2^n`
transcripts, proved through the field-rank of the identity communication matrix. -/
theorem equalitySAT_rank_lower_bound (n : Nat) (P : CommProtocol n n)
    (hSAT : ∀ a b, P.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    2 ^ n ≤ Fintype.card P.Transcript :=
  eq_rank_lower_bound n P (eval_eq_EQ_of_satIff P.eval hSAT)

/-- **Bounded-round / bounded-width corollary (rank form).**  If the transcript is a `rounds`-tuple of
width-`|State|` messages, then `width ^ rounds ≥ rank_ℚ(M_{EQ}) = 2^n`. -/
theorem eq_rounds_width_tradeoff (n rounds : Nat) (State : Type) [Fintype State]
    (P : CommProtocol n n) (hcard : @Fintype.card P.Transcript P.fintype = (Fintype.card State) ^ rounds)
    (hcomp : ∀ a b, P.eval a b = EQ n a b) :
    2 ^ n ≤ (Fintype.card State) ^ rounds := by
  rw [← hcard]; exact eq_rank_lower_bound n P hcomp

end PallLean.Paper93.DeepMath.PathB.PvsNPLogRankLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPLogRankLowerBound.matrix_rank_sum_le
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPLogRankLowerBound.rank_le_card_transcript
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPLogRankLowerBound.eq_rank_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPLogRankLowerBound.equalitySAT_rank_lower_bound
