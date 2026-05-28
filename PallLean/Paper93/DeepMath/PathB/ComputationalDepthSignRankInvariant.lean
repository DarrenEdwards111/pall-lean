import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Sign-rank invariant: the frontier observer for depth-2 threshold circuits

**STATUS: FRONTIER INVARIANT FRAMEWORK. PROVEN CONSERVATION + CARRIED FORSTER.**

This is the sign-rank rung of the observer-invariant program — the one place where
"closer to TC⁰" is genuinely true, because sign-rank yields *proven* super-polynomial
lower bounds against **depth-2 threshold circuits** (`LTF ∘ LTF`, equivalently the
unbounded-error UPP communication model), a real sub-class of TC⁰.

`HasSignRankLE M d` says the ±1 sign pattern of `M` is realized by a real matrix
factoring through dimension `d` (`B : m×d`, `C : d×n`, with `(B*C) i j` agreeing in
sign with `M i j`).  `signRank M` is the least such `d`.

## What is PROVEN here (clean, no sorry)
* `hasSignRankLE_cols` : the trivial upper bound `signRank M ≤ n` (explicit factorization).
* `hasSignRankLE_submatrix` : sign-rank is monotone under taking submatrices.
* `no_small_depth2` : the **conservation no-go** — a Forster lower bound `signRank ≥ B`
  plus the depth-2 → sign-rank bridge forces the depth-2 budget bound `≥ B`; any
  claimed sub-`B` budget is `False`.  (Same conservation shape as the crossing no-go.)

## What is CARRIED (the deep classical inputs, clearly labelled)
* `ForsterLowerBound M B` — **Forster's spectral theorem**
  `signRank M ≥ √(mn) / ‖M‖`.  This is a genuine analytic theorem (an optimization
  over `GL(d,ℝ)` to a radially-isotropic position, plus a trace/dimension count); its
  full Lean formalization is a separate major effort.  Carried as a hypothesis, exactly
  as the Nečiporuk leaf-counting lemma was carried.  For the inner-product / Hadamard
  matrix `‖M‖ = √N`, so `B = √N = 2^{n/2}` — super-polynomial.
* the **depth-2 → sign-rank bridge** (`UPP cost c ⟹ signRank ≤ 2^c`): the easy,
  constructive direction (a protocol/circuit yields the factorization), carried here as
  a hypothesis on the model.

## Honest ceiling
Sign-rank characterizes exactly **depth-2 threshold / UPP**.  It does **not** capture
depth-≥3 threshold circuits or general (constant-depth) TC⁰ — those remain open.  The
reason sign-rank evades the natural-proofs barrier is that its lower bounds key on a
*specific* hard matrix (inner product), not a large fraction of functions — which is
also precisely why they do not lift to all of TC⁰.  Real restricted theorem; not a
P vs NP bridge.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Matrix

/-- ±1 sign of a Boolean entry. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

/-! ## The sign-rank invariant -/

/-- `HasSignRankLE M d`: the ±1 sign pattern of `M` is realized by a real matrix of
rank `≤ d`, presented as a factorization `B * C` through dimension `d`. -/
def HasSignRankLE {m n : Nat} (M : Fin m -> Fin n -> Bool) (d : Nat) : Prop :=
  ∃ (B : Matrix (Fin m) (Fin d) ℝ) (C : Matrix (Fin d) (Fin n) ℝ),
    ∀ i j, 0 < sgn (M i j) * (B * C) i j

/-- **Trivial upper bound.**  Every `m × n` sign matrix has sign-rank `≤ n`: take the
columns themselves as the factorization (`B = M`, `C = 1`). -/
theorem hasSignRankLE_cols {m n : Nat} (M : Fin m -> Fin n -> Bool) :
    HasSignRankLE M n := by
  refine ⟨Matrix.of (fun i j => sgn (M i j)), (1 : Matrix (Fin n) (Fin n) ℝ), ?_⟩
  intro i j
  rw [Matrix.mul_one, Matrix.of_apply, sgn_mul_self]
  norm_num

/-- **Monotonicity under submatrices.**  Sign-rank does not increase when restricting
to a submatrix (restrict the factorization vectors). -/
theorem hasSignRankLE_submatrix {m n m' n' d : Nat} (M : Fin m -> Fin n -> Bool)
    (ρ : Fin m' -> Fin m) (σ : Fin n' -> Fin n) (h : HasSignRankLE M d) :
    HasSignRankLE (fun i j => M (ρ i) (σ j)) d := by
  obtain ⟨B, C, hBC⟩ := h
  refine ⟨B.submatrix ρ (Equiv.refl (Fin d)), C.submatrix (Equiv.refl (Fin d)) σ, ?_⟩
  intro i j
  have hmul :
      (B.submatrix ρ (Equiv.refl (Fin d)) * C.submatrix (Equiv.refl (Fin d)) σ) i j
        = (B * C) (ρ i) (σ j) := by
    rw [Matrix.submatrix_mul_equiv]; rfl
  rw [hmul]
  exact hBC (ρ i) (σ j)

/-! ## Carried Forster lower bound -/

/-- **Carried deep input — Forster's spectral lower bound.**  `signRank M ≥ B`,
i.e. no factorization of dimension below `B` can realize the sign pattern.  This is
the genuine analytic theorem; here it is a labelled hypothesis. -/
def ForsterLowerBound {m n : Nat} (M : Fin m -> Fin n -> Bool) (B : Nat) : Prop :=
  ∀ d, HasSignRankLE M d -> B <= d

/-! ## Conservation no-go: Forster ⇒ depth-2 threshold lower bound -/

/-- Under a Forster bound, any dimension realizing `M`'s sign pattern is `≥ B`. -/
theorem signRank_ge_of_forster {m n : Nat} {M : Fin m -> Fin n -> Bool} {B d : Nat}
    (hF : ForsterLowerBound M B) (h : HasSignRankLE M d) : B <= d :=
  hF d h

/-- A depth-2 model with budget `s` (via the carried bridge giving a dimension
`bound s` factorization) must satisfy `bound s ≥ B`. -/
theorem depth2_budget_ge {m n : Nat} {M : Fin m -> Fin n -> Bool} {B : Nat}
    (Compute : Nat -> Prop) (bound : Nat -> Nat)
    (hF : ForsterLowerBound M B)
    (hbridge : ∀ s, Compute s -> HasSignRankLE M (bound s))
    {s : Nat} (hs : Compute s) : B <= bound s :=
  hF (bound s) (hbridge s hs)

/-- **Conservation no-go.**  If the claimed depth-2 budget-to-dimension bound ever
falls below the Forster bound `B` at some scale, it is contradictory.  With `B`
super-polynomial (Forster on inner product: `B = 2^{n/2}`), this is a genuine
super-polynomial lower bound against depth-2 threshold / UPP. -/
theorem no_small_depth2 {m n : Nat} {M : Fin m -> Fin n -> Bool} {B : Nat}
    (Compute : Nat -> Prop) (bound : Nat -> Nat)
    (hF : ForsterLowerBound M B)
    (hbridge : ∀ s, Compute s -> HasSignRankLE M (bound s))
    {s : Nat} (hs : Compute s) (hsmall : bound s < B) : False :=
  Nat.not_lt.mpr (depth2_budget_ge Compute bound hF hbridge hs) hsmall

/-! ## Bundled invariant -/

/-- Package: the proven conservation kernel of the sign-rank invariant. -/
structure SignRankInvariant : Prop where
  /-- Trivial upper bound `signRank ≤ n`. -/
  upper_bound : ∀ {m n : Nat} (M : Fin m -> Fin n -> Bool), HasSignRankLE M n
  /-- Submatrix monotonicity. -/
  submatrix_mono : ∀ {m n m' n' d : Nat} (M : Fin m -> Fin n -> Bool)
    (ρ : Fin m' -> Fin m) (σ : Fin n' -> Fin n),
    HasSignRankLE M d -> HasSignRankLE (fun i j => M (ρ i) (σ j)) d
  /-- Forster ⇒ depth-2 budget lower bound (conservation). -/
  depth2_lower : ∀ {m n : Nat} {M : Fin m -> Fin n -> Bool} {B : Nat}
    (Compute : Nat -> Prop) (bound : Nat -> Nat),
    ForsterLowerBound M B ->
    (∀ s, Compute s -> HasSignRankLE M (bound s)) ->
    ∀ {s : Nat}, Compute s -> B <= bound s

/-- Completed sign-rank invariant kernel. -/
theorem signRankInvariant : SignRankInvariant where
  upper_bound := fun M => hasSignRankLE_cols M
  submatrix_mono := fun M ρ σ h => hasSignRankLE_submatrix M ρ σ h
  depth2_lower := by
    intro m n M B Compute bound hF hbridge s hs
    exact depth2_budget_ge Compute bound hF hbridge hs

/-! ## Kernel-only trace -/

#print axioms hasSignRankLE_cols
#print axioms hasSignRankLE_submatrix
#print axioms no_small_depth2
#print axioms signRankInvariant

end PallLean.Paper93.DeepMath.PathB
