import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDimensionRestrictionObserver

/-!
# The dimension observer's base case: a full-rank restricted bound

`ComputationalDepthDimensionRestrictionObserver` gave the dimension observer a *propagation* calculus (linear
halve/square) but no *base case*.  This file supplies the maximal one: the **equality** function on two `k`-bit
blocks has residual-span dimension exactly `2^k` on either block — full rank.

The mechanism is clean: over the free block, the residuals of equality *are the standard basis*.  For the block
`S` (the `false`-side variables), the residual at outside setting encoding `c` is `[x|_S = c]`, i.e. the
indicator of the assignment `c`.  As `c` ranges over the `2^k` block assignments these are linearly independent,
so the residual span has dimension `≥ 2^k` (`eqFun_dim_ge`), which is also the maximum on a `k`-variable block.

So the dimension observer has a genuine restricted base bound (super-log, maximal), and combined with the
halve/square calculus this is a complete restricted observer: base case (full rank) + propagation.  As scoped,
it carries no leverage past `CookLevinFrontierHyp` / Valiant rigidity — the equality base bound collapses under
other decompositions exactly as the log one does — but it makes the dimension analogue of the address-block rung
concrete.

## Honest scope

The full-rank base case of the residual-span dimension observer, via the equality function.  A restricted bound;
no separation, no new complexity-class bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DimensionFullRank

open scoped BigOperators

variable {K : Type*} [Field K] {k : ℕ}

/-- Variables: `k` positions, each with a `false`/`true` side (two `k`-bit blocks). -/
abbrev Idx (k : ℕ) := Fin k × Bool

/-- The equality function on the two blocks. -/
def eqFun (K : Type*) [Field K] (k : ℕ) : (Idx k → Bool) → K :=
  fun x => if (∀ i : Fin k, x (i, false) = x (i, true)) then 1 else 0

/-- The free block: the `false`-side variables. -/
def blockS (k : ℕ) : Finset (Idx k) := Finset.univ.filter (fun p => p.2 = false)

/-- A residual vector of `eqFun` on `blockS` at outside setting `α`. -/
def resVec (K : Type*) [Field K] (k : ℕ) (α : Idx k → Bool) : (Idx k → Bool) → K :=
  fun x => eqFun K k (fun p => if p ∈ blockS k then x p else α p)

/-- The residual indexed by the target assignment `c` on the block: the indicator `[x|_block = c]`. -/
def eqRes (K : Type*) [Field K] (k : ℕ) (c : Fin k → Bool) : (Idx k → Bool) → K :=
  fun x => if (∀ i : Fin k, x (i, false) = c i) then 1 else 0

/-- The input that sets the block to `c0` (and the other side to `false`). -/
def pt (k : ℕ) (c0 : Fin k → Bool) : Idx k → Bool := fun p => if p.2 then false else c0 p.1

theorem mem_blockS_iff (k : ℕ) (p : Idx k) : p ∈ blockS k ↔ p.2 = false := by
  simp [blockS]

/-- Each indicator residual `eqRes c` is genuinely a residual of `eqFun`. -/
theorem eqRes_is_resVec (c : Fin k → Bool) :
    eqRes K k c = resVec K k (fun p => if p.2 then c p.1 else false) := by
  funext x
  simp only [eqRes, resVec, eqFun]
  congr 1
  apply propext
  constructor
  · intro h i
    have hf : ((i, false) : Idx k) ∈ blockS k := by rw [mem_blockS_iff]
    have ht : ((i, true) : Idx k) ∉ blockS k := by rw [mem_blockS_iff]; simp
    rw [if_pos hf, if_neg ht]; simpa using h i
  · intro h i
    have hf : ((i, false) : Idx k) ∈ blockS k := by rw [mem_blockS_iff]
    have ht : ((i, true) : Idx k) ∉ blockS k := by rw [mem_blockS_iff]; simp
    have := h i; rw [if_pos hf, if_neg ht] at this; simpa using this

/-- The indicator residual evaluates to `[c0 = c]` at the point `pt c0`. -/
theorem eqRes_apply_pt (c c0 : Fin k → Bool) :
    eqRes K k c (pt k c0) = if c0 = c then (1 : K) else 0 := by
  simp only [eqRes, pt]
  congr 1
  apply propext
  constructor
  · intro h; funext i; simpa using h i
  · intro h i; simp [h]

/-- **The equality residuals are linearly independent.** -/
theorem eqRes_linearIndependent : LinearIndependent K (eqRes K k) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg c0
  have hpt := congrFun hg (pt k c0)
  simp only [Finset.sum_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hpt
  rw [Finset.sum_eq_single c0] at hpt
  · rw [eqRes_apply_pt] at hpt; simpa using hpt
  · intro c _ hc
    rw [eqRes_apply_pt, if_neg (fun h => hc h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ c0) h

/-- **Full-rank base bound.**  The residual-span dimension of `eqFun` on `blockS` is at least `2^k` — the
maximum on a `k`-variable block, so exactly full rank. -/
theorem eqFun_dim_ge :
    2 ^ k ≤ Module.finrank K (Submodule.span K (Set.range (resVec K k))) := by
  classical
  haveI : FiniteDimensional K ((Idx k → Bool) → K) := inferInstance
  have hsub : Submodule.span K (Set.range (eqRes K k))
      ≤ Submodule.span K (Set.range (resVec K k)) := by
    apply Submodule.span_mono
    rintro _ ⟨c, rfl⟩
    exact ⟨fun p => if p.2 then c p.1 else false, (eqRes_is_resVec c).symm⟩
  have hcard : Module.finrank K (Submodule.span K (Set.range (eqRes K k))) = 2 ^ k := by
    rw [finrank_span_eq_card eqRes_linearIndependent, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  calc 2 ^ k = Module.finrank K (Submodule.span K (Set.range (eqRes K k))) := hcard.symm
    _ ≤ Module.finrank K (Submodule.span K (Set.range (resVec K k))) := Submodule.finrank_mono hsub

end PallLean.Paper93.DeepMath.PathB.DimensionFullRank

#print axioms PallLean.Paper93.DeepMath.PathB.DimensionFullRank.eqRes_linearIndependent
#print axioms PallLean.Paper93.DeepMath.PathB.DimensionFullRank.eqFun_dim_ge
