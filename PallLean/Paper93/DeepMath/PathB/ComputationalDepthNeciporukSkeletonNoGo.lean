import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukSubfunctionMultiplicative

/-!
# The skeleton/subtree-counting route to `n²/log n` does NOT close (rigorous no-go)

The proposed "skeleton" argument for the constant-per-leaf Nečiporuk bound was:
1. (semantic, TRUE) every *maximal `S`-free subtree* evaluates to a constant under the outside
   assignment `α` — so the block residual is determined by those constants, giving
   `s_i ≤ 2^{freeCount S F}`, where `freeCount` counts maximal `S`-free subtrees;
2. (combinatorial, CLAIMED) `freeCount S F ≤ leavesIn S F + 1`, which would give
   `s_i ≤ 2^{leavesIn+1}` — the constant-per-leaf bound, hence `n²/log n`.

Step 2 is **false**.  A single `S`-leaf can sit at the bottom of an arbitrarily long gate chain, each
gate carrying an `S`-free sibling:
  `chainF g jout i0 k = (lit jout) g ((lit jout) g ( ⋯ g (lit i0) ))`   (`k` gates),
with `i0 ∈ S`, `jout ∉ S`.  Then `leavesIn S (chainF … k) = 1` (the lone `i0` literal) but
`freeCount S (chainF … k) = k` (the `k` `S`-free `jout`-leaves are all maximal `S`-free subtrees).

So `freeCount` is unbounded by `leavesIn`, and `2^{freeCount}` yields no useful bound.  This file proves
exactly that, fencing the route as insufficient.

(The actual `s_i` stays small here — the gates collapse, e.g. an AND-chain has only 2 residuals — but
the *subtree count* cannot detect gate collapse.  The genuine `s_i ≤ 4^{leavesIn}` bound therefore
requires a gate-collapse-aware semantic argument, NOT this structural count.  That remains the open
core; this file only rules out the naive skeleton approach.)
-/

namespace PallLean.Paper93.DeepMath.PathB

open BFormula

variable {n : ℕ}

/-- Number of **maximal `S`-free subtrees** (subtrees containing no `S`-literal), collapsing any whole
`S`-free subtree to a single count via the `leavesIn = 0` guard. -/
def freeCount (S : Finset (Fin n)) : BFormula n → ℕ
  | BFormula.lit i _ => if i ∈ S then 0 else 1
  | BFormula.cst _ => 1
  | BFormula.un _ t => if BFormula.leavesIn S t = 0 then 1 else freeCount S t
  | BFormula.bin _ a b =>
      if BFormula.leavesIn S a = 0 ∧ BFormula.leavesIn S b = 0 then 1
      else freeCount S a + freeCount S b

/-- The gate-chain witness: `k` gates `g`, each with an `S`-free left leaf `lit jout`, bottoming out
at a single `S`-leaf `lit i0`. -/
def chainF (g : Bool → Bool → Bool) (jout i0 : Fin n) : ℕ → BFormula n
  | 0 => BFormula.lit i0 true
  | (k + 1) => BFormula.bin g (BFormula.lit jout true) (chainF g jout i0 k)

variable {S : Finset (Fin n)} {g : Bool → Bool → Bool} {jout i0 : Fin n}

/-- The chain has exactly **one** `S`-leaf (the bottom `i0` literal). -/
theorem leavesIn_chainF (hi0 : i0 ∈ S) (hjout : jout ∉ S) (k : ℕ) :
    BFormula.leavesIn S (chainF g jout i0 k) = 1 := by
  induction k with
  | zero => simp [chainF, BFormula.leavesIn, hi0]
  | succ k ih => simp [chainF, BFormula.leavesIn, hjout, ih]

/-- …but it has `k` maximal `S`-free subtrees. -/
theorem freeCount_chainF (hi0 : i0 ∈ S) (hjout : jout ∉ S) (k : ℕ) :
    freeCount S (chainF g jout i0 k) = k := by
  induction k with
  | zero => simp [chainF, freeCount, hi0]
  | succ k ih =>
      have hb : ¬ (BFormula.leavesIn S (BFormula.lit jout true) = 0 ∧
                   BFormula.leavesIn S (chainF g jout i0 k) = 0) := by
        rw [leavesIn_chainF hi0 hjout k]; simp
      simp only [chainF, freeCount]
      rw [if_neg hb, if_neg hjout, ih]
      omega

/-- **No-go.**  For every bound `C`, there is a formula with a single `S`-leaf yet at least `C`
maximal `S`-free subtrees.  Hence `freeCount` is not bounded by any function of `leavesIn`, so the
skeleton bound `s_i ≤ 2^{freeCount}` cannot yield the constant-per-leaf bound `s_i ≤ 2^{O(leavesIn)}`. -/
theorem freeCount_unbounded_by_leavesIn (g : Bool → Bool → Bool)
    (hi0 : i0 ∈ S) (hjout : jout ∉ S) (C : ℕ) :
    ∃ F : BFormula n, BFormula.leavesIn S F = 1 ∧ C ≤ freeCount S F :=
  ⟨chainF g jout i0 C, leavesIn_chainF hi0 hjout C, (freeCount_chainF hi0 hjout C).ge⟩

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.freeCount_chainF
#print axioms PallLean.Paper93.DeepMath.PathB.freeCount_unbounded_by_leavesIn
