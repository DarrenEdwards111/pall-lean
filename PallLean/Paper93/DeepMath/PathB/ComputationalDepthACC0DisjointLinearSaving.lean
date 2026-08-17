import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DisjointFragmentSpeedup

/-!
# A genuine linear-exponent saving for a named depth-two ACC fragment

The earlier disjoint-fragment theorem reduces satisfiability of an `n`-variable circuit with `k`
pairwise-disjoint, independently realizable MOD gates to exhaustive search over the `k` gate-output bits.
Its published cash-out only recorded the qualitative condition `2^k < 2^n`.

This file records the quantitatively useful form.  A witness `s` with `s ≤ n` and `k ≤ n-s`
gives search cost at most `2^(n-s)`.  If `d*s ≥ c*n` for fixed positive constants `c,d`, the
saved exponent is linear in `n`; equivalently the running time is `2^(n-Ω(n))`.

This is an unconditional, falsifiable base theorem for a sharply restricted depth-two class.  It
does **not** extend to overlapping gates: disjointness is exactly what makes every oracle-output
vector independently realizable.  The next lifting problem is therefore to obtain the same gap
after restrictions/separators for an overlapping named class, including the cost of all leaves.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DisjointLinearSaving

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl
open PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization
open PallLean.Paper93.DeepMath.PathB.ACC0DisjointFragmentSpeedup

variable {n k : ℕ}

/-- A concrete exponent gap between input variables and independently searchable gate outputs. -/
structure LinearGap (n k : ℕ) where
  /-- number of exponent bits saved -/
  saving : ℕ
  savingLe : saving ≤ n
  outputBound : k ≤ n - saving

/-- The output-vector search has the advertised `2^(n-saving)` cost. -/
theorem output_search_le (G : LinearGap n k) :
    2 ^ k ≤ 2 ^ (n - G.saving) := by
  exact Nat.pow_le_pow_right (by norm_num) G.outputBound

/-- A proportional gap is an explicit `Ω(n)` exponent saving.  The division-free inequality
`d * saving ≥ c * n` is convenient in Lean and means `saving ≥ (c/d)n`. -/
def HasLinearSaving (G : LinearGap n k) (c d : ℕ) : Prop :=
  0 < c ∧ 0 < d ∧ c * n ≤ d * G.saving

/-- The quantitative depth-two SAT theorem: exact semantic reduction to the control search,
together with a `2^(n-saving)` search-space bound and a certified proportional exponent gap. -/
theorem disjoint_fragment_linear_speedup
    (C : OracleControl k) (gate : Fin k → ModGate n)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (gate j).support (gate j').support)
    (hach : ∀ j b, ∃ a : Fin n → Bool, (gate j).eval a = b)
    (G : LinearGap n k) (c d : ℕ) (hlinear : HasLinearSaving G c d) :
    (Satisfiable (fun x => controlEval C (fun j => (gate j).eval x)) ↔
        ∃ y ∈ (Finset.univ : Finset (Fin k → Bool)), controlEval C y = true)
      ∧ (Finset.univ : Finset (Fin k → Bool)).card ≤ 2 ^ (n - G.saving)
      ∧ 0 < c ∧ 0 < d ∧ c * n ≤ d * G.saving := by
  refine ⟨?_, ?_, hlinear.1, hlinear.2.1, hlinear.2.2⟩
  · rw [disjoint_fragment_sat_iff C gate hdisj hach]
    unfold Satisfiable
    simp only [Finset.mem_univ, true_and]
  · simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact output_search_le G

/-- Clean half-exponent corollary: at most `n/2` oracle outputs give search cost `2^(n-n/2)`.
The saved exponent `n/2` is linear without asymptotic notation. -/
def halfDensityGap (hkn : k ≤ n - n / 2) : LinearGap n k where
  saving := n / 2
  savingLe := Nat.div_le_self n 2
  outputBound := hkn

end PallLean.Paper93.DeepMath.PathB.ACC0DisjointLinearSaving

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DisjointLinearSaving.output_search_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DisjointLinearSaving.disjoint_fragment_linear_speedup
