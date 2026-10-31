import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0
import Mathlib

/-!
# Degree of the circuit approximation (PROVED) — the low-degree guarantee of the wrapper

The structural-recursion wrapper of the circuit-approximation has two halves: bad-set accounting
(`ComputationalDepthCircuitApprox`) and **degree tracking**.  This file proves the degree half: the approximating
polynomial built gate-by-gate (each gate's approximator multiplies the degree by `D = t(p-1)`) has total degree
`≤ D^(depth)` — polylogarithmic, not exponential.  This is the entire point of the probabilistic approximation:
the *exact* arithmetisation (`ComputationalDepthArithmetize`) has degree = product of fan-ins (exponential), while
the approximation keeps degree `D^(depth)`.

  `degApprox D C` — the degree of `C`'s approximation: `1` at a leaf, preserved by `NOT`, and `D · (max child
        degree)` at each `AND`/`OR`/`MOD` gate.
  `degApprox_le_pow_depth` — `degApprox D C ≤ D^(depth C)` for `D ≥ 1`: the gate-by-gate degree blow-up is at most
        `D` per layer, so `≤ D^depth` overall.

Combined with the per-gate approximation (`ComputationalDepthGateApproxGen`) and the bad-set accounting, this gives
the circuit-approximation: a degree-`D^depth`, error-`size·2⁻ᵗ` polynomial.  Threading the actual polynomial
construction through the `Circuit` recursion is the remaining wrapper step.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

variable {n : ℕ}

mutual
/-- The degree of the gate-by-gate approximation: `D = t(p-1)` per gate, multiplying the max child degree. -/
def degApprox (D : ℕ) : Circuit n → ℕ
  | var _ => 1
  | const _ => 1
  | not c => degApprox D c
  | and cs => D * degApproxList D cs
  | or cs => D * degApproxList D cs
  | mod _ cs => D * degApproxList D cs
def degApproxList (D : ℕ) : List (Circuit n) → ℕ
  | [] => 1
  | c :: cs => max (degApprox D c) (degApproxList D cs)
end

/-- The child degrees are bounded by `D^(child depth)`, hence their max by `D^(depthList)`. -/
theorem degApproxList_le {D : ℕ} (hD : 1 ≤ D) (cs : List (Circuit n))
    (h : ∀ c ∈ cs, degApprox D c ≤ D ^ depth c) : degApproxList D cs ≤ D ^ depthList cs := by
  induction cs with
  | nil => simp [degApproxList, depthList]
  | cons c cs ih =>
    rw [degApproxList, depthList]
    refine max_le ?_ ?_
    · exact le_trans (h c (List.mem_cons_self ..)) (Nat.pow_le_pow_right hD (le_max_left _ _))
    · exact le_trans (ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')))
        (Nat.pow_le_pow_right hD (le_max_right _ _))

/-- **The low-degree guarantee.**  The gate-by-gate approximation has degree `≤ D^(depth)`: each gate multiplies
the (max child) degree by at most `D`, so over `depth` layers the blow-up is at most `D^depth`. -/
theorem degApprox_le_pow_depth {D : ℕ} (hD : 1 ≤ D) :
    ∀ C : Circuit n, degApprox D C ≤ D ^ depth C
  | var i => by rw [degApprox, depth, pow_zero]
  | const b => by rw [degApprox, depth, pow_zero]
  | not c => by
      rw [degApprox, depth]
      exact le_trans (degApprox_le_pow_depth hD c) (Nat.pow_le_pow_right hD (Nat.le_succ _))
  | and cs => by
      rw [degApprox, depth, pow_succ, mul_comm (D ^ depthList cs) D]
      exact Nat.mul_le_mul_left D (degApproxList_le hD cs (fun c _ => degApprox_le_pow_depth hD c))
  | or cs => by
      rw [degApprox, depth, pow_succ, mul_comm (D ^ depthList cs) D]
      exact Nat.mul_le_mul_left D (degApproxList_le hD cs (fun c _ => degApprox_le_pow_depth hD c))
  | mod m cs => by
      rw [degApprox, depth, pow_succ, mul_comm (D ^ depthList cs) D]
      exact Nat.mul_le_mul_left D (degApproxList_le hD cs (fun c _ => degApprox_le_pow_depth hD c))
termination_by C => sizeOf C
decreasing_by
  all_goals simp_wf
  all_goals (rename_i hc; have := List.sizeOf_lt_of_mem hc; omega)

/-- Each child's approximation degree is at most the children's max (`degApproxList`).  Needed for the `OR`/`AND`
gate constructors: `orPoly`'s degree bound `t(p-1)·B` uses `B = degApproxList`, and each child's polynomial degree
is `≤ degApprox (child) ≤ degApproxList`. -/
theorem degApprox_le_degApproxList {D : ℕ} (cs : List (Circuit n)) (c : Circuit n) :
    c ∈ cs → degApprox D c ≤ degApproxList D cs := by
  induction cs with
  | nil => intro hc; simp at hc
  | cons d cs ih =>
    intro hc
    rw [degApproxList]
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact Nat.le_max_left _ _
    · exact le_trans (ih h) (Nat.le_max_right _ _)

end PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.degApprox_le_pow_depth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.degApprox_le_degApproxList
