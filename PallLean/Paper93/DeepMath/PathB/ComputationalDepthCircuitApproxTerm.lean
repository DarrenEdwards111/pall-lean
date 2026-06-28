import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitApprox
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitDegree
import Mathlib

/-!
# The term-carrying circuit approximation (PROVED: structure + base/unary constructors)

The final wrapper packages, for each circuit `C`, a concrete approximating polynomial together with its
correctness (`ApproxOn`), degree bound (`degApprox`), and bad-set bound (`size · 2^(n-t)`):

  `CircuitApproxData p t C` — the package `⟨poly, bad, approx, degree_le, bad_le⟩`.

This file proves the package's **base and unary constructors** — the cases that are *exact* (no probabilistic
error):

  `caVar` / `caConst` — inputs and constants: the polynomial is `Xᵢ` / a constant, `bad = ∅`.
  `caNot` — negation: `1 - poly`, same bad set (via `ApproxOn.unary`-style reasoning), degree preserved.

These thread the polynomial through the easy parts of the `Circuit` recursion.  The **gate constructors** —
`AND`/`OR` (probabilistic, via `GateApprox.exists_good_forms_gen` substituting the children's polynomials into the
OR-approximator) and `MOD_p` (exact, via `modPoly`) — together with the well-founded recursion assembling them
(the pattern of `degApprox_le_pow_depth`), are the remaining core.  Once assembled, feeding the resulting
low-degree approximator on a large agreement set into `boosting_surjection` yields the Razborov–Smolensky bound.
-/

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.CircuitApprox (ApproxOn)

namespace PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

variable {n : ℕ}

/-- The circuit, as a `ZMod p`-valued function on the cube (`0/1` outputs cast into `𝔽_p`). -/
noncomputable def cf (p : ℕ) (C : Circuit n) : (Fin n → Bool) → ZMod p :=
  fun x => ((Circuit.eval x C).toNat : ZMod p)

/-- A polynomial, as a `ZMod p`-valued function on the cube (evaluated at the `0/1` point). -/
noncomputable def pf (p : ℕ) (P : MvPolynomial (Fin n) (ZMod p)) : (Fin n → Bool) → ZMod p :=
  fun x => MvPolynomial.eval (fun i => ((x i).toNat : ZMod p)) P

/-- The term-carrying approximation package for a circuit `C`: a polynomial approximating `C` off a bad set,
with degree `≤ degApprox (t(p-1)) C` and bad set `≤ size C · 2^(n-t)`. -/
structure CircuitApproxData (p t : ℕ) (C : Circuit n) where
  poly : MvPolynomial (Fin n) (ZMod p)
  bad : Finset (Fin n → Bool)
  approx : ApproxOn (cf p C) (pf p poly) bad
  degree_le : poly.totalDegree ≤ degApprox (t * (p - 1)) C
  bad_le : bad.card ≤ size C * 2 ^ (n - t)

/-- **Input constructor.**  `var i` is computed exactly by the monomial `Xᵢ`. -/
noncomputable def caVar (p t : ℕ) [Fact p.Prime] (i : Fin n) : CircuitApproxData p t (var i) where
  poly := X i
  bad := ∅
  approx := ApproxOn.exact (fun x => by simp [cf, pf, Circuit.eval_var])
  degree_le := by rw [degApprox]; exact le_of_eq (totalDegree_X i)
  bad_le := by rw [Finset.card_empty]; exact Nat.zero_le _

/-- **Constant constructor.**  `const b` is computed exactly by the constant polynomial `b.toNat`. -/
noncomputable def caConst (p t : ℕ) [Fact p.Prime] (b : Bool) :
    CircuitApproxData p t (const b : Circuit n) where
  poly := MvPolynomial.C (b.toNat : ZMod p)
  bad := ∅
  approx := ApproxOn.exact (fun x => by simp [cf, pf])
  degree_le := by rw [degApprox]; exact le_trans (le_of_eq (totalDegree_C _)) (Nat.zero_le 1)
  bad_le := by rw [Finset.card_empty]; exact Nat.zero_le _

/-- **Negation constructor.**  From an approximation of `c`, `not c` is approximated by `1 - poly` on the same bad
set: off `bad`, `1 - poly = 1 - c.eval = (!c.eval)`.  Degree is preserved. -/
noncomputable def caNot (p t : ℕ) (c : Circuit n) (d : CircuitApproxData p t c) :
    CircuitApproxData p t (not c) where
  poly := 1 - d.poly
  bad := d.bad
  approx := by
    intro x hx
    have h := d.approx x hx
    simp only [cf, pf, Circuit.eval_not, map_sub, map_one] at h ⊢
    rw [← h]
    cases Circuit.eval x c <;> simp
  degree_le := by
    rw [degApprox]
    refine le_trans (totalDegree_sub _ _) ?_
    rw [totalDegree_one]
    exact max_le (Nat.zero_le _) d.degree_le
  bad_le := by
    rw [size]
    exact le_trans d.bad_le (Nat.mul_le_mul_right _ (Nat.le_succ _))

end PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.caVar
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.caNot
