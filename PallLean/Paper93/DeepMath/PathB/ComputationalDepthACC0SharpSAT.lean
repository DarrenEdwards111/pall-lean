import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EndToEndBT

/-!
# Bridge (algorithmic payoff, #SAT) — the satisfying-assignment count is a quasipolynomial sum (proved)

The Williams-style **counting** payoff of the polynomial Beigel–Tarui method, for the general (unary/binary) Boolean circuit
model `Circ`.  The proved `endToEnd_BT` gives a sparse low-degree representation `subst c` of any circuit `c`, with monomial
support quasipolynomial in size.  Summing it over the Boolean cube counts satisfying assignments: the **number of satisfying
assignments equals a sum over the quasipolynomial monomial support** (`bt_sharpSat`),

  `#{x : eval c x = true}  =  ∑_{d ∈ support(subst c)} coeff_d · 2^{n − |d|}`,

a sum of at most `(n+1)^{2^{depth+1}}` terms — quasipolynomially many for constant depth.  So `#SAT` is computable from the
sparse polynomial in quasipolynomial time, and in particular SAT is decided by whether this sum is nonzero — the
algorithmic-counting consequence the polynomial method delivers for general constant-depth circuits.

## What is proved (clean axioms, no `sorry`)

* **`bt_sharpSat_eq`** (PROVED) — `(#sat : R) = ∑_{d ∈ support} coeff_d · 2^{n−|d|}` (over any `CommRing R`).
* **`bt_sharpSat`** (PROVED) — the equation **and** the support has `≤ (n+1)^{2^{depth+1}}` distinct monomial features.

## Honest scope

This is the #SAT-counting algorithmic output of the proved BT representation for the general `Circ` model — the counting
ingredient of the Williams route.  Turning it into the unconditional `NEXP ⊄ ACC⁰` still needs the collapse socket
(P≠NP-strength, proved separation-equivalent).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SharpSAT

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitSubstitution (Circ)
open PallLean.Paper93.DeepMath.PathB.ACC0SubstitutionPoly (subst)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (boolVal)
open PallLean.Paper93.DeepMath.PathB.ACC0EndToEndBT (endToEnd_BT)

variable {n : ℕ}

private theorem cast_ite {R : Type*} [CommRing R] (b : Bool) :
    (if b = true then (1 : R) else 0) = boolVal b := by
  cases b <;> simp [boolVal]

open Classical in
/-- **The satisfying-assignment count equals the sparse BT sum (PROVED).** -/
theorem bt_sharpSat_eq {R : Type*} [CommRing R] [Nontrivial R] (c : Circ n) :
    ((Finset.univ.filter (fun x => ACC0CircuitSubstitution.eval c x = true)).card : R)
      = ∑ d ∈ (subst (R := R) c).support, (subst c).coeff d * (2 : R) ^ (n - d.support.card) := by
  have hbt := endToEnd_BT (R := R) c
  rw [← hbt.2.2.2, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  rw [hbt.1 x, cast_ite]

open Classical in
/-- **#SAT is a quasipolynomial sum (PROVED): the count equals the sparse sum, whose support has `≤ (n+1)^{2^{depth+1}}`
features.** -/
theorem bt_sharpSat {R : Type*} [CommRing R] [Nontrivial R] (c : Circ n) :
    ((Finset.univ.filter (fun x => ACC0CircuitSubstitution.eval c x = true)).card : R)
        = ∑ d ∈ (subst (R := R) c).support, (subst c).coeff d * (2 : R) ^ (n - d.support.card)
      ∧ ((subst (R := R) c).support.image (fun d => d.support)).card
          ≤ (n + 1) ^ (2 ^ (ACC0LowDegreeSubstitution.depth c + 1)) :=
  ⟨bt_sharpSat_eq c, (endToEnd_BT (R := R) c).2.2.1⟩

/-!
**#SAT counting payoff, proved.**  The number of satisfying assignments of any general `Circ` circuit equals a sum over the
quasipolynomial monomial support of its BT representation — so `#SAT` is computable from the sparse polynomial in
quasipolynomial time, and SAT is decided by nonzeroness of the sum.  Remaining (open, not faked): the collapse socket to
`NEXP ⊄ ACC⁰` (P≠NP-strength).  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SharpSAT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SharpSAT.bt_sharpSat
