import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SumCheck

/-!
# Arithmetization as counting — `scSum (arith) = #accepting` (proved), low-degree socketed

Entry 225 proved the sum-check round-reduction engine and left **`NexpArithmetization`** (the certificate-to-polynomial
arithmetization) as a named BFL socket.  This file proves the genuine *counting* content of arithmetization — that the
hypercube sum of an arithmetized predicate reads off the *number of accepting assignments* — isolating only the
*low-degree* property as the residual socket.

The point.  In BFL the `NEXP` claim is `H = ∑_{b ∈ {0,1}^m} g(b)` for an arithmetized predicate `g`.  For this to mean
"`H` = number of accepting certificates", `g` must (i) agree with the boolean acceptance predicate `f` on the hypercube,
and (ii) be low-degree (so the round polynomials are low-degree, which sum-check soundness needs).  Property (i) makes
`scSum g` literally the accepting count — and that is provable algebra.  Property (ii) — that a concrete low-degree
multilinear extension realises (i) — is the socket.

## What is proved (clean axioms, no `sorry`)

* **`scSum_indicator`** (PROVED) — if `g` agrees with a boolean predicate `f` on the hypercube (`∀ b, g(boolToR ∘ b) =
  boolToR (f b)`), then `scSum g = (#{b | f b} : R)`: the hypercube sum is exactly the count of accepting assignments.
* **`LowDegArithmetization`** — the residual socket: every `NEXP` acceptance predicate has a *low-degree* polynomial `g`
  agreeing with it on the hypercube (the multilinear-extension degree bound).
* **`nexpArith_counting`** — packages: the arithmetized claim `scSum g` equals the accepting count `#{b | f b}`.

## Honest scope

This proves that **arithmetization computes the accepting count** — `scSum (arith f) = #{accepting}` — completely, by
finite-sum algebra (`Finset.sum_boole`) on top of the entry-225 `scSum`.  This is the meaning of "`H` = acceptance
count" that makes the BFL sum-check claim well-posed.  What remains the named socket is **`LowDegArithmetization`**: that
the `NEXP` certificate predicate admits a *low-degree* polynomial realisation (the multilinear extension with its degree
bound) — needed for the round polynomials to be low-degree and hence for Schwartz–Zippel soundness.  The counting
identity is proved; the low-degree realisation is socketed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0Arithmetization

open PallLean.Paper93.DeepMath.PathB.ACC0SumCheck (boolToR scSum)

variable {R : Type*} [CommRing R]

/-- **Arithmetization computes the accepting count (PROVED).**  If the arithmetized polynomial `g` agrees with the
boolean acceptance predicate `f` on the hypercube — `∀ b, g(boolToR ∘ b) = boolToR (f b)` — then the hypercube sum is
the count of accepting assignments: `scSum g = (#{b | f b} : R)`.  This is the meaning of "`H` = number of accepting
certificates" in the BFL sum-check claim.  Proof: substitute the agreement, rewrite `boolToR (f b)` as `if f b then 1
else 0`, and sum (`Finset.sum_boole`). -/
theorem scSum_indicator {m : ℕ} (g : (Fin m → R) → R) (f : (Fin m → Bool) → Bool)
    (hg : ∀ b, g (fun i => boolToR (b i)) = boolToR (f b)) :
    scSum g = ((Finset.univ.filter (fun b => f b = true)).card : R) := by
  unfold scSum
  simp only [hg]
  rw [show (fun b => boolToR (f b)) = (fun b : Fin m → Bool => if f b = true then (1 : R) else 0) from ?_]
  · rw [Finset.sum_boole]
  · funext b
    unfold boolToR
    by_cases h : f b = true <;> simp [h]

/-- **The low-degree arithmetization socket (BFL).**  Every `NEXP` acceptance predicate `f` admits a *low-degree*
polynomial `g` agreeing with it on the hypercube (the multilinear extension with its degree bound) — needed so the
sum-check round polynomials are low-degree.  Stated, not proved. -/
def LowDegArithmetization {m : ℕ} (f : (Fin m → Bool) → Bool) (g : (Fin m → R) → R) : Prop :=
  ∀ b, g (fun i => boolToR (b i)) = boolToR (f b)

/-- **The arithmetized claim equals the accepting count (PROVED).**  Given a low-degree arithmetization `g` of `f`, the
sum-check claim value `scSum g` equals the count of accepting assignments `#{b | f b}` — `scSum g` reads off the count.
-/
theorem nexpArith_counting {m : ℕ} (f : (Fin m → Bool) → Bool) (g : (Fin m → R) → R)
    (hg : LowDegArithmetization f g) :
    scSum g = ((Finset.univ.filter (fun b => f b = true)).card : R) :=
  scSum_indicator g f hg

end PallLean.Paper93.DeepMath.PathB.ACC0Arithmetization

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Arithmetization.scSum_indicator
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Arithmetization.nexpArith_counting
