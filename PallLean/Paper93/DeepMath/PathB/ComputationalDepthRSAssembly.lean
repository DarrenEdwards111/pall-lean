import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitApproxTerm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultilinearize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWalshSpan
import Mathlib

/-!
# Razborov–Smolensky assembly (PROVED conditional) — circuit ⇒ low-degree Walsh approximator ⇒ separation

This file wires together the whole upper-bound arc:

  * `circuit_low_degree_approx` — an AC⁰[p] circuit is a low-degree `{0,1}` polynomial off a small bad set;
  * `Multilinearize.eval_eq_multilinear` — that polynomial is a `Multilinear.eval` (degree-preserving);
  * `WalshSpan.eval_eq_evalW` / `walshCoef_support` — the `{0,1}` multilinear poly is a `{−1,+1}` Walsh poly
    (degree-preserving).

  `circuit_walsh_approx` — **the assembled composition**: every well-formed AC⁰[p] circuit `C` is computed, on a
        set `G` with `|G| ≥ 2ⁿ − size(C)·2^(n-t)`, by a Walsh polynomial of degree `≤ (t(p−1))^depth(C)`.
  `no_acp_circuit` — **the conditional separation**: if a function `f` is *hard* (no degree-`d` Walsh polynomial
        agrees with `f` on a set larger than `B`), then no well-formed AC⁰[p] circuit of degree `≤ d` and small
        enough bad set computes `f`.  The hardness hypothesis is precisely the deep Razborov–Smolensky lower-bound
        direction (e.g. for `MOD_q`), here exposed as an explicit assumption — the only remaining gap to
        `MOD_q ∉ AC⁰[p]`.
-/

open MvPolynomial

namespace PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

variable {n : ℕ}

/-- **Circuit ⇒ low-degree Walsh approximator (assembled).**  Composes `circuit_low_degree_approx`,
`Multilinearize.eval_eq_multilinear`, and `WalshSpan.eval_eq_evalW`: every well-formed AC⁰[p] circuit `C` is
computed on a set `G` (with `|G| ≥ 2ⁿ − size(C)·2^(n-t)`) by a Walsh polynomial `evalW aCoef` whose coefficients
are supported on subsets of size `≤ (t(p−1))^depth(C)`. -/
theorem circuit_walsh_approx {p t : ℕ} [Fact p.Prime] (ht : 1 ≤ t) (htn : t ≤ n)
    (h2 : (2 : ZMod p) ≠ 0) (C : Circuit n) (hC : WF p C) :
    ∃ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
      (∀ T, (t * (p - 1)) ^ depth C < T.card → aCoef T = 0) ∧
      2 ^ n ≤ size C * 2 ^ (n - t) + G.card ∧
      ∀ x ∈ G, cf p C x = WalshSpan.evalW aCoef x := by
  obtain ⟨P, G, hdeg, hG, hagree⟩ := circuit_low_degree_approx ht htn C hC
  refine ⟨WalshSpan.walshCoef
      (fun S => ∑ d ∈ P.support.filter (fun d => d.support = S), P.coeff d), G, ?_, hG, ?_⟩
  · intro T hT
    exact WalshSpan.walshCoef_support _
      (fun S hS => Multilinearize.multilinear_coeff_support P S (lt_of_le_of_lt hdeg hS)) T hT
  · intro x hx
    rw [hagree x hx]
    simp only [pf]
    rw [Multilinearize.eval_eq_multilinear P x, WalshSpan.eval_eq_evalW h2]

/-- **Conditional separation.**  If `f` is hard — no degree-`d` Walsh polynomial agrees with `f` on a set of size
`> B` — then no well-formed AC⁰[p] circuit `C` with `(t(p−1))^depth(C) ≤ d` and `size(C)·2^(n-t) + B < 2ⁿ` computes
`f`.  The `hard` hypothesis is the deep Razborov–Smolensky lower bound (for `MOD_q`, the cited/open core); the rest
is the assembled upper-bound machinery.  Instantiating `hard` with the genuine `MOD_q` non-approximability closes
`MOD_q ∉ AC⁰[p]`. -/
theorem no_acp_circuit {p t : ℕ} [Fact p.Prime] (ht : 1 ≤ t) (htn : t ≤ n) (h2 : (2 : ZMod p) ≠ 0)
    (d B : ℕ) (f : (Fin n → Bool) → ZMod p)
    (hard : ∀ (aCoef : Finset (Fin n) → ZMod p) (G : Finset (Fin n → Bool)),
              (∀ T, d < T.card → aCoef T = 0) → (∀ x ∈ G, f x = WalshSpan.evalW aCoef x) → G.card ≤ B)
    (C : Circuit n) (hC : WF p C) (hdeg : (t * (p - 1)) ^ depth C ≤ d)
    (hCf : ∀ x, cf p C x = f x) (hsmall : size C * 2 ^ (n - t) + B < 2 ^ n) : False := by
  obtain ⟨aCoef, G, hsupp, hG, hagree⟩ := circuit_walsh_approx ht htn h2 C hC
  have hsupp' : ∀ T, d < T.card → aCoef T = 0 := fun T hT => hsupp T (lt_of_le_of_lt hdeg hT)
  have hagree' : ∀ x ∈ G, f x = WalshSpan.evalW aCoef x := fun x hx => by
    rw [← hCf]; exact hagree x hx
  have hGB := hard aCoef G hsupp' hagree'
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.circuit_walsh_approx
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.no_acp_circuit
