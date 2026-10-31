import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LowDegreeSubstitution
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AevalDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearisation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity

/-!
# Composite Beigel–Tarui capstone — the quasipolynomial low-degree sparse representation, packaged

This packages the proved approximation-side machinery into one theorem: a circuit whose gates are realised by
polynomials composed via `aeval` (each gate polynomial of degree `≤ δ`) has a **quasipolynomial low-degree sparse
`SYM∘AND` representation**.  Concretely, the circuit's polynomial `Q c` satisfies, with all remaining assumptions
explicit:

* **low degree** — `totalDegree (Q c) ≤ δ^{depth c + 1}` (quasipolynomial for constant depth);
* **quasipolynomially many features** — `#{distinct monomial supports} ≤ (n+1)^{δ^{depth c + 1}}`;
* **sparse cube count** — `∑ₓ eval (boolVal∘x) (Q c) = ∑_{d∈support} coeff_d · 2^{n-|supp d|}` (the sub-`2^n` count).

This is the cleanest remaining "ACC⁰-side" target: the composite-`MOD` low-degree representation, assembled from
`psubst_degree` (+ `aeval` degree discharge), `support_mem_lowDeg` (+ Beigel–Tarui count), and `multilinear_cube_sum`.

## What is proved (clean axioms, no `sorry`)

* **`compositeBT_representation`** — the packaged quasipoly low-degree sparse representation (the three bullets above),
  for any `aeval`-composed gate-polynomial assignment with degree-`≤ δ` gate polynomials.

## Explicit remaining assumptions

The theorem's hypotheses are exactly the residual content: the gate polynomials have degree `≤ δ` (`hgu`, `hgb` — what
the `OR`/`MOD` probabilistic polynomials of `…ACC0Mod6ProbabilisticPolynomial` / `…ACC0ProbabilisticAmplification`
provide), the substitution composes via `aeval` (`huna_eq`, `hbin_eq`), and `1 ≤ δ`.  Discharging the *error* side
(that `Q c` *approximates* the circuit, not just shares its degree) is the calibrated bound `circuit_error_bound` +
`error_calibration` (`< 2^n/10`), proved separately.  The genuinely open ACC⁰-side input is the gate polynomials
themselves for *composite* modulus (the composite probabilistic `SYM∘AND` construction).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeBTCapstone

open scoped Classical BigOperators
open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeSubstitution (depth psubst_degree)
open PallLean.Paper93.DeepMath.PathB.ACC0AevalDegree (binGate_degree unaGate_degree)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (boolVal support_mem_lowDeg multilinear_cube_sum)
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity (beigelTarui_monomial_count_le)
open PallLean.Paper93.DeepMath.PathB.Layer3 (lowDegMonomials)

/-- **Composite Beigel–Tarui representation (proved): an `aeval`-composed circuit polynomial is quasipolynomial,
low-degree, and sparse-countable.**  For a gate-polynomial assignment `Q` composed via `aeval` from degree-`≤ δ` gate
polynomials `gu`/`gb`, the circuit polynomial `Q c` has total degree `≤ δ^{depth+1}`, fewer than `(n+1)^{δ^{depth+1}}`
distinct monomial-supports, and a sparse cube count.  The quasipolynomial low-degree sparse representation. -/
theorem compositeBT_representation {n : ℕ} {R : Type*} [CommRing R]
    (Q : ACC0CircuitSubstitution.Circ n → MvPolynomial (Fin n) R)
    (gu : (Bool → Bool) → MvPolynomial (Fin 1) R) (gb : (Bool → Bool → Bool) → MvPolynomial (Fin 2) R)
    (δ : ℕ) (hδ : 1 ≤ δ)
    (hinp : ∀ i, (Q (.inp i)).totalDegree ≤ δ) (hcst : ∀ b, (Q (.cst b)).totalDegree ≤ δ)
    (hgu : ∀ f, (gu f).totalDegree ≤ δ) (hgb : ∀ g, (gb g).totalDegree ≤ δ)
    (huna_eq : ∀ f c, Q (.una f c) = aeval ![Q c] (gu f))
    (hbin_eq : ∀ g a b, Q (.bin g a b) = aeval ![Q a, Q b] (gb g))
    (c : ACC0CircuitSubstitution.Circ n) :
    (Q c).totalDegree ≤ δ ^ (depth c + 1)
      ∧ ((Q c).support.image (fun d => d.support)).card ≤ (n + 1) ^ (δ ^ (depth c + 1))
      ∧ (∑ x : Fin n → Bool, eval (fun i => (boolVal (x i) : R)) (Q c))
          = ∑ d ∈ (Q c).support, (Q c).coeff d * (2 : R) ^ (n - d.support.card) := by
  have hdeg : (Q c).totalDegree ≤ δ ^ (depth c + 1) := by
    refine psubst_degree Q δ hδ hinp hcst ?_ ?_ c
    · intro f c'
      rw [huna_eq]
      exact le_trans (unaGate_degree (gu f) (Q c')) (Nat.mul_le_mul (hgu f) (le_refl _))
    · intro g a b
      rw [hbin_eq]
      exact le_trans (binGate_degree (gb g) (Q a) (Q b)) (Nat.mul_le_mul (hgb g) (le_refl _))
  refine ⟨hdeg, ?_, multilinear_cube_sum (Q c)⟩
  refine le_trans (Finset.card_le_card ?_) (beigelTarui_monomial_count_le n (δ ^ (depth c + 1)))
  intro S hS
  rw [Finset.mem_image] at hS
  obtain ⟨d, hd, rfl⟩ := hS
  exact support_mem_lowDeg (Q c) hdeg hd

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeBTCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeBTCapstone.compositeBT_representation
