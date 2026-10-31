import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndForm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearize

/-!
# Brick (counting witness) — some function has no low-degree `F_p` representation (proved)

The counting (Shannon) not-low-degree witness, in the barrier's shape.  For `D < n`, the degree-`≤D` monomials number
strictly fewer than `2^n` (`degLeMonomials_card_lt`), so the degree-`≤D` representable functions `(Fin n → Bool) → F_p` —
which all lie in the span of the `(degLeMonomials)`-many `AND`-terms (`eval_eq_sum_andTerms`) — number at most
`p^{|degLeMonomials|} < p^{2^n}`, fewer than *all* functions.  Hence **some** function has no degree-`≤D` `F_p`
representation (`exists_no_lowdeg_repr`) — a genuine not-low-degree witness feeding the low-degree barrier.

This is the *counting* witness (a non-explicit function is hard).  The **explicit** witness for `MOD_q` (`q ≠ p`) is the
Razborov–Smolensky lower bound proper — the deep analytic theorem — which the tree carries separately in the
`BoolCircuitSyntax` formulation (`Layer4.mod_q_indicators_false`, `Layer3Smolensky.parity_function_lower_bound`); it is
**not** re-proved or faked here.

## What is proved (clean axioms, no `sorry`)

* **`degLeMonomials_card_lt`** (PROVED) — `D < n → (degLeMonomials n D).card < 2^n`.
* **`exists_no_lowdeg_repr`** (PROVED) — `D < n → ∃ g : (Fin n → Bool) → ZMod p, ¬∃ P, P.totalDegree ≤ D ∧ ∀ x, eval(bv∘x) P
  = g x`.

## Honest scope

This is the counting witness (existential, non-explicit).  It does **not** give the explicit `MOD_q` witness (RS lower
bound), handle `MOD_q`/prime-power gates, nor the Williams cash-out.  General YBT and `NEXP ⊄ ACC⁰` remain open.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CountingWitness

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0MonomialCount (degLeMonomials)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearize (support_card_le_totalDegree)
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndForm (andVal eval_eq_sum_andTerms)

variable {n p D : ℕ} [Fact p.Prime]

/-- **For `D < n`, the degree-`≤D` monomials are strictly fewer than `2^n` (PROVED).** -/
theorem degLeMonomials_card_lt (h : D < n) : (degLeMonomials n D).card < 2 ^ n := by
  have hlt : (degLeMonomials n D).card < (Finset.univ : Finset (Fin n)).powerset.card := by
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
      ⟨Finset.univ, Finset.mem_powerset.mpr (Finset.Subset.refl _), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and, Finset.card_univ, Fintype.card_fin]
    omega
  rwa [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] at hlt

/-- **The counting not-low-degree witness (PROVED): some `F_p`-valued function has no degree-`≤D` representation.** -/
theorem exists_no_lowdeg_repr (h : D < n) :
    ∃ g : (Fin n → Bool) → ZMod p,
      ¬ ∃ P : MvPolynomial (Fin n) (ZMod p),
        P.totalDegree ≤ D ∧ ∀ x, eval (fun i => (bv (x i) : ZMod p)) P = g x := by
  classical
  let andComb : (↥(degLeMonomials n D) → ZMod p) → ((Fin n → Bool) → ZMod p) :=
    fun c x => ∑ S : ↥(degLeMonomials n D), c S * andVal (S : Finset (Fin n)) x
  -- every representable function lies in the image of `andComb`
  have key : ∀ g : (Fin n → Bool) → ZMod p,
      (∃ P : MvPolynomial (Fin n) (ZMod p),
        P.totalDegree ≤ D ∧ ∀ x, eval (fun i => (bv (x i) : ZMod p)) P = g x) →
      g ∈ Finset.image andComb Finset.univ := by
    rintro g ⟨P, hdeg, hPg⟩
    have hmaps : ∀ e ∈ P.support, e.support ∈ degLeMonomials n D := by
      intro e he
      simp only [degLeMonomials, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, le_trans (support_card_le_totalDegree P e he) hdeg⟩
    refine Finset.mem_image.mpr
      ⟨fun S => ∑ e ∈ P.support.filter (fun e => e.support = S.val), coeff e P, Finset.mem_univ _, ?_⟩
    funext x
    show (∑ S : ↥(degLeMonomials n D),
        (∑ e ∈ P.support.filter (fun e => e.support = S.val), coeff e P) * andVal (S : Finset (Fin n)) x) = g x
    rw [Finset.sum_coe_sort (degLeMonomials n D)
        (fun T => (∑ e ∈ P.support.filter (fun e => e.support = T), coeff e P) * andVal T x),
      ← hPg x, eval_eq_sum_andTerms,
      ← Finset.sum_fiberwise_of_maps_to hmaps (fun e => coeff e P * andVal e.support x)]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [(Finset.mem_filter.mp he).2]
  -- the image is too small to be everything
  have hcard : (Finset.image andComb Finset.univ).card < Fintype.card ((Fin n → Bool) → ZMod p) := by
    calc (Finset.image andComb Finset.univ).card
        ≤ (Finset.univ : Finset (↥(degLeMonomials n D) → ZMod p)).card := Finset.card_image_le
      _ = p ^ (degLeMonomials n D).card := by
            rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe]
      _ < p ^ (2 ^ n) := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (degLeMonomials_card_lt h)
      _ = Fintype.card ((Fin n → Bool) → ZMod p) := by
            rw [Fintype.card_fun, ZMod.card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  -- hence some `g` is outside the image, so not representable
  obtain ⟨g, hg⟩ : ∃ g, g ∉ Finset.image andComb Finset.univ := by
    by_contra hc
    push_neg at hc
    rw [Finset.eq_univ_of_forall hc, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  exact ⟨g, fun hrep => hg (key g hrep)⟩

/-!
**The counting witness, proved.**  For `D < n`, some function has no degree-`≤D` `F_p` representation — feeding the low-degree
barrier, some function is not a bounded-degree `AC⁰[p]` circuit.  This is the Shannon (counting) lower bound; the explicit
`MOD_q` witness is the Razborov–Smolensky theorem (tree's `Layer4`/`Layer3Smolensky`), not re-proved here.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CountingWitness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingWitness.degLeMonomials_card_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountingWitness.exists_no_lowdeg_repr
