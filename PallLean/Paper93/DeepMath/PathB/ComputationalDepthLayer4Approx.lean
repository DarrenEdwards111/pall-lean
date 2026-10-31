import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4WeightRepr
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4BaseChange
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky

/-!
# Layer 4 (Route A, piece 3 — circuit side) — base-changed approximants over `F_{p^{q-1}}`

This carries the Layer-3 agreement machinery into the extension field `K = F_{p^{q-1}}`, supplying the
indicator approximants `(p_j, A_j)` that `qary_reduction_from_indicators`
(`ComputationalDepthLayer4WeightRepr`) takes as hypotheses.

* **`exists_baseChanged_approximant`** — for an `AC⁰[p]` circuit `C` on `2m+1` variables (`p^t ≥
  4·#subcircuits`), the base change `map φ (toAgree …)` along any ring hom `φ : ZMod p → K` is a
  polynomial over `K` of degree `≤ ((p-1)t)^{depth C}` agreeing with `boolToField K (C.eval ·)` on the
  agreement set `G` (`|G| ≥ (3/4)·2ⁿ`).  Combines `exists_large_agreement_set` (F_p agreement) +
  `toAgree_totalDegree_le` (degree) + brick 1 (`totalDegree_map_le`, `eval_map_comm`); the eval points
  match because `φ(boolToZMod b) = boolToField K b`.

* **`exists_indicator_approximant`** — specialising to a circuit that **computes** the residue indicator
  `[#ones ≡ j]` (`C.eval x = decide(#ones%q = j)`): its base-changed approximant equals `modIndicator K q j`
  on `G`.  This is exactly one `hp`-component of `qary_reduction_from_indicators`.

**What this leaves (the genuine residual circuit content, not faked):** to discharge *all* of
`qary_reduction_from_indicators`'s hypotheses one needs, for each `j < q`, a circuit `C_j` that *computes*
`[#ones ≡ j]` and is `AC⁰[p]` — i.e. the **padding construction** `[#ones ≡ j] = MOD_q(x ‖ (q-j)·⟨true⟩)`
in `BoolCircuitSyntax` from a `MOD_q ∈ AC⁰[p]` family — together with the intersection bookkeeping
(`G = ⋂_j G_j` needs each `|G_jᶜ| ≤ 2ⁿ/(4q)`, i.e. the horizon `p^t ≥ 4q·s`).  These are circuit-level
constructions over `BoolCircuitSyntax`, the remaining work; `exists_indicator_approximant`'s hypothesis
`hCind` (`C` computes the indicator) is where that construction would plug in.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset MvPolynomial
open Layer3 (toAgree oracleOf boolToZMod subcircuits exists_large_agreement_set toAgree_totalDegree_le)

open Classical in
/-- **Base-changed approximant.**  For an `AC⁰[p]` circuit `C` (with `p^t ≥ 4·#subcircuits`) and any ring
hom `φ : ZMod p → K`, `map φ (toAgree …)` is a degree-`≤((p-1)t)^{depth C}` polynomial over `K` agreeing
with `boolToField K (C.eval ·)` on the agreement set `G` (`|G| ≥ (3/4)·2ⁿ`). -/
theorem exists_baseChanged_approximant (p t : ℕ) [Fact p.Prime] {K : Type*} [Field K]
    (φ : ZMod p →+* K) {m : ℕ} (C : BoolCircuitSyntax (2 * m + 1))
    (hmod : ∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits C → q = p)
    (ht : 4 * (subcircuits C).toFinset.card ≤ p ^ t) (ht1 : 1 ≤ t) :
    ∃ (g : MvPolynomial (Fin (2 * m + 1)) K) (G : Finset (Fin (2 * m + 1) → Bool)),
      3 * 2 ^ (2 * m + 1) ≤ 4 * G.card ∧ g.totalDegree ≤ ((p - 1) * t) ^ C.depth ∧
      ∀ x ∈ G, eval (fun i => boolToField K (x i)) g = boolToField K (C.eval x) := by
  obtain ⟨ω, hGsize⟩ := exists_large_agreement_set p t C hmod ht
  refine ⟨MvPolynomial.map φ (toAgree p t (oracleOf p t C ω) C),
    Finset.univ.filter (fun x : Fin (2 * m + 1) → Bool =>
      eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C) = boolToZMod p (C.eval x)),
    hGsize, le_trans (totalDegree_map_le φ _) (toAgree_totalDegree_le p t ht1 _ C), ?_⟩
  intro x hx
  rw [Finset.mem_filter] at hx
  have hpt : (fun i => boolToField K (x i)) = (fun i => φ (boolToZMod p (x i))) := by
    funext i; cases x i <;> simp [boolToField, boolToZMod]
  rw [hpt, eval_map_comm, hx.2]
  cases C.eval x <;> simp [boolToField, boolToZMod]

open Classical in
/-- **Indicator approximant.**  If `C` *computes* the residue indicator `[#ones ≡ j]` and is `AC⁰[p]`,
its base-changed approximant equals `modIndicator K q j` on `G` — one `hp`-component of
`qary_reduction_from_indicators`. -/
theorem exists_indicator_approximant (p t : ℕ) [Fact p.Prime] {K : Type*} [Field K]
    (φ : ZMod p →+* K) {m : ℕ} (q j : ℕ) (C : BoolCircuitSyntax (2 * m + 1))
    (hmod : ∀ a r cs, (BoolCircuitSyntax.modGate a r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits C → a = p)
    (ht : 4 * (subcircuits C).toFinset.card ≤ p ^ t) (ht1 : 1 ≤ t)
    (hCind : ∀ x : Fin (2 * m + 1) → Bool,
      C.eval x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = j)) :
    ∃ (g : MvPolynomial (Fin (2 * m + 1)) K) (G : Finset (Fin (2 * m + 1) → Bool)),
      3 * 2 ^ (2 * m + 1) ≤ 4 * G.card ∧ g.totalDegree ≤ ((p - 1) * t) ^ C.depth ∧
      ∀ x ∈ G, eval (fun i => boolToField K (x i)) g = modIndicator K q j x := by
  obtain ⟨g, G, hG, hdeg, heval⟩ := exists_baseChanged_approximant p t φ C hmod ht ht1
  refine ⟨g, G, hG, hdeg, fun x hx => ?_⟩
  rw [heval x hx, hCind x]
  simp only [boolToField, modIndicator, decide_eq_true_eq]

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.exists_baseChanged_approximant
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.exists_indicator_approximant
