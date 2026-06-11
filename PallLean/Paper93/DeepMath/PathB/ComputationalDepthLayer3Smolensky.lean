import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Agreement
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DimensionCount

/-!
# Layer 3 — the Razborov–Smolensky contradiction assembled

This file ties the two halves of the Razborov–Smolensky AC⁰[p] lower bound together.

* **Agreement side** (`ComputationalDepthLayer3Agreement`): `composed_error_le` /
  `exists_large_agreement_set` — an `AC⁰[p]` circuit's composed low-degree approximant agrees with the
  circuit on a `(3/4)` fraction of inputs.
* **Dimension side** (`ComputationalDepthLayer3DimensionCount`): `smolensky_contradiction` — if the full
  `±1` product `χ_univ` has a degree-`Δ` representative on such a large agreement set `G`, with the band
  margin window, then `False`.

The bridge between them is the observation that `χ_univ(x) = ∏ᵢ pmOne(xᵢ) = (-1)^{#ones} = pmOne(parity x)`:
**if the circuit computes parity** (`∏ᵢ pmOne(xᵢ) = pmOne(C.eval x)`), then `1 - 2·g_C` is a low-degree
representative of `χ_univ` on `G` (using `pmOne b = 1 - 2·boolToZMod b`).  Assembling all three gives
`parity_circuit_false`: no parity-computing `AC⁰[p]` circuit can simultaneously have a low-degree
approximant (small size/depth) and enough agreement (large time horizon) — the Razborov–Smolensky
size–depth tradeoff for `PARITY`.

The only remaining *mathematical* inputs are the explicit hypotheses of `parity_circuit_false`: that the
circuit computes parity (the statement being refuted), that it is `AC⁰[p]`, that `p` is odd, the
`toAgree`-degree bound (the degree side, `((p-1)t)^depth`), and the parameter conditions
`pᵗ ≥ 4·#subcircuits` and `16Δ² < 2m+3` (whose simultaneous satisfiability for a *small* circuit is the
size lower bound).
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open MvPolynomial

/-- `pmOne b = 1 - 2·boolToZMod b` (the `{0,1} ↦ ±1` linear change of variable, over any `ZMod p`). -/
theorem pmOne_eq_one_sub_two_boolToZMod (p : ℕ) (b : Bool) :
    pmOne p b = 1 - 2 * boolToZMod p b := by cases b <;> simp [pmOne, boolToZMod] <;> ring

/-- **The `MOD_q ↔ χ_univ` bridge.**  If `g_C` is a degree-`≤Δ` polynomial agreeing on `G` with the
circuit value `boolToZMod(C.eval ·)`, and the circuit **computes parity** in the sense
`∏ᵢ pmOne(xᵢ) = pmOne(C.eval x)`, then `1 - 2·g_C` is a degree-`≤Δ` polynomial representing the full
`±1` product `χ_univ = ∏ᵢ pmOne(xᵢ)` on `G`.  (`χ_univ(x) = pmOne(C.eval x) = 1 - 2·boolToZMod(C.eval x)`
and `g_C` realises `boolToZMod(C.eval ·)` on `G`.)  This is the genuinely function-specific step:
parity is exactly the function whose `AC⁰[p]` approximant yields a low-degree `χ_univ`. -/
theorem chi_univ_repr (p : ℕ) [Fact p.Prime] {n : ℕ} (G : Finset (Fin n → Bool)) (Δ : ℕ)
    (Cir : BoolCircuitSyntax n) (gC : MvPolynomial (Fin n) (ZMod p)) (hdeg : gC.totalDegree ≤ Δ)
    (hagree : ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) gC = boolToZMod p (Cir.eval x))
    (hpar : ∀ x : Fin n → Bool, (∏ i, pmOne p (x i)) = pmOne p (Cir.eval x)) :
    ∃ g : MvPolynomial (Fin n) (ZMod p), g.totalDegree ≤ Δ ∧
      ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) g = ∏ i, pmOne p (x i) := by
  refine ⟨1 - 2 * gC, ?_, ?_⟩
  · refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
    · rw [totalDegree_one]; exact Nat.zero_le Δ
    · rw [show (2 : MvPolynomial (Fin n) (ZMod p)) = MvPolynomial.C 2 from (map_ofNat MvPolynomial.C 2).symm]
      exact le_trans (totalDegree_mul _ _) (by rw [totalDegree_C, zero_add]; exact hdeg)
  · intro x hx
    rw [map_sub, map_one, map_mul, map_ofNat, hagree x hx, ← pmOne_eq_one_sub_two_boolToZMod]
    exact (hpar x).symm

open Classical in
/-- **The Razborov–Smolensky contradiction for `PARITY`.**  Let `Cir` be an `AC⁰[p]` circuit on
`2m+1` variables (`p` odd) that **computes parity** (`∏ᵢ pmOne(xᵢ) = pmOne(Cir.eval x)`).  Suppose, at
time horizon `t`, its composed approximant `toAgree` has total degree `≤ Δ`, the horizon satisfies
`pᵗ ≥ 4·#subcircuits` (so the agreement set covers `≥ 3/4` of the cube), and the band-margin window
`16Δ² < 2m+3` holds (so `Δ = O(√m)`).  Then `False`.

In other words: a parity-computing `AC⁰[p]` circuit cannot simultaneously achieve a degree-`Δ`
approximant **and** the agreement-horizon and band-margin conditions — the obstruction whose
quantitative form (`Δ ≈ ((p-1)t)^depth` small `vs` `pᵗ ≥ 4·size`) is the `PARITY ∉ AC⁰[p]` lower bound.
This assembles `exists_large_agreement_set` (agreement-set size), `chi_univ_repr` (the parity bridge),
and `smolensky_contradiction` (the dimension contradiction). -/
theorem parity_circuit_false (p : ℕ) [Fact p.Prime] {m Δ : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (Cir : BoolCircuitSyntax (2 * m + 1)) (t : ℕ)
    (hpar : ∀ x : Fin (2 * m + 1) → Bool, (∏ i, pmOne p (x i)) = pmOne p (Cir.eval x))
    (hmod : ∀ q r cs,
      (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits Cir → q = p)
    (htoAgreeDeg : ∀ ω : FormSpace p t Cir, (toAgree p t (oracleOf p t Cir ω) Cir).totalDegree ≤ Δ)
    (ht : 4 * (subcircuits Cir).toFinset.card ≤ p ^ t) (hwindow : 16 * Δ ^ 2 < 2 * m + 3) : False := by
  obtain ⟨ω, hGsize⟩ := exists_large_agreement_set p t Cir hmod ht
  set G := Finset.univ.filter (fun x : Fin (2 * m + 1) → Bool =>
    eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t Cir ω) Cir)
      = boolToZMod p (Cir.eval x)) with hG
  have hagree : ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t Cir ω) Cir)
      = boolToZMod p (Cir.eval x) := by
    intro x hx; rw [hG, Finset.mem_filter] at hx; exact hx.2
  obtain ⟨g, hgdeg, hgeval⟩ := chi_univ_repr p G Δ Cir (toAgree p t (oracleOf p t Cir ω) Cir)
    (htoAgreeDeg ω) hagree hpar
  exact smolensky_contradiction p hp2 G g hgdeg hgeval hwindow hGsize

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.pmOne_eq_one_sub_two_boolToZMod
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.chi_univ_repr
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.parity_circuit_false
