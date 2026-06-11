import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky

/-!
# Layer 4 (Route A, piece 3 — final assembly lemmas)

The two ingredients the §3-C note flagged as the last step before the end-to-end `MOD_q ∉ AC⁰[p]`:

* **`exists_tight_agreement_set`** — the **parameterised** agreement lemma.  Identical to Layer 3's
  `exists_large_agreement_set` (`p^t ≥ 4·s ⇒ 3·2ⁿ ≤ 4·|G|`) except the constant `4 ↦ 4q`: under the
  tighter horizon `p^t ≥ 4q·s` it gives the **tight complement bound** `4q·|cbadᵪ| ≤ 2ⁿ`, exactly the
  per-set hypothesis of `inter_three_quarters` (`ComputationalDepthLayer4Intersection`).  Reuses the same
  horizon-independent error count `composed_error_le` (`|cbad|·p^t ≤ s·2ⁿ`).

* **`hmod_of_isAC0p`** — the `AC⁰[p] ⇒ hmod` glue: `IsAC0pSyntax p C` implies every `MOD` gate in
  `subcircuits C` has modulus `p` (so `padTrue_isAC0pSyntax` discharges the `hmod` hypotheses of the
  agreement/approximant lemmas).  Via `isAC0p_of_mem_subcircuits` (subcircuits preserve `AC⁰[p]`) +
  `exists_of_mem_subcircuitsList`.

With these, the chain closes: padding (`padTrue_computes_indicator` + `padTrue_isAC0pSyntax` +
`padTrue_depth`) produces, from a `MOD_q ∈ AC⁰[p]` family, the `q` indicator circuits; `exists_tight_
agreement_set` + the base change (`exists_baseChanged_approximant`) give the tight indicator approximants;
`inter_three_quarters` combines their agreement sets to a `(3/4)`-set; `qary_reduction_from_indicators`
collapses the dimension there; `dim_contradiction_general` closes it.  (The final multi-residue parameter
thread + the degree→span bridge `eval_mem_lowDegSpan`-over-`K` is the remaining wiring.)
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset MvPolynomial
open Layer3 (toAgree oracleOf boolToZMod subcircuits composed_error_le self_mem_subcircuits FormSpace)

open Classical in
/-- **Parameterised (tight) agreement set.**  For an `AC⁰[p]` circuit with `p^t ≥ 4q·s`, there is a form
`ω` whose composed approximant disagrees with the circuit on at most a `1/(4q)` fraction:
`4q·|cbad| ≤ 2ⁿ`.  (Layer 3's `exists_large_agreement_set` is the `q = 1` case; same proof, constant
`4 ↦ 4q`.) -/
theorem exists_tight_agreement_set (p t q : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n)
    (hmod : ∀ a r cs, (BoolCircuitSyntax.modGate a r cs : BoolCircuitSyntax n) ∈ subcircuits C → a = p)
    (ht : 4 * q * (subcircuits C).toFinset.card ≤ p ^ t) :
    ∃ ω : FormSpace p t C,
      4 * q * (Finset.univ.filter (fun x : Fin n → Bool =>
          eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
            ≠ boolToZMod p (C.eval x))).card
        ≤ 2 ^ n := by
  obtain ⟨ω, hω⟩ := composed_error_le p t C hmod
  refine ⟨ω, ?_⟩
  set N := Fintype.card (Fin n → Bool) with hN
  set s := (subcircuits C).toFinset.card with hs
  set cb := (Finset.univ.filter (fun x : Fin n → Bool =>
    eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
      ≠ boolToZMod p (C.eval x))).card with hcb
  have hNeq : N = 2 ^ n := by rw [hN, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hs1 : 1 ≤ s := by
    rw [hs, Finset.one_le_card]; exact ⟨C, List.mem_toFinset.mpr (self_mem_subcircuits C)⟩
  have h1 : s * (4 * q * cb) ≤ s * N := by
    calc s * (4 * q * cb) = (4 * q * s) * cb := by ring
      _ ≤ p ^ t * cb := by gcongr
      _ = cb * p ^ t := by ring
      _ ≤ s * N := hω
  rw [← hNeq]; exact Nat.le_of_mul_le_mul_left h1 hs1

/-- A member of `subcircuitsList cs` is a subcircuit of some list element. -/
theorem exists_of_mem_subcircuitsList {n : ℕ} (G : BoolCircuitSyntax n) :
    ∀ (cs : List (BoolCircuitSyntax n)), G ∈ Layer3.subcircuitsList cs →
      ∃ c ∈ cs, G ∈ subcircuits c
  | [], hG => by simp [Layer3.subcircuitsList] at hG
  | c :: cs, hG => by
      simp only [Layer3.subcircuitsList, List.mem_append] at hG
      rcases hG with hG | hG
      · exact ⟨c, List.mem_cons_self .., hG⟩
      · obtain ⟨c', hc', hG'⟩ := exists_of_mem_subcircuitsList G cs hG
        exact ⟨c', List.mem_cons_of_mem _ hc', hG'⟩

/-- **`AC⁰[p]` is inherited by subcircuits.** -/
theorem isAC0p_of_mem_subcircuits {n p : ℕ} :
    ∀ (C : BoolCircuitSyntax n), BoolCircuitSyntax.IsAC0pSyntax p C →
      ∀ G ∈ subcircuits C, BoolCircuitSyntax.IsAC0pSyntax p G
  | .const b, h, G, hG => by simp only [subcircuits, List.mem_singleton] at hG; subst hG; exact h
  | .input i, h, G, hG => by simp only [subcircuits, List.mem_singleton] at hG; subst hG; exact h
  | .not c, h, G, hG => by
      simp only [subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact h
      · simp only [BoolCircuitSyntax.IsAC0pSyntax] at h
        exact isAC0p_of_mem_subcircuits c h G hG
  | .orGate cs, h, G, hG => by
      simp only [subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact h
      · simp only [BoolCircuitSyntax.IsAC0pSyntax] at h
        obtain ⟨c, hc, hGc⟩ := exists_of_mem_subcircuitsList G cs hG
        exact isAC0p_of_mem_subcircuits c (h c hc) G hGc
  | .andGate cs, h, G, hG => by
      simp only [subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact h
      · simp only [BoolCircuitSyntax.IsAC0pSyntax] at h
        obtain ⟨c, hc, hGc⟩ := exists_of_mem_subcircuitsList G cs hG
        exact isAC0p_of_mem_subcircuits c (h c hc) G hGc
  | .modGate q r cs, h, G, hG => by
      simp only [subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact h
      · simp only [BoolCircuitSyntax.IsAC0pSyntax] at h
        obtain ⟨c, hc, hGc⟩ := exists_of_mem_subcircuitsList G cs hG
        exact isAC0p_of_mem_subcircuits c (h.2 c hc) G hGc

/-- **`AC⁰[p] ⇒ hmod`.**  An `AC⁰[p]` circuit has only `MOD_p` gates among its subcircuits — exactly the
`hmod` hypothesis of the agreement/approximant lemmas, dischargeable from `padTrue_isAC0pSyntax`. -/
theorem hmod_of_isAC0p {n p : ℕ} (C : BoolCircuitSyntax n) (h : BoolCircuitSyntax.IsAC0pSyntax p C)
    (a r cs) (hG : (BoolCircuitSyntax.modGate a r cs : BoolCircuitSyntax n) ∈ subcircuits C) :
    a = p := by
  have h2 := isAC0p_of_mem_subcircuits C h _ hG
  simp only [BoolCircuitSyntax.IsAC0pSyntax] at h2
  exact h2.1

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.exists_tight_agreement_set
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.hmod_of_isAC0p
