import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModResidueSpeedup

/-!
# Smallest nontrivial depth-3 normalization: a boolean combination of `MOD` gates

The support normal form (`…ACC0SupportNormalForm`) gives a gain only for *juntas* (circuits reading few variables).
The genuine `MOD` gain is different: a `MOD_q` gate may read **all `n`** variables yet has only `q` residue states.
This file normalizes the smallest syntactic depth-3 `ACC⁰` fragment that exploits it — a boolean combination of
`MOD` gates — into the residue observer form, and gets `< 2^n` search automatically.

Concretely, a syntactic `ACC0Circuit` of the form `(MOD_{q₁}) ∧ (MOD_{q₂})` (or any top function of finitely many
`MOD` gates) equals a `Depth2ModCircuit` whose top folds the boolean structure, so it is residue-searchable in
`≤ ∏ q_i` cells — `< 2^n` when `∏ q_i < 2^n`, **independent of the gate supports** (which may be all of `[n]`,
where the junta/projection bound `2^{|support|} = 2^n` gives nothing).

## What is proved (clean axioms, no `sorry`)

* `mod_bottom_circuit_searchable` — an *arbitrary* top function of a family of `MOD` gates is residue-searchable in
  `< 2^n` cells when `∏ q_i < 2^n` (the depth-`d`-above-`MOD` fragment; the AC⁰ structure folds into `top`).
* `and_of_mods_searchable` — **the smallest syntactic case**: the `ACC0Circuit` `(MOD_{q₁} S₁ t₁) ∧ (MOD_{q₂} S₂ t₂)`
  normalizes to a `Depth2ModCircuit` and is residue-searchable in `< 2^n` cells when `q₁·q₂ < 2^n`, regardless of
  `S₁, S₂`.

## Honest scope

A genuine syntactic depth-3 normalization exploiting the residue gain: `MOD`-combination circuits collapse to the
residue observer, searchable below brute force with no support restriction.  It does **not** prove the full
Yao–Beigel–Tarui reduction (an arbitrary `ACC⁰` circuit to a `MOD`/small-support bottom — the deep step, still open):
here the `MOD`-bottom structure is given, not derived from an arbitrary circuit.  Still the cell-count model;
nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Depth3ModNormalize

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup

variable {n : ℕ}

/-- **An arbitrary top function of a `MOD`-gate family is residue-searchable (proved).**  `∏ q_i < 2^n` ⇒ the
residue cell search decides the circuit's SAT in `< 2^n` cells — independent of the gate supports.  The AC⁰
structure above the `MOD` layer folds into `top`. -/
theorem mod_bottom_circuit_searchable {m : ℕ} (gates : Fin m → ModGate n)
    (hpos : ∀ i, 0 < (gates i).modulus) (top : (Fin m → Bool) → Bool)
    (hregime : (∏ i, (gates i).modulus) < 2 ^ n) :
    ∃ G : ((j : Fin m) → ZMod (gates j).modulus) → Bool,
      (Satisfiable (Depth2ModCircuit.eval ⟨gates, top⟩)
        ↔ ∃ v ∈ Finset.univ.image (modResVec ⟨gates, top⟩), G v = true)
      ∧ (Finset.univ.image (modResVec ⟨gates, top⟩)).card < 2 ^ n :=
  mod_circuit_sat_speedup ⟨gates, top⟩ hpos hregime

/-- **The smallest syntactic depth-3 normalization (proved): `MOD_{q₁} ∧ MOD_{q₂}` is residue-searchable.**  The
`ACC0Circuit` `and (mod q₁ S₁ t₁) (mod q₂ S₂ t₂)` equals a `Depth2ModCircuit` (top `= ∧`), so its SAT is decided by
a residue search over `< 2^n` cells when `q₁·q₂ < 2^n` — even when `S₁ = S₂ = univ` (where the junta bound `2^n`
gives nothing). -/
theorem and_of_mods_searchable {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (S₁ S₂ : Finset (Fin n)) (t₁ : ZMod q₁) (t₂ : ZMod q₂) (hregime : q₁ * q₂ < 2 ^ n) :
    ∃ C : Depth2ModCircuit n 2,
      (∀ x, eval (ACC0Circuit.and (.mod q₁ S₁ t₁) (.mod q₂ S₂ t₂)) x = C.eval x)
        ∧ (Finset.univ.image (modResVec C)).card < 2 ^ n := by
  refine ⟨⟨![⟨q₁, S₁, t₁⟩, ⟨q₂, S₂, t₂⟩], fun v => v 0 && v 1⟩, fun x => rfl, ?_⟩
  have hpos : ∀ i : Fin 2,
      0 < ((⟨![⟨q₁, S₁, t₁⟩, ⟨q₂, S₂, t₂⟩], fun v => v 0 && v 1⟩ : Depth2ModCircuit n 2).gates i).modulus := by
    intro i
    fin_cases i
    · exact Nat.pos_of_ne_zero (NeZero.ne q₁)
    · exact Nat.pos_of_ne_zero (NeZero.ne q₂)
  refine lt_of_le_of_lt (residue_cell_count_le _ hpos) ?_
  rw [Fin.prod_univ_two]
  exact hregime

end PallLean.Paper93.DeepMath.PathB.ACC0Depth3ModNormalize

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Depth3ModNormalize.mod_bottom_circuit_searchable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Depth3ModNormalize.and_of_mods_searchable
