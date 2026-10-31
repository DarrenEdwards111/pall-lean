import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDimensionGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukOptimalBound

/-!
# N-Frame: the joint thermodynamic budget, wired to the Nečiporuk kernel

The dimension no-go (`boundaryDim_le_three`) showed the separating content of the boundary model is the **joint** budget:
volume (energy) under a width (dimension) constraint.  This file builds that joint invariant and — the payoff — wires it
to the repo's *proved* Nečiporuk `n²/log n` kernel, giving the boundary model its **first genuine, unconditional tearing
bound** on a concrete target.

  `budgetAt w f` — the joint invariant: minimal volume among width-`≤ w` transducers computing `f` (energy at bounded
        dimension).
  `exists_width_le_three` / `budgetAt_anti` / `budget_le_budgetAt` — **PROVED**: basic laws — everything is realisable at
        dimension `3`, relaxing the dimension can only lower the energy, and the free budget is the cheapest.

**The wire.**  A boundary transducer *is* a full-binary-basis formula: `toBFormula` translates `Trans` to the Nečiporuk
arc's `BFormula` preserving semantics, with `litCount ≤ volume`.  The kernel's optimal bound
(`NecHard.hardF_rate_sq_opt`, the real `n²/log n` Nečiporuk lower bound proved in this repo) then transfers:

  `volume_hardF_lower` / `volume_hardF_family` — **PROVED, UNCONDITIONAL**: every boundary transducer computing the
        indexed-storage-access function `hardF` has volume `≥ N²/(64·b)` — super-linear energy, at *any* width.
  `budgetAt_hardF_lower` — **PROVED, UNCONDITIONAL, the joint tearing bound**: for every dimension budget `w ≥ 3`,
        `budgetAt w hardF ≥ N²/(64·b)`.  A concrete target provably tears the thermodynamic budget of *every* admissible
        bounded-dimension boundary embedding — the first real "tearing" quantity of the boundary programme.

## Honest scope — real tearing, polynomial magnitude

This is a genuine, hypothesis-free lower bound in the boundary model, inherited from the repo's proved kernel — the
boundary programme now *has* an unconditional separating instance (`hardF` is not computable by any `o(N²/log N)`-energy
boundary observer).  Its honest magnitude: `N²/log N` is super-linear but **polynomial** — Nečiporuk's method provably
tops out there (the repo's own no-go shows the crossing-bottleneck bridge to `TC⁰`/`NC¹`/width-5 BPs is false), and the
transducer model is a *formula* (tree) model, weaker than general circuits.  So this bound tears the boundary but does not
approach `P vs NP`; a super-polynomial joint gap would need lower-bound technology beyond Nečiporuk (formula/BP-strength,
open).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### The joint invariant: energy at bounded dimension -/

/-- The **joint thermodynamic budget**: the minimal volume (energy) among width-`≤ w` (dimension-bounded) transducers
computing `f`. -/
noncomputable def budgetAt (w : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {v | ∃ t : Trans n, eval t = f ∧ width t ≤ w ∧ volume t = v}

/-- **Everything is realisable at dimension `3` (proved)** — the DNF caterpillar, so `budgetAt w f` is a genuine minimum
for every `w ≥ 3`. -/
theorem exists_width_le_three (f : (Fin n → Bool) → Bool) :
    ∃ t : Trans n, eval t = f ∧ width t ≤ 3 :=
  ⟨dnfFor f, eval_dnfFor f, width_dnfOn _⟩

/-- **Relaxing the dimension can only lower the energy (proved).** -/
theorem budgetAt_anti {f : (Fin n → Bool) → Bool} {w w' : ℕ} (hww' : w ≤ w')
    (hne : ∃ t : Trans n, eval t = f ∧ width t ≤ w) :
    budgetAt w' f ≤ budgetAt w f := by
  obtain ⟨t0, he0, hw0⟩ := hne
  have hne' : {v | ∃ t : Trans n, eval t = f ∧ width t ≤ w ∧ volume t = v}.Nonempty :=
    ⟨volume t0, t0, he0, hw0, rfl⟩
  unfold budgetAt
  obtain ⟨t, he, hw, hv⟩ := Nat.sInf_mem hne'
  rw [← hv]
  exact Nat.sInf_le ⟨t, he, le_trans hw hww', rfl⟩

/-- **The free budget is the cheapest (proved)**: dropping the dimension constraint can only lower the energy. -/
theorem budget_le_budgetAt {f : (Fin n → Bool) → Bool} (w : ℕ)
    (hne : ∃ t : Trans n, eval t = f ∧ width t ≤ w) :
    budget f ≤ budgetAt w f := by
  obtain ⟨t0, he0, hw0⟩ := hne
  have hne' : {v | ∃ t : Trans n, eval t = f ∧ width t ≤ w ∧ volume t = v}.Nonempty :=
    ⟨volume t0, t0, he0, hw0, rfl⟩
  unfold budgetAt
  obtain ⟨t, he, _, hv⟩ := Nat.sInf_mem hne'
  rw [← hv]
  exact Nat.sInf_le ⟨t, he, rfl⟩

/-! ### The wire: boundary transducers are Nečiporuk formulas -/

/-- Translate a boundary transducer to a full-binary-basis formula of the Nečiporuk arc. -/
def toBFormula : Trans n → BFormula n
  | .var i => BFormula.lit i true
  | .cst b => BFormula.cst b
  | .un op t => BFormula.un op (toBFormula t)
  | .bin op t₁ t₂ => BFormula.bin op (toBFormula t₁) (toBFormula t₂)

/-- **Semantics are preserved (proved).** -/
theorem eval_toBFormula (t : Trans n) (x : Fin n → Bool) :
    BFormula.eval (toBFormula t) x = eval t x := by
  induction t with
  | var i => rfl
  | cst b => rfl
  | un op t ih => simp [toBFormula, BFormula.eval, eval, ih]
  | bin op t₁ t₂ ih₁ ih₂ => simp [toBFormula, BFormula.eval, eval, ih₁, ih₂]

/-- **The formula's leaf count is dominated by the transducer's volume (proved).** -/
theorem litCount_toBFormula_le (t : Trans n) :
    BFormula.litCount (toBFormula t) ≤ volume t := by
  induction t with
  | var i => simp [toBFormula, BFormula.litCount, volume]
  | cst b => simp [toBFormula, BFormula.litCount, volume]
  | un op t ih => simp only [toBFormula, BFormula.litCount, volume]; omega
  | bin op t₁ t₂ ih₁ ih₂ => simp only [toBFormula, BFormula.litCount, volume]; omega

/-! ### The tearing bound: `hardF` needs super-linear energy at every dimension -/

/-- **Boundary volume lower bound for `hardF` (proved, unconditional).**  Every boundary transducer computing the
indexed-storage-access function has volume `≥ N²/(64·b)` — inherited from the repo's proved Nečiporuk kernel via the
wire. -/
theorem volume_hardF_lower {b m : ℕ} (hb : 5 ≤ b)
    (hlo : 2 ^ b ≤ 2 * (m * b)) (hhi : m * b ≤ 2 ^ b)
    (t : Trans (NecHard.nn b m)) (ht : eval t = NecHard.hardF) :
    (NecHard.nn b m) ^ 2 / (64 * b) ≤ volume t := by
  have hF : ∀ x, BFormula.eval (toBFormula t) x = NecHard.hardF x := by
    intro x; rw [eval_toBFormula, ht]
  exact le_trans (NecHard.hardF_rate_sq_opt m b hb hlo hhi (toBFormula t) hF)
    (litCount_toBFormula_le t)

/-- **The family form (proved, unconditional).**  For every `b ≥ 5` there is a block count `m` such that every boundary
transducer computing the `N = nn b m`-variable `hardF` has volume `≥ N²/(64·b) = Ω(N²/log N)`. -/
theorem volume_hardF_family (b : ℕ) (hb : 5 ≤ b) :
    ∃ m, ∀ t : Trans (NecHard.nn b m), eval t = NecHard.hardF →
      (NecHard.nn b m) ^ 2 / (64 * b) ≤ volume t := by
  obtain ⟨m, hlo, hhi⟩ := NecHard.exists_balanced_m b hb
  exact ⟨m, fun t ht => volume_hardF_lower hb hlo hhi t ht⟩

/-- **THE JOINT TEARING BOUND (proved, unconditional).**  For every dimension budget `w ≥ 3`, the joint thermodynamic
budget of `hardF` is `≥ N²/(64·b)`: a concrete target tears the energy budget of *every* admissible bounded-dimension
boundary embedding.  The boundary programme's first genuine unconditional separating instance. -/
theorem budgetAt_hardF_lower (b : ℕ) (hb : 5 ≤ b) :
    ∃ m, ∀ w, 3 ≤ w →
      (NecHard.nn b m) ^ 2 / (64 * b) ≤ budgetAt w (NecHard.hardF (b := b) (m := m)) := by
  obtain ⟨m, hm⟩ := volume_hardF_family b hb
  refine ⟨m, fun w hw => ?_⟩
  have hne' : {v | ∃ t : Trans (NecHard.nn b m),
      eval t = NecHard.hardF ∧ width t ≤ w ∧ volume t = v}.Nonempty := by
    obtain ⟨t0, he0, hw0⟩ := exists_width_le_three (NecHard.hardF (b := b) (m := m))
    exact ⟨volume t0, t0, he0, le_trans hw0 hw, rfl⟩
  unfold budgetAt
  obtain ⟨t, he, _, hv⟩ := Nat.sInf_mem hne'
  rw [← hv]
  exact hm t he

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budgetAt_anti
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.volume_hardF_family
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budgetAt_hardF_lower
