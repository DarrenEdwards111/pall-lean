import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeBoundaryGodmoveSymmetric
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModSymAndForm

/-!
# The SYM∘AND count layer: Beigel–Tarui's cheap top, bridged into the Williams fast-SAT route

The previous rung (`…CubeBoundaryGodmoveSymmetric`) compressed a full-support **symmetric** gate to `n + 1` count-cells
by counting *true input bits* (Hamming weight).  Beigel–Tarui's normal form generalises the count: an `ACC⁰` circuit
equals a **`SYM ∘ AND`** — a symmetric function of `m` `AND`-terms — and its value depends only on *how many of the `m`
terms fire*, giving `m + 1` count-cells regardless of `n`.  The repo already proves the cheap-top half of this
(`ACC0SymmetricObserver`: `gateCount`, `symEval`, `sym_count_card_le ≤ m+1`, `observed_sat_iff`).  What was missing —
and what this file supplies — is the **bridge from that count observer into the `FastSATModel` / Williams route** the
boundary-Godmove arc feeds.

  `symAndModel` — **the bridge (proved)**: any `SYM ∘ (m gates)` circuit `symEval g h`, with `(m+1)+1 ≤ 2^{n−budget}`,
        yields a `NFrameFastSAT.FastSATModel` whose count-cell table is the achievable-count image
        (`≤ m+1` cells, via the repo's `sym_count_card_le`), deciding SAT through the count boundary (via
        `observed_sat_iff`) rather than the `2^n` cube.
  `symAnd_gives_nframe_speedup` — the SYM∘AND circuit routes to the N-Frame fast-SAT speedup slot the Williams
        meta-theorem consumes.
  `modGate_eq_symAnd` — **the unification (proved, re-exported)**: `MOD_m` on all `n` bits *is* `SYM ∘ (singleton ANDs)`
        (`gateCount` of the singletons = Hamming weight).  So the previous symmetric-input rung is exactly the
        `m = n` singleton-`AND` special case of this one — junta → symmetric-inputs → SYM∘AND is one ladder.
  `symAndEx…` — a concrete **depth-2** `SYM∘AND` (threshold-2 of three 2-`AND`s over 6 bits, `≤ 4` cells, budget `3`):
        a genuine SYM∘AND that is neither a junta nor a single symmetric gate.

## Honest scope — the count engine, not the reduction

This bridges the **cheap SYM top** (the count boundary, `≤ m+1` cells) into the fast-SAT model.  It is the engine the
Beigel–Tarui/Williams `ACC⁰`-SAT algorithm runs on, and it consumes an *already-given* `SYM ∘ AND` form.  The **deep**
direction — that an arbitrary `ACC⁰` circuit actually *reduces* to a `SYM ∘ AND` with `m` quasipolynomial (Yao–Beigel–
Tarui, with the `AND`-fan-in/degree growing to `polylog` under depth composition) — is **not** proved here; it is the
repo's open structural socket (`MixedACCDepthReductionSocket` / the `beigelTarui_faithful` axiom).  This file provides
the SYM-layer count model that *consumes* that reduction's output; it does not perform the reduction.  Also, a small
cell count is a compression bound, not a uniform poly-time algorithm.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymAnd

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameFastSAT
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat (fastSatWork)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount symEval sym_count_card_le)
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver (observed_sat_iff)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0ModSymAndForm (modGateFn modGate_eq_symEval)

variable {n m : ℕ}

/-- **The bridge (proved): a `SYM ∘ (m gates)` circuit yields a `FastSATModel`.**  The count-cell table is the
achievable-count image `image (gateCount g)`, whose size is `≤ m + 1` (the repo's `sym_count_card_le` — the SYM top's
cheap count boundary), and SAT is decided by searching that image (`observed_sat_iff`).  Given the savings bound
`(m+1)+1 ≤ 2^{n−budget}`, this is an N-Frame fast-SAT model. -/
noncomputable def symAndModel (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool)
    (budget : ℕ) (hb : budget ≤ n) (hcard : (m + 1) + 1 ≤ 2 ^ (n - budget)) :
    FastSATModel n Unit (fun _ => decide (Satisfiable (symEval g h))) where
  encode := fun _ =>
    ⟨(Finset.univ.image (gateCount g)).card, decide (∃ c ∈ Finset.univ.image (gateCount g), h c = true)⟩
  correct := fun _ =>
    decide_eq_decide.mpr
      (observed_sat_iff (f := symEval g h) (stat := gateCount g) h (fun _ => rfl)).symm
  budget := budget
  budget_le := hb
  work_le := fun _ => by
    have hcell : (Finset.univ.image (gateCount g)).card + 1 ≤ (m + 1) + 1 :=
      Nat.add_le_add_right (sym_count_card_le g) 1
    simpa [fastSatWork] using le_trans hcell hcard

/-- The SYM∘AND circuit routes to the N-Frame fast-SAT speedup slot the Williams meta-theorem consumes. -/
theorem symAnd_gives_nframe_speedup (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool)
    (budget : ℕ) (hb : budget ≤ n) (hcard : (m + 1) + 1 ≤ 2 ^ (n - budget)) :
    NFrameFastSATSpeedup n Unit (fun _ => decide (Satisfiable (symEval g h))) :=
  ⟨symAndModel g h budget hb hcard⟩

/-! ### Unification: the symmetric-input rung is the singleton-`AND` special case -/

/-- **The unification (proved)**: `MOD_m` on all `n` bits *is* `SYM ∘ (singleton ANDs)` — the count of the `n` singleton
`AND`s is the Hamming weight.  So the previous symmetric-input rung is the `m = n` singleton case of `symAndModel`. -/
theorem modGate_eq_symAnd (mm : ℕ) :
    (modGateFn mm : (Fin n → Bool) → Bool)
      = symEval (fun (i : Fin n) y => monoAND {i} y) (fun c => decide (mm ∣ c)) :=
  modGate_eq_symEval mm

/-- `MOD_m` on all `n` bits as a SYM∘AND fast-SAT model (the `m = n` singleton-`AND` instance of `symAndModel`),
recovering the previous rung's `n + 1` count-cells through the general SYM∘AND bridge. -/
noncomputable def modGateSymAndModel (mm budget : ℕ) (hb : budget ≤ n) (hcard : (n + 1) + 1 ≤ 2 ^ (n - budget)) :
    FastSATModel n Unit
      (fun _ => decide (Satisfiable (symEval (fun (i : Fin n) y => monoAND {i} y)
        (fun c => decide (mm ∣ c))))) :=
  symAndModel (fun (i : Fin n) y => monoAND {i} y) (fun c => decide (mm ∣ c)) budget hb hcard

/-! ### A concrete depth-2 SYM∘AND: threshold-2 of three 2-`AND`s over 6 bits -/

/-- Three genuine `AND`-of-two-literals sub-gates over `6` bits (not singletons, not the whole weight). -/
def gEx : Fin 3 → (Fin 6 → Bool) → Bool :=
  fun j y => ![y 0 && y 1, y 2 && y 3, y 4 && y 5] j

/-- Outer symmetric top: at least `2` of the three `AND`-terms fire. -/
def hEx : ℕ → Bool := fun c => decide (2 ≤ c)

/-- A concrete depth-2 `SYM∘AND` (`threshold-2 ∘ three 2-ANDs`) over `6` bits as a fast-SAT model: `≤ 4` count-cells,
budget `3` (a real `2^3` speedup) — a SYM∘AND that is neither a junta nor a single symmetric gate. -/
noncomputable def symAndEx : FastSATModel 6 Unit (fun _ => decide (Satisfiable (symEval gEx hEx))) :=
  symAndModel gEx hEx 3 (by norm_num) (by norm_num)

/-- The depth-2 witness searches `≤ 4` count-cells (the `m+1 = 4` SYM-top boundary), delivering `2^budget · work ≤ 2^6`. -/
theorem symAndEx_savings :
    2 ^ symAndEx.budget * fastSatWork (symAndEx.encode ()).cells ≤ 2 ^ 6 :=
  fastSATModel_savings symAndEx ()

/-- The depth-2 SYM∘AND routes to the N-Frame fast-SAT speedup slot. -/
theorem symAndEx_speedup : NFrameFastSATSpeedup 6 Unit (fun _ => decide (Satisfiable (symEval gEx hEx))) :=
  ⟨symAndEx⟩

end PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymAnd.symAndModel
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymAnd.symAnd_gives_nframe_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymAnd.modGate_eq_symAnd
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymAnd.symAndEx_savings
