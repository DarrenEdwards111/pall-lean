import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeBoundaryGodmoveGate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModSymAndForm

/-!
# Full-support count compression: the symmetric observer past the junta wall

`…CubeBoundaryGodmoveGate` instantiated the observer boundary on **juntas** and proved the wall
(`fullVisible_no_boundary`): a coordinate-hiding cut compresses a gate only by *ignoring* coordinates, so a gate
depending on **all** `n` inputs (a full-support function) admits no `CubeBoundaryGodmove`.  This file crosses that wall
for the class where honest compression genuinely exists — **symmetric** gates — by *generalising the observer* from a
coordinate cut to an arbitrary finite **count-cell** partition.

A symmetric gate (e.g. `MOD_m` on *all* `n` bits — the very gate the degree method hit the `MOD_6`/`ACC⁰[6]` wall on)
depends on every coordinate, yet its value depends only on the **Hamming weight**: there are only `n + 1` distinct
"cells" (weight classes), not `2^n`.  This is the count compression the Razborov–Smolensky *degree* method could not
see, and it is exactly the `SYM`-layer engine of the Beigel–Tarui / Williams `ACC⁰`-SAT algorithm.

  `CountObserver n f` — the generalised observer: a finite `Cell` type, an `obs : assignment → Cell`, a per-cell value
        `cellVal`, with `factors` (the gate factors through the observer) and `surj` (every cell is reachable).  The
        cut-based `CubeBoundary` is the special case `Cell = 2^{visible}`; here `Cell` is arbitrary.
  `countObserver_sat_iff` — **the compression (proved)**: SAT of the gate equals `∃` a cell with value `true` — a
        search over `|Cell|` cells, not `2^n` assignments.
  `countObserverModel` — **the reduction (proved)**: a count observer with `|Cell| + 1 ≤ 2^{n − budget}` yields a
        `NFrameFastSAT.FastSATModel` (hence the Williams route), with cell count `|Cell|`.
  `symObserver` — **the full-support instance (proved)**: any symmetric `f` gets a `CountObserver` with
        `Cell = Fin (n+1)` (the weight classes), so `|Cell| = n + 1` — **polynomial** count-cells for a gate depending
        on all `n` coordinates.  `canonAssign` / `weight_canonAssign` supply the reachability of every weight.
  `modGateFn_symmetric` + `mod3all8` — the concrete `ACC⁰[m]` gate `MOD_m` on all `n` bits carried through: a numeric
        witness `MOD_3` on all `8` bits with `9` count-cells and budget `4` (a real `2^4` speedup on a **full-support**
        gate — where the junta observer gets nothing, `fullVisible_no_boundary`).

## Honest scope — what this is and is not

This is genuine full-support count compression: the mechanism the junta wall forbids, now realised for symmetric gates,
reusing the repo's own `hammingWeight` and `modGateFn` (the composite-MOD-arc gate).  Two honest caveats:

1. A *single* symmetric gate has **trivial SAT** (weight `0` always satisfies `MOD_m`).  The content is not the SAT
   answer but the *representation*: a full-support function decided through `n + 1` count-cells rather than `2^n`
   assignments — the generalisation past the junta wall, and the engine the real algorithm runs on.

2. The full `ACC⁰`-SAT algorithm applies this `SYM` engine **after** the Beigel–Tarui reduction of `ACC⁰` to
   `SYM ∘ AND` (the repo's named socket `beigelTarui_faithful` / `IsSymAnd`), where the count is over up to
   `n^{polylog}` `AND`-terms, not the `n` raw coordinates.  That reduction is **not** performed here.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This supplies the honest `SYM`-layer count compression that the boundary
route needs, for full-support symmetric gates.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymmetric

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameFastSAT
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat (fastSatWork)
open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT (hammingWeight)
open PallLean.Paper93.DeepMath.PathB.ACC0ModSymAndForm (modGateFn)

variable {n : ℕ}

/-! ### The generalised count observer -/

/-- A **count observer** for a Boolean gate `f`: a finite set of `Cell`s, a map `obs` sending each assignment to its
cell, a per-cell value `cellVal`, such that the gate *factors* through the observer (`factors`) and every cell is
*reachable* (`surj`).  SAT is then a search over `|Cell|` cells.  The coordinate-cut `CubeBoundary` is the special case
`Cell = 2^{visible}`; here `Cell` is an arbitrary finite quotient of the cube (e.g. weight classes). -/
structure CountObserver (n : ℕ) (f : (Fin n → Bool) → Bool) where
  /-- The count-cell index type. -/
  Cell : Type
  /-- `Cell` is finite (there are boundedly many count-cells). -/
  fin : Fintype Cell
  /-- The observer: each assignment lands in a cell. -/
  obs : (Fin n → Bool) → Cell
  /-- The value the gate takes on a cell. -/
  cellVal : Cell → Bool
  /-- **Factorisation**: the observer sees enough — the gate is constant on each cell. -/
  factors : ∀ x, f x = cellVal (obs x)
  /-- **Reachability**: every cell is hit by some assignment. -/
  surj : Function.Surjective obs

attribute [instance] CountObserver.fin

/-- **The compression (proved)**: SAT of the gate equals the existence of a cell with value `true` — a search over the
`|Cell|` count-cells, not the `2^n` assignments. -/
theorem countObserver_sat_iff {f : (Fin n → Bool) → Bool} (O : CountObserver n f) :
    (∃ x, f x = true) ↔ (∃ c : O.Cell, O.cellVal c = true) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨O.obs x, by rw [← O.factors x]; exact hx⟩
  · rintro ⟨c, hc⟩
    obtain ⟨x, rfl⟩ := O.surj c
    exact ⟨x, by rw [O.factors x]; exact hc⟩

/-- **The reduction (proved)**: a count observer with `|Cell| + 1 ≤ 2^{n − budget}` yields an N-Frame fast-SAT model —
the `|Cell|` count-cells are the `NFrameProgram`, and the savings is the small cell count. -/
def countObserverModel {f : (Fin n → Bool) → Bool} (O : CountObserver n f)
    (budget : ℕ) (hb : budget ≤ n) (hcard : Fintype.card O.Cell + 1 ≤ 2 ^ (n - budget)) :
    FastSATModel n Unit (fun _ => decide (∃ x, f x = true)) where
  encode := fun _ => ⟨Fintype.card O.Cell, decide (∃ c : O.Cell, O.cellVal c = true)⟩
  correct := fun _ => decide_eq_decide.mpr (countObserver_sat_iff O).symm
  budget := budget
  budget_le := hb
  work_le := fun _ => hcard

/-! ### The canonical assignment of each Hamming weight -/

/-- The canonical assignment of weight `w`: set exactly the first `w` coordinates. -/
def canonAssign (w : Fin (n + 1)) : Fin n → Bool := fun i => decide ((i : ℕ) < w.val)

/-- Counting indices below a threshold (`k` of them, capped at `n`). -/
theorem card_filter_lt (k : ℕ) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)).card = min n k := by
  have hinj : Function.Injective (Fin.val : Fin n → ℕ) := Fin.val_injective
  have himg : Finset.image Fin.val (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k))
      = Finset.range (min n k) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range,
      Nat.lt_min]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i.isLt, hi⟩
    · rintro ⟨hmn, hmk⟩; exact ⟨⟨m, hmn⟩, hmk, rfl⟩
  rw [← Finset.card_image_of_injective _ hinj, himg, Finset.card_range]

/-- **The canonical assignment has the intended weight (proved)**: `hammingWeight (canonAssign w) = w`. -/
theorem weight_canonAssign (w : Fin (n + 1)) : hammingWeight (canonAssign w) = w.val := by
  unfold hammingWeight canonAssign
  simp only [decide_eq_true_eq]
  rw [card_filter_lt]
  omega

/-- The Hamming weight never exceeds `n`. -/
theorem hammingWeight_le (x : Fin n → Bool) : hammingWeight x ≤ n := by
  unfold hammingWeight
  calc (Finset.univ.filter (fun i => x i = true)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- The Hamming weight packaged as an element of `Fin (n + 1)` (the weight-class index). -/
def weightFin (x : Fin n → Bool) : Fin (n + 1) := ⟨hammingWeight x, Nat.lt_succ_of_le (hammingWeight_le x)⟩

/-! ### The symmetric observer: full-support count compression -/

/-- A gate is **symmetric** if its value depends only on the Hamming weight of the input. -/
def Symmetric (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, hammingWeight x = hammingWeight y → f x = f y

/-- **The full-support instance (proved)**: any symmetric gate has a count observer whose cells are the `n + 1` weight
classes — polynomial count-cells for a gate that depends on all `n` coordinates. -/
def symObserver {f : (Fin n → Bool) → Bool} (hf : Symmetric f) : CountObserver n f where
  Cell := Fin (n + 1)
  fin := inferInstance
  obs := weightFin
  cellVal := fun w => f (canonAssign w)
  factors := fun x => hf x (canonAssign (weightFin x)) (weight_canonAssign (weightFin x)).symm
  surj := fun c => ⟨canonAssign c, Fin.ext (weight_canonAssign c)⟩

/-- The symmetric observer has exactly `n + 1` count-cells (one per weight class). -/
theorem symObserver_card {f : (Fin n → Bool) → Bool} (hf : Symmetric f) :
    Fintype.card (symObserver hf).Cell = n + 1 := by
  simp only [symObserver, Fintype.card_fin]

/-! ### Concrete full-support `ACC⁰[m]` gate: `MOD_m` on all `n` bits (the composite-MOD-arc gate) -/

/-- The repo's `MOD_m`-on-all-coordinates gate is symmetric (it reads only the Hamming weight). -/
theorem modGateFn_symmetric (m : ℕ) : Symmetric (modGateFn (n := n) m) := by
  intro x y h
  simp only [modGateFn, h]

/-- `MOD_m` on all `n` bits carried through the count observer: `n + 1` weight-cells. -/
def modGateObserver (m : ℕ) : CountObserver n (modGateFn m) := symObserver (modGateFn_symmetric m)

theorem modGateObserver_card (m : ℕ) : Fintype.card (modGateObserver (n := n) m).Cell = n + 1 :=
  symObserver_card _

/-- **The full-support fast-SAT model (proved)**: given the (numeric) savings bound, `MOD_m` on all `n` bits yields a
`FastSATModel` through its `n + 1` weight-cells — full-support count compression the junta observer cannot provide. -/
def modGateModel (m budget : ℕ) (hb : budget ≤ n) (hcard : (n + 1) + 1 ≤ 2 ^ (n - budget)) :
    FastSATModel n Unit (fun _ => decide (∃ x, modGateFn (n := n) m x = true)) :=
  countObserverModel (modGateObserver m) budget hb (by rw [modGateObserver_card]; exact hcard)

/-- `MOD_m` on all `n` bits routes to the N-Frame fast-SAT speedup slot the Williams meta-theorem consumes. -/
theorem modGate_gives_nframe_speedup (m budget : ℕ) (hb : budget ≤ n)
    (hcard : (n + 1) + 1 ≤ 2 ^ (n - budget)) :
    NFrameFastSATSpeedup n Unit (fun _ => decide (∃ x, modGateFn (n := n) m x = true)) :=
  ⟨modGateModel m budget hb hcard⟩

/-! ### A concrete numeric witness: `MOD_3` on all `8` bits, `9` cells, budget `4` -/

/-- `MOD_3` on all `8` bits: a full-support symmetric gate compressed to `9` weight-cells, budget `4` — a real `2^4`
speedup over brute force `2^8`, on a gate where a coordinate-hiding boundary gets **nothing**
(`CubeBoundaryGodmoveGate.fullVisible_no_boundary`). -/
def mod3all8 : FastSATModel 8 Unit (fun _ => decide (∃ x, modGateFn (n := 8) 3 x = true)) :=
  modGateModel (n := 8) 3 4 (by norm_num) (by norm_num)

/-- The witness searches only `9` count-cells for `8` full-support inputs (polynomial, not `2^8`). -/
theorem mod3all8_cells : (mod3all8.encode ()).cells = 9 := by
  simp [mod3all8, modGateModel, countObserverModel, modGateObserver_card]

/-- The witness delivers Williams savings: `2^budget · work ≤ 2^8`. -/
theorem mod3all8_savings : 2 ^ mod3all8.budget * fastSatWork (mod3all8.encode ()).cells ≤ 2 ^ 8 :=
  fastSATModel_savings mod3all8 ()

end PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymmetric

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymmetric.countObserver_sat_iff
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymmetric.symObserver
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymmetric.modGate_gives_nframe_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymmetric.mod3all8_cells
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveSymmetric.mod3all8_savings
