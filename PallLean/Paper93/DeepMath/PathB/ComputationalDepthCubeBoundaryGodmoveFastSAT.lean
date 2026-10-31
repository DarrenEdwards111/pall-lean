import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFastSAT
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeAdmissibleBoundary

/-!
# The Boundary-Godmove fast-SAT route: `CubeBoundaryGodmove → FastSATModel → Williams`

The polynomial-method / cube-rank arc terminated honestly at the composite `MOD_6` / `ACC⁰[6]` wall
(`…CubeACC6Barrier`): no *single field* makes every modulus of a multi-prime circuit high degree, and that
impossibility is now a theorem.  Williams' algorithmic route bypasses the degree wall — it needs a **nontrivial
`ACC⁰`-SAT algorithm**, not a hard field — and the repo already packages the algorithmic terminus as
`NFrameFastSAT.FastSATModel` feeding the Williams meta-theorem.

This file keeps the **cube/N-Frame boundary Godmove** as the central object and routes it *into* that algorithmic
terminus, rather than building generic SAT plumbing detached from the boundary framework.  The Godmove boundary is an
**observer** (`CubeBoundary` = a partial assignment / admissible cut, from `…CubeAdmissibleBoundary`) that compresses
the `2ⁿ` search into a count-cell table indexed by the *visible* coordinates; hiding coordinates is exactly where the
`2^{budget}` speedup comes from.

  `CubeBoundaryGodmove` — the interface: per circuit an observer cut `boundary`, a compressed count-cell table `cells`,
        a boundary cell-search verdict `decideSAT`, and the two load-bearing guarantees —
        *correctness* (`preserves_sat`: the boundary search decides SAT) and *savings*
        (`compress`: `cells ≤ 2^{#visible}` + `hides`: the observer hides enough coordinates that
        `#visible + 1 ≤ n − budget`).
  `cubeBoundaryGodmove_fastSATModel` — **the reduction (proved)**: a `CubeBoundaryGodmove` yields a
        `NFrameFastSAT.FastSATModel`, deriving the Williams work bound `fastSatWork cells ≤ 2^{n−budget}` from the
        boundary geometry (the observer's hidden coordinates *are* the budget).
  `cubeBoundaryGodmove_gives_separation` — **the route (proved glue)**: `CubeBoundaryGodmove` ⇒ the N-Frame fast-SAT
        speedup slot ⇒ (with the two named classical Williams sockets) `NEXP ⊄ ACC⁰`.
  `toyGodmove` / `toy_boundary_speedup` — non-vacuity: the boundary interface is inhabitable.

## Why this is the boundary route, and the honest scope

The savings here is *geometric*: it is produced by the observer `boundary` hiding coordinates (`hides`), with the cell
table sized by the surviving visible configurations (`compress`).  That is the "Cube Godmove" shape — a dual separator /
observer cut compressing the bulk — now wired to the algorithmic certificate that is not blocked by the `MOD_6`
two-fields/CRT obstruction.

Honest scope: this is the **interface + reduction + route glue**, not `NEXP ⊄ ACC⁰`.  The genuinely deep pieces are
unchanged and *not* proved here: (i) the classical Williams sockets `EasyWitnessCollapse` / `NondetTimeHierarchy`
(Williams 2011), and (ii) the open algorithmic target this interface is meant to be *instantiated* with — an actual
observer-boundary family for arbitrary `ACC⁰` (composite `MOD`, depth `> 1`) whose count-cell table is genuinely
subexponential while preserving SAT.  Constructing that family is the load-bearing move and is not fakeable.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveFastSAT

open PallLean.Paper93.DeepMath.PathB.NFrameFastSAT
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat (fastSatWork)
open PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP (CubeBoundary visible)

/-- **The boundary-Godmove fast-SAT interface.**  For a circuit family `Circuit` (true SAT predicate `satOf`) over `n`
bits, an observer boundary compresses each circuit's search into a count-cell table:

* `boundary C` — the observer cut (a partial assignment: `none` = visible, `some b` = hidden);
* `cells C` — the size of the compressed count-cell table searched through that boundary;
* `decideSAT C` — the boundary cell-search verdict;
* `preserves_sat` — **correctness**: the boundary search decides SAT (`decideSAT C = satOf C`);
* `compress` — the cell table is indexed by the *visible* configurations, so `cells C ≤ 2^{#visible}`;
* `hides` — the observer hides enough coordinates that `#visible + 1 ≤ n − budget` (the `budget` hidden coordinates are
  the source of the speedup). -/
structure CubeBoundaryGodmove (n : ℕ) (Circuit : Type) (satOf : Circuit → Bool) where
  /-- The observer cut assigned to each circuit: a partial assignment / admissible boundary. -/
  boundary : Circuit → CubeBoundary n
  /-- The size of the compressed count-cell table searched through the boundary. -/
  cells : Circuit → ℕ
  /-- The boundary cell-search verdict on SAT. -/
  decideSAT : Circuit → Bool
  /-- **Correctness**: the boundary states preserve SAT — the cell search decides it. -/
  preserves_sat : ∀ C, decideSAT C = satOf C
  /-- The `budget` of hidden coordinates (the speedup exponent). -/
  budget : ℕ
  /-- The budget cannot exceed the number of input bits. -/
  budget_le : budget ≤ n
  /-- **Compression**: the count-cell table is indexed by the visible-coordinate configurations. -/
  compress : ∀ C, cells C ≤ 2 ^ (visible (boundary C)).card
  /-- **Savings geometry**: the observer hides enough coordinates that the visible block fits under `n − budget`. -/
  hides : ∀ C, (visible (boundary C)).card + 1 ≤ n - budget

/-- Arithmetic core of the savings: a cell count bounded by `2^v` with `v + 1 ≤ k` gives
`cells + 1 ≤ 2^k` — i.e. `fastSatWork cells ≤ 2^k`.  This is where hiding one extra coordinate (`v + 1 ≤ k`) pays for
the `+1` in the count-cell work. -/
theorem cells_succ_le_pow {c v k : ℕ} (hc : c ≤ 2 ^ v) (hk : v + 1 ≤ k) : c + 1 ≤ 2 ^ k :=
  calc c + 1 ≤ 2 ^ v + 1 := Nat.add_le_add_right hc 1
    _ ≤ 2 ^ v + 2 ^ v := Nat.add_le_add_left (Nat.one_le_pow v 2 (by norm_num)) _
    _ = 2 ^ (v + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- **The reduction (proved): `CubeBoundaryGodmove ⇒ FastSATModel`.**  An observer-boundary Godmove is a genuine N-Frame
fast-SAT model: the compressed count-cell table is the `NFrameProgram`, correctness is inherited, and the Williams work
bound `fastSatWork cells ≤ 2^{n−budget}` is *derived from the boundary geometry* — the observer's hidden coordinates are
the budget (`compress` + `hides` via `cells_succ_le_pow`). -/
def cubeBoundaryGodmove_fastSATModel {n : ℕ} {Circuit : Type} {satOf : Circuit → Bool}
    (G : CubeBoundaryGodmove n Circuit satOf) : FastSATModel n Circuit satOf where
  encode := fun C => ⟨G.cells C, G.decideSAT C⟩
  correct := G.preserves_sat
  budget := G.budget
  budget_le := G.budget_le
  work_le := fun C => cells_succ_le_pow (G.compress C) (G.hides C)

/-- The boundary-Godmove speedup slot: the family admits an observer-boundary fast-SAT model.  Via
`cubeBoundaryGodmove_fastSATModel` this inhabits the N-Frame `NFrameFastSATSpeedup` slot. -/
def CubeBoundaryGodmoveSpeedup (n : ℕ) (Circuit : Type) (satOf : Circuit → Bool) : Prop :=
  Nonempty (CubeBoundaryGodmove n Circuit satOf)

/-- A boundary-Godmove speedup feeds the N-Frame fast-SAT speedup slot (the concrete Williams inhabitant). -/
theorem cubeBoundaryGodmove_speedup {n : ℕ} {Circuit : Type} {satOf : Circuit → Bool}
    (h : CubeBoundaryGodmoveSpeedup n Circuit satOf) : NFrameFastSATSpeedup n Circuit satOf :=
  h.elim (fun G => ⟨cubeBoundaryGodmove_fastSATModel G⟩)

/-- **The route (proved glue): boundary Godmove ⇒ `NEXP ⊄ ACC⁰`.**  A `CubeBoundaryGodmove` for `ACC⁰` compiles (via the
reduction) to the N-Frame fast-SAT speedup, which with the two named classical Williams sockets forces `NEXP ⊄ ACC⁰`.
The Godmove boundary inhabits the speedup slot; the deep sockets are the classical ingredients (not proved here). -/
theorem cubeBoundaryGodmove_gives_separation
    (NEXP ACC0 NTIME2n NTIME2nFast : CClass) {n : ℕ} {Circuit : Type} {satOf : Circuit → Bool}
    (collapse : EasyWitnessCollapse NEXP ACC0 NTIME2n NTIME2nFast (NFrameFastSATSpeedup n Circuit satOf))
    (hierarchy : NondetTimeHierarchy NTIME2n NTIME2nFast)
    (G : CubeBoundaryGodmove n Circuit satOf) :
    ¬ (NEXP ⊆ ACC0) :=
  nframe_fastSAT_gives_separation NEXP ACC0 NTIME2n NTIME2nFast collapse hierarchy
    ⟨cubeBoundaryGodmove_fastSATModel G⟩

/-- The all-hidden observer cut has no visible coordinates. -/
theorem visible_all_hidden {n : ℕ} (b : Bool) :
    visible (fun (_ : Fin n) => (some b : Option Bool)) = ∅ := by
  ext i
  simp [visible]

/-- Non-vacuity: an observer-boundary Godmove for the degenerate single-input family.  The observer hides *both*
coordinates (`boundary = all-hidden`), leaving a `0`-cell table (`cells = 0 ≤ 2^0`) with a real `2^1` speedup
(`#visible = 0`, so `0 + 1 ≤ 2 − 1`). -/
def toyGodmove : CubeBoundaryGodmove 2 Unit (fun _ => true) where
  boundary := fun _ => (fun _ => some false)
  cells := fun _ => 0
  decideSAT := fun _ => true
  preserves_sat := fun _ => rfl
  budget := 1
  budget_le := by norm_num
  compress := fun _ => by norm_num
  hides := fun _ => by rw [visible_all_hidden]; norm_num

/-- The toy family admits an observer-boundary fast-SAT speedup — the boundary interface is inhabitable. -/
theorem toy_boundary_speedup : CubeBoundaryGodmoveSpeedup 2 Unit (fun _ => true) := ⟨toyGodmove⟩

/-- Sanity: the boundary Godmove routes all the way to the N-Frame speedup slot the Williams meta-theorem consumes. -/
theorem toy_boundary_gives_nframe_speedup : NFrameFastSATSpeedup 2 Unit (fun _ => true) :=
  cubeBoundaryGodmove_speedup toy_boundary_speedup

end PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveFastSAT.cubeBoundaryGodmove_fastSATModel
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveFastSAT.cubeBoundaryGodmove_gives_separation
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveFastSAT.toy_boundary_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveFastSAT.toy_boundary_gives_nframe_speedup
