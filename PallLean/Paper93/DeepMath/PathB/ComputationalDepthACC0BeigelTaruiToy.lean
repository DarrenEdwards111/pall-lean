import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueObserver

/-!
# Toy Beigel–Tarui: a bounded-bottom depth-2 fragment is observer-searchable

Using the residue-observer algebra (`…ACC0ResidueObserver`), this file proves a genuine toy depth-reduction step:
the **bounded-bottom** depth-2 fragment — an *arbitrary* top gate over `m` bottom gates, each reading a support of
`≤ w` coordinates — is observer-searchable, with `≤ ∏_i 2^{|T_i|}` cells (`≤ 2^{w·m}` for fan-in `≤ w`).  This is
the searchable form the `SYM`-of-`AND_w` Beigel–Tarui normal form targets: each bounded-fan-in bottom gate is
observed by the **projection** to its support (`card 2^{|T_i|}`), and the observer composition law (`observed_top_pi`)
lifts an arbitrary top over them to the product projection.

So the depth-reduction socket, restricted to this fragment, is *discharged*: bounded-bottom depth-2 circuits are
residue/projection-searchable in `< 2^n` steps when `∏_i 2^{|T_i|} < 2^n` (i.e. total bottom fan-in `< n`).

## What is proved (clean axioms, no `sorry`)

* `boundedGate_observedBy` — a gate reading only support `T` is observed by the projection `x ↦ x|_T`.
* `proj_card` — the projection codomain `↥T → Bool` has `2^{|T|}` states.
* `toy_bottom_observable` — an arbitrary top over bounded-support gates is observed by the product projection.
* `toy_bottom_cellCount_le` — that observer has `≤ ∏_i 2^{|T_i|}` cells.
* `toy_bounded_bottom_searchable` — **the toy depth reduction**: `∏_i 2^{|T_i|} < 2^n` ⇒ SAT is decided by a
  `< 2^n`-cell observer search.

## Honest scope

A real toy: it discharges the depth-reduction socket *for the bounded-bottom fragment* (the `SYM`-of-`AND_w` form),
via the observer composition law.  It does **not** prove the full Yao–Beigel–Tarui theorem (that an *arbitrary*
`ACC⁰` circuit reduces to this fragment — the deep structural step, still open).  Still the cell-count model;
nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiToy

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver

variable {n m : ℕ}

/-- **A bounded-support gate is observed by the projection to its support (proved).**  A gate that depends only on
the coordinates in `T` factors through `x ↦ (x j)_{j∈T}`. -/
theorem boundedGate_observedBy (T : Finset (Fin n)) (gate : (Fin n → Bool) → Bool)
    (hdep : ∀ x y : Fin n → Bool, (∀ j ∈ T, x j = y j) → gate x = gate y) :
    ObservedBy gate (fun x => fun j : ↥T => x j.val) := by
  classical
  refine ⟨fun v => gate (fun i => if h : i ∈ T then v ⟨i, h⟩ else false), fun x => ?_⟩
  apply hdep
  intro j hj
  simp [hj]

/-- **The projection codomain has `2^{|T|}` states (proved).** -/
theorem proj_card (T : Finset (Fin n)) : Fintype.card (↥T → Bool) = 2 ^ T.card := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- **An arbitrary top over bounded-support gates is observed by the product projection (proved).** -/
theorem toy_bottom_observable (f : Fin m → (Fin n → Bool) → Bool) (T : Fin m → Finset (Fin n))
    (hdep : ∀ i, ∀ x y : Fin n → Bool, (∀ j ∈ T i, x j = y j) → f i x = f i y)
    (top : (Fin m → Bool) → Bool) :
    ObservedBy (fun x => top (fun i => f i x))
      (fun (x : Fin n → Bool) => fun i => fun j : ↥(T i) => x j.val) :=
  observed_top_pi (fun i => f i) (fun i x => fun j : ↥(T i) => x j.val)
    (fun i => boundedGate_observedBy (T i) (f i) (hdep i)) top

/-- **The bounded-bottom observer has `≤ ∏_i 2^{|T_i|}` cells (proved).** -/
theorem toy_bottom_cellCount_le (T : Fin m → Finset (Fin n)) :
    (Finset.univ.image (fun (x : Fin n → Bool) => fun i => fun j : ↥(T i) => x j.val)).card
      ≤ ∏ i, 2 ^ (T i).card := by
  refine le_trans (observed_cellCount_le _) (le_of_eq ?_)
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl (fun i _ => proj_card (T i))

/-- **The toy depth reduction (proved): a bounded-bottom depth-2 circuit is searchable in `< 2^n` steps.**  An
arbitrary top over `m` gates of fan-in `≤ w` (so `∏_i 2^{|T_i|} < 2^n`, e.g. total bottom fan-in `< n`) has its SAT
decided by an observer search over `< 2^n` cells — the `SYM`-of-`AND_w` Beigel–Tarui form, discharged via the
observer composition law. -/
theorem toy_bounded_bottom_searchable (f : Fin m → (Fin n → Bool) → Bool) (T : Fin m → Finset (Fin n))
    (hdep : ∀ i, ∀ x y : Fin n → Bool, (∀ j ∈ T i, x j = y j) → f i x = f i y)
    (top : (Fin m → Bool) → Bool) (hregime : (∏ i, 2 ^ (T i).card) < 2 ^ n) :
    ∃ (g : (∀ i, ↥(T i) → Bool) → Bool),
      (Satisfiable (fun x => top (fun i => f i x))
        ↔ ∃ s ∈ Finset.univ.image (fun (x : Fin n → Bool) => fun i => fun j : ↥(T i) => x j.val), g s = true)
      ∧ (Finset.univ.image (fun (x : Fin n → Bool) => fun i => fun j : ↥(T i) => x j.val)).card < 2 ^ n := by
  obtain ⟨g, hg⟩ := toy_bottom_observable f T hdep top
  exact ⟨g, observed_sat_iff g hg, lt_of_le_of_lt (toy_bottom_cellCount_le T) hregime⟩

end PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiToy

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiToy.boundedGate_observedBy
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiToy.toy_bottom_cellCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiToy.toy_bounded_bottom_searchable
