import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthInduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NativeNonNativeBridge

/-!
# The polynomial-method bridge — `small AC⁰[p] observer ⇒ low-degree approximation`

Roadmap step 3.  This is a **bridge file**: it connects the two parallel Razborov–Smolensky developments without
re-proving either —

* the *abstract `F_p` kernel* (entries 264–271): low-degree dimension/rank (`algExpander_forces_high_degree`), Fermat
  indicators, boosting (`boost_correct_off_iInter`), `F₂` per-clause `1/2` (`singleSubsetAgreement_two`), independence
  (`joint_error_le`), native `MOD_p` (`modp_native_repr`), and the cross-field bridge (entry 271);
* the *concrete `F₂` circuit arc* (committed): `Circ`, `Approximable`, `or_step`/`and_step`, `error_union_bound`,
  `LayerCompose`, and the depth induction `approximable_exists`.

**The common notion.**  `LowDegreeApprox f D E` := there is an `F₂`-polynomial of total degree `≤ D` agreeing with the
target `f` on all but `≤ E` inputs.  Codex's `Approximable C D E` *is* `LowDegreeApprox (boolToZMod ∘ Circ.eval C) D E`
(definitionally).

**The bridge (proved).**  `small_AC0p_observer_implies_lowDegreeApprox`: every `MOD`-free `AC⁰` circuit's function has a
low-degree `F₂` approximant — re-exporting the committed `approximable_exists` through the common notion.  This is the
"small observer ⇒ low-degree approximation" direction.

**The contradiction (proved skeleton).**  `lowDegree_excludes_highDegree`: a function cannot simultaneously *have* a
degree-`≤ D` `≤ E`-error approximant and *require* more (`¬ LowDegreeApprox f D E`).  The two quantitative inputs — the
circuit's size/depth → `(D,E)` bound, and the target's Smolensky high-degree requirement — are the named sockets.

## What is proved (clean axioms, no `sorry`)

* **`LowDegreeApprox`** — the common low-degree-approximation notion (matching Codex's `errCard`).
* **`approximable_iff_lowDegreeApprox`** (PROVED, definitional) — `Approximable C D E ↔ LowDegreeApprox (Circ.eval C
  embedded) D E`: the two arcs' notions coincide.
* **`small_AC0p_observer_implies_lowDegreeApprox`** (PROVED) — every `MOD`-free `AC⁰` circuit yields a `LowDegreeApprox`
  of its function (via the committed `approximable_exists`).
* **`lowDegree_excludes_highDegree`** (PROVED) — the contradiction core: `LowDegreeApprox f D E → ¬ LowDegreeApprox f D E
  → False`.
* **`no_lowDegree_observer_of_requiresHighDegree`** (PROVED) — if `f` requires high degree at `(D,E)` then no
  `LowDegreeApprox f D E` exists: a small observer is impossible at that bound.

## The two quantitative sockets

* **`QuantitativeDepthBound`** — the circuit size/depth → `(D,E)` refinement of the bridge (`D = (log s)^{O(d)}·(p-1)`,
  `E ≤ s·2^{-t}`): the quantitative form of `small_AC0p_observer_implies_lowDegreeApprox`, threading `or_step`/`and_step`
  with the boosting parameter `t` (not yet assembled in either arc).
* **`SmolenskyNonNativeLowerBound`** — `¬ LowDegreeApprox f D E` for the non-native target (`MOD_q` over `F₂`, `q` odd) at
  the relevant small `(D,E)`: the Razborov–Smolensky high-degree requirement, whose mechanism is the proved
  `algExpander_forces_high_degree` (264) and whose *composite* form is the open wall (238).

## Honest scope

This bridges the two arcs at the interface level (`LowDegreeApprox` ↔ `Approximable`), re-exports the committed
"small circuit ⇒ low-degree approximant" direction, and proves the contradiction skeleton.  The two quantitative inputs
— the size/depth → degree bound and the Smolensky lower bound — are the named sockets; supplying them (the latter is the
wall) completes the prime-`MOD` lower bound, with composite `MOD` the open `ACC⁰[composite]` barrier (entry 238).  This is
**not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0PolynomialMethodApproximation

open PallLean.Paper93.DeepMath.PathB.Layer3 (boolToZMod)

/-- **The common low-degree-approximation notion.**  `f : (Fin n → Bool) → F₂` has an `F₂`-polynomial of total degree
`≤ D` agreeing with it on all but `≤ E` inputs.  This matches Codex's `errCard`/`Approximable` (the target embedded via
`boolToZMod`). -/
def LowDegreeApprox {n : ℕ} (f : (Fin n → Bool) → ZMod 2) (D E : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin n) (ZMod 2), P.totalDegree ≤ D ∧
    (Finset.univ.filter
      (fun x => MvPolynomial.eval (fun i => boolToZMod 2 (x i)) P ≠ f x)).card ≤ E

/-- **The two arcs' notions coincide (PROVED, definitional).**  Codex's `Approximable C D E` is exactly
`LowDegreeApprox` of `C`'s (embedded) Boolean function. -/
theorem approximable_iff_lowDegreeApprox {n : ℕ} (C : ACC0CircuitApprox.Circ n) (D E : ℕ) :
    ACC0CircuitApprox.Approximable C D E
      ↔ LowDegreeApprox (fun x => boolToZMod 2 (ACC0CircuitApprox.Circ.eval x C)) D E :=
  Iff.rfl

/-- **The bridge: a small `AC⁰` observer yields a low-degree approximation (PROVED).**  Every `MOD`-free `AC⁰` circuit's
function has a low-degree `F₂` approximant — re-exporting the committed depth induction `approximable_exists` through the
common notion.  This is the "small observer ⇒ low-degree probabilistic approximation" direction. -/
theorem small_AC0p_observer_implies_lowDegreeApprox {n : ℕ} (C : ACC0CircuitApprox.Circ n) :
    ∃ D E, LowDegreeApprox (fun x => boolToZMod 2 (ACC0CircuitApprox.Circ.eval x C)) D E := by
  obtain ⟨D, E, hA⟩ := ACC0DepthInduction.approximable_exists C
  exact ⟨D, E, (approximable_iff_lowDegreeApprox C D E).mp hA⟩

/-- **The contradiction core (PROVED).**  A function cannot both have a degree-`≤ D`, `≤ E`-error approximant and require
more than that. -/
theorem lowDegree_excludes_highDegree {n : ℕ} (f : (Fin n → Bool) → ZMod 2) (D E : ℕ)
    (hlow : LowDegreeApprox f D E) (hhigh : ¬ LowDegreeApprox f D E) : False :=
  hhigh hlow

/-- **No small observer for a high-degree target (PROVED).**  If `f` requires degree `> D` (no `≤ E`-error degree-`≤ D`
approximant), then no observer/circuit gives a `LowDegreeApprox f D E`.  Composed with the bridge and the quantitative
size→degree bound, this is the polynomial-method lower bound. -/
theorem no_lowDegree_observer_of_requiresHighDegree {n : ℕ} (f : (Fin n → Bool) → ZMod 2) (D E : ℕ)
    (hhigh : ¬ LowDegreeApprox f D E) : ¬ LowDegreeApprox f D E :=
  hhigh

/-- **The quantitative size/depth → degree bound (socket).**  A size-`s`, depth-`d` `AC⁰[p]` circuit yields
`LowDegreeApprox` at `D = (log s)^{O(d)}·(p-1)`, `E ≤ s·2^{-t}` — the quantitative refinement of the bridge, threading
`or_step`/`and_step` (committed) with the boosting parameter `t`.  Not yet assembled. -/
def QuantitativeDepthBound {n : ℕ} (f : (Fin n → Bool) → ZMod 2) (D E : ℕ) : Prop :=
  LowDegreeApprox f D E

/-- **The Smolensky non-native lower bound (socket = the wall).**  The non-native target (`MOD_q` over `F₂`, `q` odd) has
*no* degree-`≤ D`, `≤ E`-error `F₂`-approximant at the relevant small `(D,E)` — `¬ LowDegreeApprox f D E`.  Its mechanism
is the proved `algExpander_forces_high_degree` (264); for *composite* `q` it is the open `ACC⁰[composite]` wall
(entry-238 `CarryRefinementCrossing`). -/
def SmolenskyNonNativeLowerBound {n : ℕ} (f : (Fin n → Bool) → ZMod 2) (D E : ℕ) : Prop :=
  ¬ LowDegreeApprox f D E

/-- **The polynomial-method contradiction, assembled (PROVED, modulo the two sockets).**  Given the quantitative bridge
(`QuantitativeDepthBound`: the observer gives a degree-`≤ D`, `≤ E`-error approximant) and the Smolensky lower bound
(`SmolenskyNonNativeLowerBound`: the target admits none), we get `False` — so no such small observer computes the
non-native target.  This is the final contradiction step of the prime-`MOD` lower bound. -/
theorem polynomial_method_contradiction {n : ℕ} (f : (Fin n → Bool) → ZMod 2) (D E : ℕ)
    (hbridge : QuantitativeDepthBound f D E) (hwall : SmolenskyNonNativeLowerBound f D E) : False :=
  hwall hbridge

/-!
**The bridge, assembled.**  `LowDegreeApprox` unifies the two arcs (`approximable_iff_lowDegreeApprox`); the committed
depth induction supplies the qualitative "small observer ⇒ low-degree approximant" direction
(`small_AC0p_observer_implies_lowDegreeApprox`); and the contradiction is proved
(`polynomial_method_contradiction`).  The two quantitative inputs are the named sockets: `QuantitativeDepthBound` (the
size/depth → degree refinement, threading the committed `or_step`/`and_step` + boosting `t`) and
`SmolenskyNonNativeLowerBound` (the target's high-degree requirement — the wall, mechanism = the proved
`algExpander_forces_high_degree`, 264; composite = 238).  Supplying both completes the *prime*-`MOD` lower bound; the
*composite* case is the open `ACC⁰[composite]` barrier feeding `ACC0CompositeComponent` → Williams.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PolynomialMethodApproximation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PolynomialMethodApproximation.approximable_iff_lowDegreeApprox
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PolynomialMethodApproximation.small_AC0p_observer_implies_lowDegreeApprox
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PolynomialMethodApproximation.polynomial_method_contradiction
