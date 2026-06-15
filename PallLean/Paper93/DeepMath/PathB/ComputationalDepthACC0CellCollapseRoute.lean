import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCSwitchingPipeline
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRestrictionTree

/-!
# The N-Frame route: cell collapse ⇒ low holonomy correlation (bridge proved, restriction lemma socketed)

This file states the N-Frame route to a full-`ACC⁰` correlation bound in the explicit *cell-collapse* vocabulary,
isolating the single hard missing statement.  The route is:

```
full ACC⁰ predictor  ──[FullACC0ForcesCellCollapse : restriction lemma, the HARD open socket]──►
   ∃ live set L : CellCollapse supports L   (few gate-supports survive on L)
                                  │  cell_collapse_implies_low_holonomy_correlation  (PROVED)
                                  ▼
   LowHolonomyCorrelation supports g   (the predictor cannot correlate with some holonomy parity)
```

The **bridge** (collapse ⇒ low correlation) is already a *proved* theorem of the corpus
(`ACCSwitchingPipeline.predictor_fails_of_survivors`: `2^{#survivors} < |L|` ⇒ a holonomy support `D` and an
off-diagonal axis `(v,w)` on which the predictor agrees with `fParity D` at most half the time).  The **hard** piece
is `FullACC0ForcesCellCollapse` — that a full-`ACC⁰` predictor, under some restriction, *achieves* the collapse.  This
is the N-Frame analogue of a switching / restriction lemma for full `ACC⁰` (cf. `ACCRestrictionTree.Restriction
TreeSwitch`, the same `NP ⊄ ACC⁰`-strength content).

## What is proved (clean axioms, no `sorry`)

* `CellCollapse` / `LowHolonomyCorrelation` — the route's two predicates, in the corpus's `survivingCount` /
  `weightVec` / `fParity` vocabulary.
* **`cell_collapse_implies_low_holonomy_correlation`** — the bridge, *proved* (re-export of
  `predictor_fails_of_survivors`).
* **`cell_collapse_of_survival`** — the socket *reduced to a concrete condition*: a live set with `< m` survivors and
  size `≥ 2^m` gives the collapse.  So the open content is exactly "a restriction leaving fewer than `log₂|L|`
  surviving supports on a live set `L`".
* **`nframe_route`** — the composition: `FullACC0ForcesCellCollapse ⇒ LowHolonomyCorrelation` (socket ▸ proved bridge).

## Honest scope — what is open and why

`FullACC0ForcesCellCollapse` is the **open** statement, and it is `NP ⊄ ACC⁰`-strength.  Its probabilistic half is
proved (`ACCSwitchingPipeline.exists_low_survival`: a low-*expected*-survivor restriction exists), but the
quantitative bound it needs — *fewer than `log₂|L|` survivors* on a large live set, for a *full* `ACC⁰` predictor — is
the genuine switching/restriction lemma.  For *full* `ACC⁰` this is not deliverable by naive leaf-switching: the
proved `MOD` no-go (`ACCSwitchingModBridge.mod_gate_parity_nonconstant` — a `MOD`/parity gate is non-constant on any
cube leaving a support coordinate free) shows leaf-only restrictions cannot drive the collapse through a `MOD` layer.
So this file pins the open target precisely; it does **not** prove it.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline

variable {n k : ℕ}

/-- **Cell collapse on a live set `L`**: fewer than `log₂|L|` gate-supports survive the restriction to `L`
(`2^{#survivors} < |L|`), so the predictor's behaviour on `L` collapses to fewer cells than there are off-diagonal
axes — the pigeonhole input to the correlation bound. -/
def CellCollapse (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : Prop :=
  2 ^ survivingCount supports L < L.card

/-- **Low holonomy correlation**: there is a holonomy support `D` and an off-diagonal axis `(v,w)` on which the
predictor `g ∘ weightVec` agrees with `fParity D` at most half the time — i.e. no correlation. -/
def LowHolonomyCorrelation (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) : Prop :=
  ∃ (D : Finset (Fin n)) (v w : Fin n), v ≠ w ∧
    2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => g (weightVec supports x) = fParity D x)).card
      ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card

/-- **The bridge (proved): cell collapse ⇒ low holonomy correlation.**  Re-export of
`predictor_fails_of_survivors` — once few supports survive on a live set, the predictor cannot correlate with the
holonomy parity. -/
theorem cell_collapse_implies_low_holonomy_correlation
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (L : Finset (Fin n))
    (h : CellCollapse supports L) : LowHolonomyCorrelation supports g :=
  predictor_fails_of_survivors supports L g h

/-- **The hard socket: a full-`ACC⁰` predictor's supports force cell collapse on some live set.**  The N-Frame
switching / restriction lemma — the single open, `NP ⊄ ACC⁰`-strength statement. -/
def FullACC0ForcesCellCollapse (supports : Fin k → Finset (Fin n)) : Prop :=
  ∃ L : Finset (Fin n), CellCollapse supports L

/-- **The socket reduced to a concrete condition (proved): few survivors on a large live set ⇒ cell collapse.**  If
some live set `L` has `< m` surviving supports and `|L| ≥ 2^m`, the collapse holds.  So the open content is exactly
"a restriction leaving `< log₂|L|` survivors on a live set `L`". -/
theorem cell_collapse_of_survival (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) (m : ℕ)
    (hsurv : survivingCount supports L < m) (hsize : 2 ^ m ≤ L.card) :
    FullACC0ForcesCellCollapse supports :=
  ⟨L, lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hsurv) hsize⟩

/-- **The N-Frame route (proved composition): the cell-collapse socket cashes out to low correlation.**  Given the
restriction lemma `FullACC0ForcesCellCollapse`, the predictor fails to correlate with the holonomy parity — by the
proved bridge. -/
theorem nframe_route (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (hcollapse : FullACC0ForcesCellCollapse supports) : LowHolonomyCorrelation supports g := by
  obtain ⟨L, hL⟩ := hcollapse
  exact cell_collapse_implies_low_holonomy_correlation supports g L hL

end PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute.cell_collapse_implies_low_holonomy_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute.cell_collapse_of_survival
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute.nframe_route
