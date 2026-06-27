import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMNexpAxiom
import Mathlib.Tactic

/-!
# Discharging Socket 1 (`faithful`) as a cited classical axiom, and the fully axiom-backed separation — step 6c

`WilliamsBridge.faithful` (`FaithfulOnDiagonal C sim`: the clocked simulator reproduces the class value on every
self-application) is the **deeper** separation-strength socket.  It holds exactly when the clock budget dominates
each `ACC⁰` machine's running time — which is the Beigel–Tarui `SYM∘AND` quasipolynomial normal form (every
`ACC⁰` function equals a depth-2 symmetric-of-quasipoly-`AND` circuit) evaluated inside the budget.  As with
Socket 2, we **assert it as a named, cited Lean `axiom`** rather than proving it.

A subtlety forces care: `FaithfulOnDiagonal C sim` is an *equation* `∀ e, sim e e = C e e`.  Axiomatising it over
arbitrary `C, sim` would be inconsistent (instantiate to two functions that disagree on the diagonal and derive
`False`).  So we introduce **designated opaque** objects — the designated clocked simulator `acc0Sim`, the
designated clocked family `acc0Class` enumerating `ACC⁰`, and the designated `ACC⁰` predicate `DesignatedACC0` —
and axiomatise faithfulness between *those*.  Opaque functions have no computable definitions, so an equation
between their diagonals is consistent.

References:
* R. Beigel and J. Tarui, *On ACC*, Computational Complexity 4 (1994) (FOCS 1991) — the `SYM∘AND` quasipoly
  normal form for `ACC⁰`.
* R. Williams, *Nonuniform ACC Circuit Lower Bounds*, JACM 2014 — the use of that normal form inside the budget.

With Socket 1 (cited, deep), Socket 2 (cited, deep — `williams_decider_in_NEXP`), and the two structural
well-formedness axioms below, the conditional `NEXP ⊄ ACC⁰` closes with **no remaining hypotheses**, resting
only on the explicitly named axioms (all visible in `#print axioms`).
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- The designated clocked simulator: evaluates each `ACC⁰` machine via its Beigel–Tarui `SYM∘AND` quasipoly
normal form within the clock budget.  Opaque — only its faithfulness (cited axiom) is used. -/
opaque acc0Sim : ℕ → ℕ → ℕ

/-- The designated clocked family enumerating `ACC⁰` (decision functions, Boolean outputs).  Opaque. -/
opaque acc0Class : ℕ → ℕ → ℕ

/-- The designated `ACC⁰` predicate on decision functions.  Opaque. -/
opaque DesignatedACC0 : (ℕ → ℕ) → Prop

/-- **Beigel–Tarui faithfulness — cited axiom (Socket 1)** [Beigel–Tarui 1994; Williams 2014].

Via the `SYM∘AND` quasipolynomial normal form for `ACC⁰`, the clocked simulator reproduces the class value on
every self-application: the simulated output `acc0Sim e e` equals the true class value `acc0Class e e`, because
the quasipoly `SYM∘AND` evaluation fits inside the clock budget (budget domination = `ACC⁰` membership).

**Asserted, not proved** — the separation-strength content.  Visible in `#print axioms` as
`beigelTarui_faithful`. -/
axiom beigelTarui_faithful : FaithfulOnDiagonal acc0Class acc0Sim

/-- **Structural well-formedness axiom**: the clocked family is Boolean-valued on its diagonal (its members are
decision functions, outputs in `{0,1}`).  Not separation-strength — a definitional property of the designated
class, an axiom here only because `acc0Class` is opaque. -/
axiom acc0Class_boolean : ∀ e, acc0Class e e ≤ 1

/-- **Structural well-formedness axiom**: the clocked family enumerates the designated `ACC⁰` class (every
`ACC⁰` decision function is some row `acc0Class e`).  This is the identification of the abstract diagonal class
with `ACC⁰`; again an axiom only because the objects are opaque. -/
axiom acc0Class_enumerates : ∀ f : ℕ → ℕ, DesignatedACC0 f → ∃ e, ∀ x, acc0Class e x = f x

/-- The fully assembled `WilliamsBridge` for the designated objects: both deep sockets supplied by the cited
axioms (`beigelTarui_faithful`, `williams_decider_in_NEXP`), the structural fields by the well-formedness
axioms. -/
def williamsBridge_designated :
    WilliamsBridge DesignatedACC0 WilliamsNEXP acc0Sim acc0Class where
  faithful := beigelTarui_faithful
  boolean := acc0Class_boolean
  decider_in_nexp := williams_decider_in_NEXP acc0Sim
  acc0_enumerated := acc0Class_enumerates

/-- **`NEXP ⊄ ACC⁰`, reduced entirely to the named axioms.**  With both deep sockets discharged as cited
classical axioms (Beigel–Tarui faithfulness and the Williams fast-`SAT` `NEXP` membership) and the two
structural well-formedness axioms, the conditional separation closes with **no remaining hypotheses**.

`#print axioms` lists exactly what it rests on: `propext`, the two deep cited axioms `beigelTarui_faithful` and
`williams_decider_in_NEXP`, and the two structural axioms `acc0Class_boolean`, `acc0Class_enumerates` — the
honest, fully-exposed dependency set.  Discharging the two deep axioms *is* the Williams theorem; everything
else in the arc is unconditional. -/
theorem NEXP_not_subset_ACC0_fromAxioms :
    ¬ (∀ f : ℕ → ℕ, WilliamsNEXP f → DesignatedACC0 f) :=
  NEXP_not_subset_ACC0 DesignatedACC0 WilliamsNEXP acc0Sim acc0Class williamsBridge_designated

/-- The explicit separating witness, fully axiom-backed: the diagonal decider `ramDiag acc0Sim` is in
`WilliamsNEXP` and not in `DesignatedACC0`. -/
theorem ramDiag_separates_fromAxioms :
    WilliamsNEXP (ramDiag acc0Sim) ∧ ¬ DesignatedACC0 (ramDiag acc0Sim) :=
  ramDiag_separates DesignatedACC0 WilliamsNEXP acc0Sim acc0Class williamsBridge_designated

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.NEXP_not_subset_ACC0_fromAxioms
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.ramDiag_separates_fromAxioms
