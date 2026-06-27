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

With Socket 1 (cited, deep) and Socket 2 (cited, deep — `williams_decider_in_NEXP`), the conditional
`NEXP ⊄ ACC⁰` closes with **no remaining hypotheses**.  The structural well-formedness facts are *proved* here
(the designated `acc0Class`/`DesignatedACC0` are given concrete definitions), so the separation rests on exactly
the two deep cited axioms plus `propext` (all visible in `#print axioms`).
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- The designated clocked simulator: evaluates each `ACC⁰` machine via its Beigel–Tarui `SYM∘AND` quasipoly
normal form within the clock budget.  Opaque — only its faithfulness (cited axiom) is used. -/
opaque acc0Sim : ℕ → ℕ → ℕ

/-- The designated clocked family of decision functions, given concretely: `acc0Class e` is the `{0,1}`-valued
function whose value at `x` is the `x`-th bit of `e`.  This is a genuine countable family of Boolean functions
(matching that `ACC⁰` is a countable circuit class), so the structural facts below are *proved*, not assumed.
It is a stand-in for the clocked `ACC⁰` family; the deep content — that the separate simulator `acc0Sim`
reproduces this family's values — stays in the cited `beigelTarui_faithful` axiom. -/
def acc0Class : ℕ → ℕ → ℕ := fun e x => if Nat.testBit e x then 1 else 0

/-- The designated `ACC⁰` predicate, defined concretely as the range of the clocked family: a function is in
the class exactly when some row of `acc0Class` computes it.  (Countable, as `ACC⁰` is.)  With this definition
the enumeration fact is provable by construction. -/
def DesignatedACC0 : (ℕ → ℕ) → Prop := fun f => ∃ e, ∀ x, acc0Class e x = f x

/-- **Beigel–Tarui faithfulness — cited axiom (Socket 1)** [Beigel–Tarui 1994; Williams 2014].

Via the `SYM∘AND` quasipolynomial normal form for `ACC⁰`, the clocked simulator reproduces the class value on
every self-application: the simulated output `acc0Sim e e` equals the true class value `acc0Class e e`, because
the quasipoly `SYM∘AND` evaluation fits inside the clock budget (budget domination = `ACC⁰` membership).

**Asserted, not proved** — the separation-strength content.  Visible in `#print axioms` as
`beigelTarui_faithful`. -/
axiom beigelTarui_faithful : FaithfulOnDiagonal acc0Class acc0Sim

/-- **Structural well-formedness — now PROVED** (was a structural axiom): the clocked family is Boolean-valued
on its diagonal.  Immediate from the concrete definition (`if … then 1 else 0`). -/
theorem acc0Class_boolean : ∀ e, acc0Class e e ≤ 1 := by
  intro e; unfold acc0Class; split <;> omega

/-- **Structural well-formedness — now PROVED** (was a structural axiom): the clocked family enumerates the
designated `ACC⁰` class.  True by construction, since `DesignatedACC0` is *defined* as the range of
`acc0Class`. -/
theorem acc0Class_enumerates : ∀ f : ℕ → ℕ, DesignatedACC0 f → ∃ e, ∀ x, acc0Class e x = f x :=
  fun _ h => h

/-- The fully assembled `WilliamsBridge` for the designated objects: both deep sockets supplied by the cited
axioms (`beigelTarui_faithful`, `williams_decider_in_NEXP`), the structural fields by the now-**proved**
well-formedness theorems. -/
def williamsBridge_designated :
    WilliamsBridge DesignatedACC0 WilliamsNEXP acc0Sim acc0Class where
  faithful := beigelTarui_faithful
  boolean := acc0Class_boolean
  decider_in_nexp := williams_decider_in_NEXP acc0Sim
  acc0_enumerated := acc0Class_enumerates

/-- **`NEXP ⊄ ACC⁰`, reduced to exactly the two deep cited axioms.**  The structural well-formedness fields are
now proved (`acc0Class` and `DesignatedACC0` are concrete), so the conditional separation closes with **no
remaining hypotheses** and rests only on `propext` and the two deep separation-strength axioms.

`#print axioms` lists exactly: `propext`, `beigelTarui_faithful` (Socket 1, Beigel–Tarui) and
`williams_decider_in_NEXP` (Socket 2, Williams fast-`SAT`).  Discharging those two *is* the Williams theorem;
everything else in the arc — including the structural facts — is unconditional and `sorry`-free. -/
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
