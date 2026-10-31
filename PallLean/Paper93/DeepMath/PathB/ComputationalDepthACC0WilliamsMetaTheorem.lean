import Mathlib

/-!
# Williams' meta-theorem — the proof *architecture* (glue proved, deep ingredients socketed)

Williams' `NEXP ⊄ ACC⁰` lower bound has the shape: *a fast `ACC⁰`-SAT algorithm, together with the assumption
`NEXP ⊆ ACC⁰`, would simulate nondeterministic exponential time too quickly, contradicting the nondeterministic time
hierarchy.*  This file formalises that **architecture** over an explicit complexity-class framework and proves the
**glue** (modus tollens), reducing Williams' theorem to its two genuinely-deep components — which remain *sockets*.

**This is not a proof of Williams' theorem.**  The two deep ingredients —
1. the **nondeterministic time hierarchy** (`NondetTimeHierarchy`, proved classically by diagonalisation over
   time-bounded nondeterministic Turing machines), and
2. the **easy-witness / SAT-speedup collapse** (`EasyWitnessCollapse`: a fast `ACC⁰`-SAT algorithm plus
   `NEXP ⊆ ACC⁰` simulate `NTIME[2ⁿ]` in `NTIME[2ⁿ/superpoly]`, via Impagliazzo–Kabanets–Wigderson easy witnesses) —
require a Turing-machine time-class infrastructure not present here (nor in Mathlib).  They are stated as named
hypotheses; only the logical composition is proved.

## Framework

* `Lang := List Bool → Prop` — a decision problem; `CClass := Set Lang` — a complexity class; class inclusion is `⊆`.
* `NEXP ACC0 NTIME2n NTIME2nFast : CClass`, `ACC0SatSpeedup : Prop` — the actors (abstract here).

## What is proved (clean axioms, no `sorry`)

* **`williams_meta_theorem`** — the glue: `EasyWitnessCollapse` ∧ `NondetTimeHierarchy` ∧ `ACC0SatSpeedup` ⇒
  `¬ (NEXP ⊆ ACC⁰)`.  (Modus tollens: the collapse would put `NTIME[2ⁿ]` inside `NTIME[2ⁿ/superpoly]`, which the
  hierarchy forbids.)
* **`nexp_not_acc0_via_williams`** — combined with the RS side: a proved RS representation `⇒` (via the `counting`
  socket) the SAT speedup `⇒` (via Williams' glue) the separation.

## Honest scope

Only the modus-tollens composition is proved.  The nondeterministic time hierarchy and the easy-witness collapse — the
actual mathematical content of Williams' theorem — are the named sockets `NondetTimeHierarchy` /
`EasyWitnessCollapse`; formalising them is a separate, major project (a verified NTM time-class library).  This file
makes Williams' proof skeleton explicit and machine-checks its glue.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem

/-- A decision problem. -/
abbrev Lang := List Bool → Prop

/-- A complexity class is a set of languages. -/
abbrev CClass := Set Lang

variable (NEXP ACC0 NTIME2n NTIME2nFast : CClass) (ACC0SatSpeedup : Prop)

/-- **Socket 1 — Williams' algorithmic core (easy-witness collapse).**  A fast `ACC⁰`-SAT algorithm together with
`NEXP ⊆ ACC⁰` simulates `NTIME[2ⁿ]` within `NTIME[2ⁿ/superpoly]` (Impagliazzo–Kabanets–Wigderson easy witnesses +
the SAT speedup).  Stated, not proved — it needs a verified NTM time-class library. -/
def EasyWitnessCollapse : Prop :=
  ACC0SatSpeedup → NEXP ⊆ ACC0 → NTIME2n ⊆ NTIME2nFast

/-- **Socket 2 — the nondeterministic time hierarchy.**  `NTIME[2ⁿ]` is not contained in `NTIME[2ⁿ/superpoly]`
(classical diagonalisation over time-bounded nondeterministic Turing machines).  Stated, not proved. -/
def NondetTimeHierarchy : Prop :=
  ¬ (NTIME2n ⊆ NTIME2nFast)

/-- **Williams' meta-theorem, glue proved (modus tollens).**  Given the easy-witness collapse and the nondeterministic
time hierarchy, a fast `ACC⁰`-SAT algorithm forces `NEXP ⊄ ACC⁰`: if `NEXP ⊆ ACC⁰` held, the collapse would put
`NTIME[2ⁿ] ⊆ NTIME[2ⁿ/superpoly]`, contradicting the hierarchy. -/
theorem williams_meta_theorem
    (collapse : EasyWitnessCollapse NEXP ACC0 NTIME2n NTIME2nFast ACC0SatSpeedup)
    (hierarchy : NondetTimeHierarchy NTIME2n NTIME2nFast)
    (speedup : ACC0SatSpeedup) :
    ¬ (NEXP ⊆ ACC0) := by
  intro hsub
  exact hierarchy (collapse speedup hsub)

/-- **Route B fused with Williams (proved conditional).**  A proved RS representation `rs` yields the `ACC⁰`-SAT
speedup via the `counting` socket; Williams' glue then gives `NEXP ⊄ ACC⁰`.  Conditional on the `counting` socket and
Williams' two deep ingredients (`collapse`, `hierarchy`). -/
theorem nexp_not_acc0_via_williams {RSRep : Prop}
    (rs : RSRep) (counting : RSRep → ACC0SatSpeedup)
    (collapse : EasyWitnessCollapse NEXP ACC0 NTIME2n NTIME2nFast ACC0SatSpeedup)
    (hierarchy : NondetTimeHierarchy NTIME2n NTIME2nFast) :
    ¬ (NEXP ⊆ ACC0) :=
  williams_meta_theorem NEXP ACC0 NTIME2n NTIME2nFast ACC0SatSpeedup collapse hierarchy
    (counting rs)

end PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem.williams_meta_theorem
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem.nexp_not_acc0_via_williams
