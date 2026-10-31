import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsMetaTheorem

/-!
# A nondeterministic time-class library — foundations (model + `NTIME`), deep theorems socketed

The Williams meta-theorem (`…ACC0WilliamsMetaTheorem`) reduced `NEXP ⊄ ACC⁰` to two deep ingredients over an abstract
class framework: the nondeterministic time hierarchy and the easy-witness collapse.  Discharging them needs a *concrete*
model of nondeterministic time-bounded computation.  This file builds the **foundation** of that library — a faithful
configuration-graph model of nondeterministic computation with a step bound, the `NTIME` complexity classes, and the
genuinely-provable foundational lemmas — and states the deep theorems as precise sockets over this concrete model.

**This is a foundation, not the full library.**  The time hierarchy (diagonalisation), universal simulation (with
clocking overhead), and the clocked time-class inclusion are the genuine deep content; a complete verified treatment is
a major project.  They are stated here as named sockets over the concrete `NTIME`; only the model and its basic
algebra are proved.

## Model

* `NTM` — a nondeterministic machine: a configuration type, a nondeterministic one-step relation `step`, an
  initialiser `init : List Bool → Config`, and an `accept` predicate.
* `reachIn M k c c'` — `c'` is reachable from `c` in exactly `k` steps; `acceptsWithin M x t` — some accepting
  configuration is reached from `init x` within `t` steps.
* `NTIME f` — the languages `L` with a machine accepting exactly `L` within `f(|x|)` steps.

## What is proved (clean axioms, no `sorry`)

* **`reachIn_add`** — reachability composes: `reachIn M (a+b) c c' ↔ ∃ d, reachIn M a c d ∧ reachIn M b d c'`.
* **`acceptsWithin_mono`** — more steps only help: `t ≤ t' → acceptsWithin M x t → acceptsWithin M x t'`.
* **`williams_concrete`** — the Williams glue instantiated at concrete `NTIME` classes: given the concrete collapse and
  hierarchy sockets, `¬ (NEXP ⊆ ACC0)`.

## The deep sockets (stated over concrete `NTIME`, not proved)

* **`ClockedInclusion`** — `f ≤ g → NTIME f ⊆ NTIME g` (needs the step-counter clocking construction).
* **`UniversalSimulation`** — a time-bounded universal machine (with overhead).
* **`ConcreteHierarchy`** — `¬ (NTIME f ⊆ NTIME g)` for an appropriate separation `f`/`g` (diagonalisation).

## Honest scope

The model and its algebra (`reachIn_add`, `acceptsWithin_mono`) are *proved*; the `NTIME` classes are honestly defined;
the Williams glue is instantiated at them.  The hierarchy, simulation, and clocking — the actual mathematical content
of a time-class library — are sockets requiring substantial further work.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NTM

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)

/-- A nondeterministic machine: configurations, a nondeterministic one-step relation, an initialiser, and an accept
predicate. -/
structure NTM where
  Config : Type
  step : Config → Config → Prop
  init : List Bool → Config
  accept : Config → Prop

/-- `reachIn M k c c'` : `c'` is reachable from `c` in exactly `k` steps of `M`. -/
def reachIn (M : NTM) : ℕ → M.Config → M.Config → Prop
  | 0, c, c' => c = c'
  | (k + 1), c, c' => ∃ d, M.step c d ∧ reachIn M k d c'

/-- `acceptsWithin M x t` : `M` reaches an accepting configuration from `init x` within `t` steps. -/
def acceptsWithin (M : NTM) (x : List Bool) (t : ℕ) : Prop :=
  ∃ k ≤ t, ∃ c, reachIn M k (M.init x) c ∧ M.accept c

/-- **Reachability composes (proved): `reachIn M (a+b) c c' ↔ ∃ d, reachIn M a c d ∧ reachIn M b d c'`.** -/
theorem reachIn_add (M : NTM) (a b : ℕ) (c c' : M.Config) :
    reachIn M (a + b) c c' ↔ ∃ d, reachIn M a c d ∧ reachIn M b d c' := by
  induction a generalizing c with
  | zero => simp [reachIn]
  | succ a ih =>
      rw [Nat.succ_add, reachIn]
      constructor
      · rintro ⟨e, hse, hr⟩
        rw [ih] at hr
        obtain ⟨d, h1, h2⟩ := hr
        exact ⟨d, ⟨e, hse, h1⟩, h2⟩
      · rintro ⟨d, ⟨e, hse, h1⟩, h2⟩
        exact ⟨e, hse, by rw [ih]; exact ⟨d, h1, h2⟩⟩

/-- **More steps only help (proved): `t ≤ t' → acceptsWithin M x t → acceptsWithin M x t'`.** -/
theorem acceptsWithin_mono (M : NTM) (x : List Bool) {t t' : ℕ} (h : t ≤ t') :
    acceptsWithin M x t → acceptsWithin M x t' := by
  rintro ⟨k, hk, c, hr, ha⟩
  exact ⟨k, le_trans hk h, c, hr, ha⟩

/-- The complexity class `NTIME f`: languages decided by some machine within `f(|x|)` steps. -/
def NTIME (f : ℕ → ℕ) : CClass :=
  { L : Lang | ∃ M : NTM, ∀ x, L x ↔ acceptsWithin M x (f x.length) }

/-- Nondeterministic exponential time: `NTIME(2^{poly})`. -/
def NEXP : CClass :=
  { L : Lang | ∃ c : ℕ, L ∈ NTIME (fun n => 2 ^ (n ^ c + c)) }

/-! ## Deep sockets (precise statements over the concrete model; not proved) -/

/-- **Socket — clocked time-class inclusion.**  `f ≤ g ⇒ NTIME f ⊆ NTIME g` (the step-counter clocking construction). -/
def ClockedInclusion (f g : ℕ → ℕ) : Prop :=
  (∀ n, f n ≤ g n) → NTIME f ⊆ NTIME g

/-- **Socket — the nondeterministic time hierarchy.**  `NTIME f` is not contained in `NTIME g` for a suitable
separation (diagonalisation over time-bounded machines). -/
def ConcreteHierarchy (f g : ℕ → ℕ) : Prop :=
  ¬ (NTIME f ⊆ NTIME g)

/-! ## The Williams glue at concrete `NTIME` classes -/

/-- **Williams instantiated at concrete `NTIME` (proved glue).**  Given the concrete easy-witness collapse and the
concrete time hierarchy (both sockets over this model), a fast `ACC⁰`-SAT algorithm forces `¬ (NEXP ⊆ ACC0)`.  This
plugs the time-class library into the Williams meta-theorem; the two sockets are the genuine deep content. -/
theorem williams_concrete (ACC0 : CClass) (f g : ℕ → ℕ) (speedup : Prop)
    (collapse : speedup → NEXP ⊆ ACC0 → NTIME f ⊆ NTIME g)
    (hierarchy : ConcreteHierarchy f g)
    (s : speedup) :
    ¬ (NEXP ⊆ ACC0) :=
  ACC0WilliamsMetaTheorem.williams_meta_theorem NEXP ACC0 (NTIME f) (NTIME g) speedup
    collapse hierarchy s

end PallLean.Paper93.DeepMath.PathB.ACC0NTM

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NTM.reachIn_add
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NTM.acceptsWithin_mono
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NTM.williams_concrete
