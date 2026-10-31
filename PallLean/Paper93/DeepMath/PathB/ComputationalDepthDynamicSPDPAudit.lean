import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResidualInvariantNoGo
import Mathlib.Algebra.BigOperators.Fin

/-!
# Dynamic SPDP: the trilemma

`ComputationalDepthNFrameConcreteInvariant` killed *static* representation-SPDP rank, and
`ComputationalDepthResidualInvariantNoGo` killed the intrinsic residual-rank repair (fails `PUpper`).  The
remaining N-Frame candidate is a **dynamic** (time / causal-evolution) SPDP.  Book 1 gives no precise
complexity-theoretic definition; there are three natural ones, and this file proves each meets a distinct fate.

* **Horn 1 — attached dynamic SPDP is representation-dependent.**  A time-indexed sheet attached to a
  computation carries irrelevant high-rank dynamics without changing the decision, so the same decision function
  admits computations of unboundedly different cumulative rank.  This is the `e29c9238` countermodel over time.
  (`horn1_attached_representation_dependent`.)

* **Horn 2 — global-across-input dynamic rank is exponential for an easy P family.**  Aggregating rank over the
  configurations reached across *all* inputs of length `n` is super-polynomial even for a trivial language: a
  machine that merely copies its input into its state has `2^n` distinct configurations while deciding the
  constant-`false` language in `0` steps.  So this measure fails `PUpper`.  (`horn2_global_exponential`.)

* **Horn 3 — actual-trace dynamic rank is polynomially bounded by runtime; its SAT lower bound is the open
  obligation.**  The per-run trace rank (number of steps at which the configuration changes) is `≤ runtime`, so
  it **clears** `PUpper` (`Rtrace_PUpper`).  Its only open gate, `SATLower`, already *implies* `SAT ∉ P`
  (`Rtrace_satLower_imp_notInP`) — i.e. proving it is precisely the unresolved time-lower-bound breakthrough,
  not a representational shortcut.

The bundled statement is `dynamic_spdp_trilemma`.  A fourth definition escaping all three horns would be the
candidate worth pursuing; naive dynamic versions fail for the same reasons as static rank.

## Honest scope

A machine-checked audit of the three natural dynamic-SPDP definitions.  Horns 1–2 are no-go countermodels;
horn 3 shows the only survivor reduces its remaining gate to a genuine `SAT ∉ P` time lower bound, which is
**not** discharged here.  No lower bound is proved and no separating invariant is supplied.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DynamicSPDPAudit

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant
open PallLean.Paper93.DeepMath.PathB.ResidualInvariantNoGo

/-- The identity-sheet row map has `2^n` distinct rows (the `e29c9238` computation, reused). -/
theorem card_range_decide_eq (n : Nat) :
    Nat.card (Set.range (fun x : Fin n → Bool => fun y : Fin n → Bool => decide (x = y))) = 2 ^ n := by
  have hinj : Function.Injective
      (fun x : Fin n → Bool => fun y : Fin n → Bool => decide (x = y)) := by
    intro a b h
    by_contra hne
    have hc : decide (a = a) = decide (b = a) := congrFun h a
    rw [decide_eq_false (fun hba : b = a => hne hba.symm)] at hc
    simp at hc
  rw [Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-! ## Horn 1: attached dynamic SPDP is representation-dependent -/

/-- A computation with a **time-indexed** attached SPDP sheet: a decision function plus, for each of `Steps`
time steps, a Boolean representation matrix (rows = inputs, columns = probes). -/
structure DynAttached (n : Nat) where
  decision : (Fin n → Bool) → Bool
  Steps : Nat
  Probe : Type
  probeFintype : Fintype Probe
  sheet : Fin Steps → (Fin n → Bool) → Probe → Bool

/-- Cumulative dynamic rank: sum over time of the number of distinct rows at each step. -/
noncomputable def dynAttachedRank {n : Nat} (C : DynAttached n) : Nat :=
  ∑ t : Fin C.Steps, Nat.card (Set.range (C.sheet t))

/-- Constant time-indexed sheet: one step, all rows equal — cumulative rank `1`. -/
def trivialDyn {n : Nat} (f : (Fin n → Bool) → Bool) : DynAttached n where
  decision := f
  Steps := 1
  Probe := Unit
  probeFintype := inferInstance
  sheet := fun _ _ _ => false

/-- Identity time-indexed sheet: one step, identity matrix — cumulative rank `2^n`. -/
def identityDyn {n : Nat} (f : (Fin n → Bool) → Bool) : DynAttached n where
  decision := f
  Steps := 1
  Probe := Fin n → Bool
  probeFintype := inferInstance
  sheet := fun _ x y => decide (x = y)

theorem trivialDyn_rank {n : Nat} (f : (Fin n → Bool) → Bool) :
    dynAttachedRank (trivialDyn f) = 1 := by
  show (∑ _t : Fin 1, Nat.card (Set.range (fun _ : Fin n → Bool => (fun _ : Unit => false)))) = 1
  rw [Fin.sum_univ_one]
  have hset : Set.range (fun _ : Fin n → Bool => (fun _ : Unit => false)) = {fun _ : Unit => false} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨fun _ => default, rfl⟩, ?_⟩
    rintro y ⟨x, rfl⟩; rfl
  rw [hset, Nat.card_eq_fintype_card, Fintype.card_unique]

theorem identityDyn_rank {n : Nat} (f : (Fin n → Bool) → Bool) :
    dynAttachedRank (identityDyn f) = 2 ^ n := by
  show (∑ _t : Fin 1,
    Nat.card (Set.range (fun x : Fin n → Bool => fun y : Fin n → Bool => decide (x = y)))) = 2 ^ n
  rw [Fin.sum_univ_one]
  exact card_range_decide_eq n

/-- **Horn 1.**  For every bound `B` there are two computations of the *same* decision whose cumulative dynamic
ranks differ by more than a factor `B`.  A time-indexed attached sheet measures the representation, not the
decision — the static no-go survives time-indexing. -/
theorem horn1_attached_representation_dependent :
    ∀ B : Nat, ∃ (n : Nat) (C₁ C₂ : DynAttached n),
      C₁.decision = C₂.decision ∧ B * dynAttachedRank C₁ < dynAttachedRank C₂ := by
  intro B
  refine ⟨B + 1, trivialDyn (fun _ => false), identityDyn (fun _ => false), rfl, ?_⟩
  rw [trivialDyn_rank, identityDyn_rank, mul_one]
  calc B < 2 ^ B := B.lt_two_pow_self
    _ ≤ 2 ^ (B + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ B)

/-! ## Horn 2: global-across-input dynamic rank is exponential for an easy P family -/

/-- A machine that copies its input into its configuration and decides the constant-`false` language in `0`
steps — as easy as a language gets, yet its configurations distinguish all `2^n` inputs. -/
def copyMachine : ClockedMachine where
  Config := List Bool
  init := fun x => x
  next := fun c => c
  output := fun _ => false
  runtime := fun _ => 0

/-- Global rank at length `n`: the number of distinct initial configurations across all length-`n` inputs. -/
noncomputable def Rglobal (M : ClockedMachine) (n : Nat) : Nat :=
  Nat.card (Set.range (fun a : Fin n → Bool => M.init (List.ofFn a)))

theorem copyMachine_polyTime : IsPolyTime copyMachine :=
  ⟨0, 0, fun _ => Nat.zero_le _⟩

/-- `copyMachine` decides the (trivial) constant-`false` language. -/
theorem copyMachine_decides_const : Decides copyMachine (fun _ => false) :=
  fun _ => rfl

theorem Rglobal_copyMachine (n : Nat) : Rglobal copyMachine n = 2 ^ n := by
  have hinj : Function.Injective (fun a : Fin n → Bool => copyMachine.init (List.ofFn a)) := by
    intro a b h
    simp only [copyMachine] at h
    exact List.ofFn_inj.mp h
  rw [Rglobal, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- **Horn 2.**  A polynomial-time (in fact `0`-step) machine deciding a trivial language has super-polynomial
global-across-input dynamic rank.  So aggregating rank over all inputs fails `PUpper` — exactly the failure of
the global-across-input configuration count. -/
theorem horn2_global_exponential :
    ∃ M : ClockedMachine, IsPolyTime M ∧ ¬ PolyBounded (Rglobal M) := by
  refine ⟨copyMachine, copyMachine_polyTime, ?_⟩
  have heq : Rglobal copyMachine = fun n => 2 ^ n := funext Rglobal_copyMachine
  rw [heq]; exact two_pow_not_polyBounded

/-! ## Horn 3: actual-trace dynamic rank is poly-bounded by runtime; SAT lower bound = the open obligation -/

open Classical in
/-- **Per-run trace rank.**  The number of steps of `M` on input `x` (within its clock) at which the
configuration actually changes — the cumulative rank of the trace's changes, with unit charge per step. -/
noncomputable def traceRank (M : ClockedMachine) (x : List Bool) : Nat :=
  ((Finset.range (M.runtime x)).filter
    (fun t => M.next (M.next^[t] (M.init x)) ≠ M.next^[t] (M.init x))).card

/-- The trace rank is bounded by the runtime: at most one unit of change per clocked step. -/
theorem traceRank_le_runtime (M : ClockedMachine) (x : List Bool) :
    traceRank M x ≤ M.runtime x := by
  classical
  calc traceRank M x ≤ (Finset.range (M.runtime x)).card := Finset.card_filter_le _ _
    _ = M.runtime x := Finset.card_range _

/-- The per-run trace rank lifted to `ℕ → ℕ`: the worst case over length-`n` inputs. -/
noncomputable def Rtrace (M : ClockedMachine) (n : Nat) : Nat :=
  (Finset.univ : Finset (Fin n → Bool)).sup (fun a => traceRank M (List.ofFn a))

/-- **The trace rank clears `PUpper`.**  Because trace rank `≤ runtime` and a polynomial-time machine has
polynomial runtime, the trace rank is polynomially bounded on every polynomial-time machine — unlike the static,
residual, attached, and global variants. -/
theorem Rtrace_PUpper : PUpper Rtrace := by
  intro M hM
  obtain ⟨c, k, hck⟩ := hM
  refine ⟨c, k, fun n => ?_⟩
  apply Finset.sup_le
  intro a _
  calc traceRank M (List.ofFn a) ≤ M.runtime (List.ofFn a) := traceRank_le_runtime _ _
    _ ≤ c * ((List.ofFn a).length + 1) ^ k := hck _
    _ = c * (n + 1) ^ k := by rw [List.length_ofFn]

/-- **Horn 3.**  Since `Rtrace` clears `PUpper`, its `SATLower` obligation already *implies* `SAT ∉ P`: proving
the trace-rank SAT lower bound is precisely the unresolved time-lower-bound breakthrough, discharged nowhere
here.  This is the only one of the three dynamic definitions that is not a countermodel — and its remaining gate
is the genuine obstruction, not a representational shortcut. -/
theorem Rtrace_satLower_imp_notInP (L : List Bool → Bool) (h : SATLower Rtrace L) : ¬ InP L :=
  no_InP_of_invariant Rtrace L Rtrace_PUpper h

/-! ## The trilemma -/

/-- **Dynamic SPDP trilemma.**  (1) The attached (representation-indexed) dynamic rank is representation-
dependent; (2) the global-across-input dynamic rank is exponential for an easy `P` family; (3) the actual-trace
dynamic rank is polynomially bounded (clears `PUpper`) but its SAT lower bound implies `SAT ∉ P` — the open
obligation.  Naive dynamic SPDP fails exactly as static rank did; a viable candidate must escape all three
horns. -/
theorem dynamic_spdp_trilemma :
    (∀ B : Nat, ∃ (n : Nat) (C₁ C₂ : DynAttached n),
        C₁.decision = C₂.decision ∧ B * dynAttachedRank C₁ < dynAttachedRank C₂)
      ∧ (∃ M : ClockedMachine, IsPolyTime M ∧ ¬ PolyBounded (Rglobal M))
      ∧ (PUpper Rtrace ∧ ∀ L : List Bool → Bool, SATLower Rtrace L → ¬ InP L) :=
  ⟨horn1_attached_representation_dependent, horn2_global_exponential,
    Rtrace_PUpper, fun L => Rtrace_satLower_imp_notInP L⟩

end PallLean.Paper93.DeepMath.PathB.DynamicSPDPAudit

#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPAudit.horn1_attached_representation_dependent
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPAudit.horn2_global_exponential
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPAudit.Rtrace_PUpper
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPAudit.dynamic_spdp_trilemma
