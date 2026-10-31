import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA3
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMCSP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardnessMagnificationSocket
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverInvariantBridge

/-!
# Shrinkage to Observer/N-Frame: the honest bridge

The shrinkage campaign lives in the constant-extended De Morgan formula model
`DMTreeC`.  This file connects that model to the Observer/N-Frame program in
three precise layers.

1. **Observer identification.**  `dmsizeC` is exactly the generic N-Frame
   minimum-description invariant (`NFrameMCSP.mcsp`) instantiated with
   representations `DMTreeC`, semantics `DMTreeC.eval`, and cost `lsize0`.
   A verified DNF construction proves that this representation is surjective.
2. **Weak lower-bound target.**  A quantitative shrinkage/formula lower bound
   is packaged as a concrete `WeakMagnificationTarget`.
3. **Conditional cash-out.**  Given an actual non-natural, non-local hardness-
   magnification transport, the proved weak lower bound reaches the existing
   metacomplexity capstone and rules out the canonical polynomial-time SAT
   decider.  A second adapter records the stronger route to the repository's
   standard `P != NP` proposition: it additionally requires a machine-invariant
   transport turning shrinkage hardness into intrinsic SAT hardness for every
   decider, plus the already-formalized time calibration and Cook--Levin.

The load-bearing transport is deliberately explicit.  De Morgan formula lower
bounds do **not** imply general DAG-circuit lower bounds: sharing is exactly the
missing step, and making that implication automatic here would be false.
Nothing in this file proves the transport or `P != NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ShrinkObserverBridge

open PallLean.Paper93.DeepMath.PathB.Khrapchenko
open PallLean.Paper93.DeepMath.PathB.NFrameMCSP
open SATDepthMachine

/-! ## A complete De Morgan representation -/

/-- The minterm for assignment `a`, over a supplied coordinate list. -/
def mintermC {n : ℕ} (a : Fin n → Bool) : List (Fin n) → DMTreeC n
  | [] => .cst true
  | i :: is => .and (.lit i (a i)) (mintermC a is)

theorem eval_mintermC {n : ℕ} (a : Fin n → Bool) (is : List (Fin n))
    (x : Fin n → Bool) :
    (mintermC a is).eval x = is.all (fun i => x i == a i) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [mintermC, DMTreeC.eval, ih]

/-- A full minterm recognizes exactly its assignment. -/
theorem eval_mintermC_eq_true_iff {n : ℕ} (a x : Fin n → Bool) :
    (mintermC a (List.finRange n)).eval x = true ↔ x = a := by
  rw [eval_mintermC, List.all_eq_true]
  constructor
  · intro h
    funext i
    exact beq_iff_eq.mp (h i (List.mem_finRange i))
  · rintro rfl i _
    simp

/-- An OR-chain of minterms. -/
def dnfOnC {n : ℕ} : List (Fin n → Bool) → DMTreeC n
  | [] => .cst false
  | a :: as => .or (mintermC a (List.finRange n)) (dnfOnC as)

theorem eval_dnfOnC {n : ℕ} (as : List (Fin n → Bool)) (x : Fin n → Bool) :
    (dnfOnC as).eval x =
      as.any (fun a => (mintermC a (List.finRange n)).eval x) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [dnfOnC, DMTreeC.eval, ih]

/-- The DNF formula containing precisely the accepted assignments of `f`. -/
noncomputable def dnfForC {n : ℕ} (f : (Fin n → Bool) → Bool) : DMTreeC n :=
  dnfOnC ((Finset.univ : Finset (Fin n → Bool)).toList.filter f)

/-- The DNF representation computes `f`. -/
theorem eval_dnfForC {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (dnfForC f).eval = f := by
  funext x
  rw [dnfForC, eval_dnfOnC]
  cases hfx : f x with
  | true =>
      apply List.any_eq_true.mpr
      refine ⟨x, ?_, (eval_mintermC_eq_true_iff x x).mpr rfl⟩
      rw [List.mem_filter]
      exact ⟨Finset.mem_toList.mpr (Finset.mem_univ x), hfx⟩
  | false =>
      apply List.any_eq_false.mpr
      intro a ha hax
      rw [List.mem_filter] at ha
      have hxa := (eval_mintermC_eq_true_iff a x).mp hax
      subst a
      rw [hfx] at ha
      exact Bool.noConfusion ha.2

/-- Every Boolean function has a constant-extended De Morgan formula. -/
theorem dmTreeC_surjective {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∃ t : DMTreeC n, t.eval = f :=
  ⟨dnfForC f, eval_dnfForC f⟩

/-! ## `dmsizeC` is an N-Frame minimum-description observer -/

/-- The formula-size class at variable-leaf budget `s`. -/
def dmFormulaSizeClass {n : ℕ} (s : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ t : DMTreeC n, t.eval = f ∧ t.lsize0 ≤ s

/-- The shrinkage measure is exactly the generic N-Frame/MCSP invariant for
constant-extended De Morgan formulas. -/
theorem dmsizeC_eq_nframeMCSP {n : ℕ} (f : (Fin n → Bool) → Bool) :
    dmsizeC f = mcsp (fun t : DMTreeC n => t.eval) DMTreeC.lsize0 f := by
  unfold dmsizeC mcsp
  congr 1
  ext s
  constructor
  · rintro ⟨t, ht, hs⟩
    exact ⟨t, funext ht, hs⟩
  · rintro ⟨t, ht, hs⟩
    exact ⟨t, fun x => congrFun ht x, hs⟩

/-- The formula size class is the generic representation-size class. -/
theorem dmFormulaSizeClass_eq_nframeSizeClass {n : ℕ} (s : ℕ)
    (f : (Fin n → Bool) → Bool) :
    dmFormulaSizeClass s f ↔
      sizeClass (fun t : DMTreeC n => t.eval) DMTreeC.lsize0 s f := by
  rfl

/-- The exact Observer/N-Frame reading: a `dmsizeC` gap is formula-class
non-membership.  This is a restricted-model statement, not a DAG-circuit gap. -/
theorem dmsizeC_gap_iff_not_dmFormulaSizeClass {n : ℕ} (s : ℕ)
    (f : (Fin n → Bool) → Bool) :
    s < dmsizeC f ↔ ¬ dmFormulaSizeClass s f := by
  rw [dmsizeC_eq_nframeMCSP, dmFormulaSizeClass_eq_nframeSizeClass]
  exact mcsp_gap_iff_not_sizeClass
    (fun t : DMTreeC n => t.eval) DMTreeC.lsize0 dmTreeC_surjective s f

/-! ## Shrinkage as a concrete weak magnification target -/

/-- A Boolean-function family indexed by its input arity. -/
abbrev BoolFamily := (n : ℕ) → (Fin n → Bool) → Bool

/-- A quantitative lower bound supplied by shrinkage: every De Morgan formula
for `F n` has at least `q n` variable leaves. -/
def ShrinkageLowerBound (F : BoolFamily) (q : ℕ → ℕ) : Prop :=
  ∀ n (t : DMTreeC n), t.eval = F n → q n ≤ t.lsize0

/-- The already-proved parity calibration as an actual shrinkage-family lower
bound.  It demonstrates that the adapter consumes real theorems, while making
no claim that parity is a magnification-eligible metacomplexity target. -/
theorem parity_shrinkageLowerBound :
    ShrinkageLowerBound (fun n => oddF n) (fun n => n ^ 2) := by
  intro n t ht
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact parityC_lb (n + 1) (by omega) t (fun x => congrFun ht x)

/-- The concrete weak target presented to the repository's magnification
interface.  The lower bound is useful only when accompanied by a real transport. -/
def shrinkageMagnificationTarget
    (D : DescribedCanonicalSurface) (F : BoolFamily) (q : ℕ → ℕ) :
    WeakMagnificationTarget D where
  WeakLowerBound := ShrinkageLowerBound F q

/-- Package a proved shrinkage lower bound and an independently proved
non-natural/non-local transport as a genuine magnification breakthrough. -/
def shrinkageBreakthrough
    (D : DescribedCanonicalSurface) (F : BoolFamily) (q : ℕ → ℕ)
    (T : HardnessMagnificationTransport D
      (shrinkageMagnificationTarget D F q))
    (hLower : ShrinkageLowerBound F q)
    (hNonNatural : T.non_natural_guard)
    (hNonLocal : T.non_local_guard) :
    HardnessMagnificationBreakthrough D where
  target := shrinkageMagnificationTarget D F q
  transport := T
  weak_lower_bound := hLower
  non_natural := hNonNatural
  non_local := hNonLocal

/-- **Conditional capstone.**  Shrinkage reaches the existing Observer/N-Frame
metacomplexity conclusion exactly when the missing non-natural, non-local
magnification transport is supplied. -/
theorem noCanonicalSATDecisionInP_of_shrinkage
    (D : DescribedCanonicalSurface) (F : BoolFamily) (q : ℕ → ℕ)
    (T : HardnessMagnificationTransport D
      (shrinkageMagnificationTarget D F q))
    (hLower : ShrinkageLowerBound F q)
    (hNonNatural : T.non_natural_guard)
    (hNonLocal : T.non_local_guard) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_hardnessMagnificationBreakthrough D
    (shrinkageBreakthrough D F q T hLower hNonNatural hNonLocal)

/-- The corresponding bundled route conclusion, retaining the generator
lower-bound statement as well as no canonical polynomial-time SAT decision. -/
theorem ktRoute_finalClosure_of_shrinkage
    (D : DescribedCanonicalSurface) (F : BoolFamily) (q : ℕ → ℕ)
    (T : HardnessMagnificationTransport D
      (shrinkageMagnificationTarget D F q))
    (hLower : ShrinkageLowerBound F q)
    (hNonNatural : T.non_natural_guard)
    (hNonLocal : T.non_local_guard) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure_of_hardnessMagnificationBreakthrough D
    (shrinkageBreakthrough D F q T hLower hNonNatural hNonLocal)

/-! ## Direct observer-invariant route to the standard separation proposition -/

open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge

/-- The missing semantic adapter from a formula shrinkage theorem to an
intrinsic machine invariant.  Its load-bearing field quantifies over every SAT
decider through `InvHard`; this is strictly stronger than exhibiting a hard
formula representation and is intentionally not manufactured from syntax. -/
structure ShrinkageObserverTransport
    (SATV : NPObs) (Inv : Invariant) (F : BoolFamily) (q : ℕ → ℕ) where
  time_bounded : InvTimeBounded SATV Inv
  shrinkage_to_intrinsic_hardness : ShrinkageLowerBound F q → InvHard SATV Inv

/-- **Standard conditional separation capstone.**  A proved shrinkage lower
bound yields `P != NP` once a calibrated, representation-independent transport
to intrinsic SAT hardness and Cook--Levin are supplied.  The theorem exposes
the real open seam; it does not infer machine hardness from formula hardness. -/
theorem PneqNP_of_shrinkage_observer
    (SATV : NPObs) (Inv : Invariant) (F : BoolFamily) (q : ℕ → ℕ)
    (T : ShrinkageObserverTransport SATV Inv F q)
    (hLower : ShrinkageLowerBound F q)
    (hCL : CookLevin SATV) :
    ¬ PeqNP :=
  PneqNP_from_timeBounded SATV Inv T.time_bounded
    (T.shrinkage_to_intrinsic_hardness hLower) hCL

end PallLean.Paper93.DeepMath.PathB.ShrinkObserverBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkObserverBridge.eval_dnfForC
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkObserverBridge.dmsizeC_eq_nframeMCSP
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkObserverBridge.dmsizeC_gap_iff_not_dmFormulaSizeClass
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkObserverBridge.parity_shrinkageLowerBound
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkObserverBridge.noCanonicalSATDecisionInP_of_shrinkage
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkObserverBridge.PneqNP_of_shrinkage_observer
