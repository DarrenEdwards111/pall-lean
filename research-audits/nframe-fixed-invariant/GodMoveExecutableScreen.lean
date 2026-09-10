import GodMoveExpanderScreen
import GodMoveMonomialMinor

/-!
# Direct binary encoding of one expander screen

The code scans the indexed edges and appends their parity bits. Erased edges
contribute zero. It never enumerates the type of all possible screens.
Injectivity is derived from binary uniqueness and the existing graph-expansion
theorem. The instrumented implementation counts one erasure check and binary
append per edge, and at most |S| constraint steps per retained edge. A constraint
step is one endpoint-membership query and one addition in F₂; these counts do
not include the bit cost of graph access, membership, or integer arithmetic.

This is per-label execution. It does not evaluate the full binomial-size
coefficient boundary or efficiently construct the normalized SAT polynomial.
-/

namespace GodMoveExecutableScreen

open PallLean.Paper93.DeepMath.PathB
open GodMoveExpanderScreen GodMoveMonomialMinor
open scoped BigOperators

/-- A little-endian binary encoder with an explicit edge-index recursion. -/
def binaryCode : {E : ℕ} → (Fin E → ZMod 2) → ℕ
  | 0, _ => 0
  | E + 1, f => (f 0).val + 2 * binaryCode (fun i : Fin E => f i.succ)

theorem binaryCode_lt {E : ℕ} (f : Fin E → ZMod 2) : binaryCode f < 2 ^ E := by
  induction E with
  | zero => simp [binaryCode]
  | succ E ih =>
    have ht := ih (fun i : Fin E => f i.succ)
    have hh := (f 0).val_lt
    simp only [binaryCode, pow_succ]
    omega

/-- Every fixed-width parity vector has a distinct binary code. -/
theorem binaryCode_injective (E : ℕ) : Function.Injective (@binaryCode E) := by
  induction E with
  | zero =>
    intro f g _
    funext i
    exact Fin.elim0 i
  | succ E ih =>
    intro f g h
    have hf := (f 0).val_lt
    have hg := (g 0).val_lt
    simp only [binaryCode] at h
    have hhead : (f 0).val = (g 0).val := by omega
    have htail : binaryCode (fun i : Fin E => f i.succ) =
        binaryCode (fun i : Fin E => g i.succ) := by omega
    have heq := ih htail
    funext i
    refine Fin.cases ?_ (fun j => congrFun heq j) i
    exact ZMod.val_injective 2 hhead

/-- Zero erased coordinates; compute each retained parity from actual constraints. -/
def erasedParity {m E : ℕ} (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (S : Finset (Fin m)) (e : Fin E) : ZMod 2 :=
  if e ∈ erased then 0 else G.combination S e

/-- Executable bounded screen code, without a finite-type enumeration. -/
def screenCode {m E : ℕ} (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (S : Finset (Fin m)) : Fin (2 ^ E) :=
  ⟨binaryCode (erasedParity G erased S), binaryCode_lt _⟩

theorem screenCode_eq_iff {m E : ℕ} (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (S T : Finset (Fin m)) :
    screenCode G erased S = screenCode G erased T ↔
      screen G erased S = screen G erased T := by
  constructor
  · intro h
    have hb := binaryCode_injective E (congrArg Fin.val h)
    funext e
    have he := congrFun hb e.val
    simpa only [erasedParity, if_neg e.property, screen] using he
  · intro h
    apply Fin.ext
    change binaryCode (erasedParity G erased S) = binaryCode (erasedParity G erased T)
    apply congrArg binaryCode
    funext e
    by_cases he : e ∈ erased
    · simp [erasedParity, he]
    · have hh := congrFun h ⟨e, he⟩
      simpa only [erasedParity, if_neg he, screen] using hh

/-- The actual derivative label is encoded directly, one screen at a time. -/
def executableScreenLabel {m E k : ℕ} (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (S : KSubset m k) : Fin (2 ^ E) :=
  screenCode G erased S.val

theorem executableScreenLabel_injective {m E k c : ℕ}
    (G : TseitinGraph (Fin m) (Fin E)) (hexp : G.HasExpansion c)
    (hwindow : 4 * k ≤ m) (erased : Finset (Fin E))
    (herased : erased.card < 2 * c) :
    Function.Injective (executableScreenLabel (k := k) G erased) := by
  intro S T heq
  apply Subtype.ext
  exact screen_injective_on_card G hexp (by simpa using hwindow) erased herased
    (kSubset_size S) (kSubset_size T) ((screenCode_eq_iff G erased S.val T.val).mp heq)

/-- Count the actual finite constraint fold: each term performs one incidence
query and one parity addition. No choice of a finset enumeration is exposed. -/
def countedCombination {m E : ℕ} (G : TseitinGraph (Fin m) (Fin E))
    (S : Finset (Fin m)) (e : Fin E) : ZMod 2 × ℕ :=
  ∑ v ∈ S, (G.constraint v e, 1)

theorem countedCombination_spec {m E : ℕ} (G : TseitinGraph (Fin m) (Fin E))
    (S : Finset (Fin m)) (e : Fin E) :
    countedCombination G S e = (G.combination S e, S.card) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [countedCombination, TseitinGraph.combination, Finset.sum_empty,
      Finset.card_empty]
    rfl
  | @insert v S hv ih =>
    simp only [countedCombination, TseitinGraph.combination] at ih ⊢
    rw [Finset.sum_insert hv, Finset.sum_insert hv, Finset.card_insert_of_notMem hv, ih]
    simp [Nat.add_comm]

structure CodeRun where
  value : ℕ
  edgeVisits : ℕ
  constraintSteps : ℕ
deriving Repr, DecidableEq

/-- The explicit edge loop evaluates each supplied parity fold once. -/
def runBinary : {E : ℕ} → (Fin E → ZMod 2 × ℕ) → CodeRun
  | 0, _ => ⟨0, 0, 0⟩
  | E + 1, f =>
      let head := f 0
      let tail := runBinary (fun i : Fin E => f i.succ)
      ⟨head.1.val + 2 * tail.value, tail.edgeVisits + 1,
        head.2 + tail.constraintSteps⟩

theorem runBinary_spec {E : ℕ} (f : Fin E → ZMod 2 × ℕ)
    (b : ℕ) (hb : ∀ i, (f i).2 ≤ b) :
    (runBinary f).value = binaryCode (fun i => (f i).1) ∧
      (runBinary f).edgeVisits = E ∧ (runBinary f).constraintSteps ≤ E * b := by
  induction E with
  | zero => simp [runBinary, binaryCode]
  | succ E ih =>
    obtain ⟨hv, he, hc⟩ := ih (fun i : Fin E => f i.succ) (fun i => hb i.succ)
    have hh := hb 0
    simp only [runBinary, binaryCode]
    exact ⟨by rw [hv], by omega, by nlinarith⟩

/-- Executable screen generation with the primitive counters carried along. -/
def screenRun {m E : ℕ} (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (S : Finset (Fin m)) : CodeRun :=
  runBinary (fun e => if e ∈ erased then (0, 0) else countedCombination G S e)

/-- One supplied label costs E edge visits and at most E*|S| constraint steps.
Each visit includes one erasure test and one binary append. -/
theorem screenRun_spec {m E : ℕ} (G : TseitinGraph (Fin m) (Fin E))
    (erased : Finset (Fin E)) (S : Finset (Fin m)) :
    (screenRun G erased S).value = (screenCode G erased S).val ∧
      (screenRun G erased S).edgeVisits = E ∧
      (screenRun G erased S).constraintSteps ≤ E * S.card := by
  have h := runBinary_spec
    (fun e => if e ∈ erased then (0, 0) else countedCombination G S e) S.card
    (fun e => by by_cases he : e ∈ erased <;> simp [he, countedCombination_spec])
  simpa [screenRun, screenCode, erasedParity, countedCombination_spec,
    apply_ite Prod.fst] using h

/-- Kernel-evaluated calibration: direct little-endian K4 singleton codes. -/
theorem K4_singleton_codes :
    (screenCode K4 ∅ {0}).val = 7 ∧
    (screenCode K4 ∅ {1}).val = 25 ∧
    (screenCode K4 ∅ {2}).val = 42 ∧
    (screenCode K4 ∅ {3}).val = 52 := by decide

theorem K4_erased_codes :
    (screenCode K4 {0, 1, 2} {0}).val = 0 ∧
    (screenCode K4 {0, 1, 2} {1}).val = 24 ∧
    (screenCode K4 {0, 1, 2} {2}).val = 40 ∧
    (screenCode K4 {0, 1, 2} {3}).val = 48 := by decide

#eval screenRun K4 ∅ {0}
#eval screenRun K4 {0, 1, 2} {1}

end GodMoveExecutableScreen

#print axioms GodMoveExecutableScreen.binaryCode_lt
#print axioms GodMoveExecutableScreen.binaryCode_injective
#print axioms GodMoveExecutableScreen.screenCode_eq_iff
#print axioms GodMoveExecutableScreen.executableScreenLabel_injective
#print axioms GodMoveExecutableScreen.countedCombination_spec
#print axioms GodMoveExecutableScreen.runBinary_spec
#print axioms GodMoveExecutableScreen.screenRun_spec
#print axioms GodMoveExecutableScreen.K4_singleton_codes
#print axioms GodMoveExecutableScreen.K4_erased_codes
