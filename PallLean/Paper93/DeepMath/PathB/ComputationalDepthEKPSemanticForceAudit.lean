import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInstrumentedSheetAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOperationalTraceSemanticRank

/-!
# EKP semantic-force audit

The book's strongest candidate for the missing theorem is the Epistemic Kakeya
Principle (EKP): a correct SAT decider should somehow realize all inferential
directions of the SAT instance.  This file makes that target precise enough to
test.

There are two readings.

* **Run-indexed EKP coverage**: every direction is witnessed by an actual time
  in the deterministic DTM run.  This is the classical/semantic reading most
  directly tied to machine execution.
* **Non-local EKP coverage**: directions are supplied by a stronger semantic
  object not indexed by the run trace.  This is the only remaining possible
  breakthrough shape.

The theorem below proves that run-indexed EKP coverage cannot carry the
paper-scale binomial boundary for polynomial-time DTMs: an actual run has only
polynomially many time indices.  Therefore any successful EKP force theorem
must be non-local in a precise sense; it cannot be a counting of actual
configurations in the run.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open InstrumentedSheetAudit

/-! ## Run-indexed EKP directions -/

/-- A run-indexed realization of `directionCount` EKP directions.

Each direction is assigned a distinct time in the actual DTM run window.  This
is the broadest direct "the classical run sees every direction" shape that
still ties directions to actual machine semantics instead of external
bookkeeping. -/
structure RunIndexedEKPDirectionRealization
    (M : TuringMachine.DTM) (n : Nat) (input : Fin n -> Bool)
    (directionCount : Nat) : Type where
  timeOf : Fin directionCount -> Nat
  time_lt : forall d : Fin directionCount,
    timeOf d < TuringMachine.timeSteps M n + 1
  injective_timeOf : Function.Injective timeOf

namespace RunIndexedEKPDirectionRealization

/-- The directions inject into the finite time window of the run. -/
def timeEmbedding
    {M : TuringMachine.DTM} {n : Nat} {input : Fin n -> Bool}
    {directionCount : Nat}
    (R : RunIndexedEKPDirectionRealization M n input directionCount) :
    Fin directionCount -> Fin (TuringMachine.timeSteps M n + 1) :=
  fun d => ⟨R.timeOf d, R.time_lt d⟩

/-- Run-indexed EKP direction coverage is bounded by the actual run time
window. -/
theorem directionCount_le_timeWindow
    {M : TuringMachine.DTM} {n : Nat} {input : Fin n -> Bool}
    {directionCount : Nat}
    (R : RunIndexedEKPDirectionRealization M n input directionCount) :
    directionCount <= TuringMachine.timeSteps M n + 1 := by
  have hinj : Function.Injective R.timeEmbedding := by
    intro a b h
    apply R.injective_timeOf
    exact congrArg Fin.val h
  have hcard :=
    Fintype.card_le_of_injective R.timeEmbedding hinj
  simpa using hcard

end RunIndexedEKPDirectionRealization

/-- A paper-scale EKP boundary claim realized directly by the actual run.

The lower bound is expressed as a number of independent EKP directions.  The
realization then forces those directions to be represented by distinct actual
run times. -/
structure RunIndexedEKPBoundaryVisible
    (enc : ThreeCNFEncoding) (M : TuringMachine.DTM) (n : Nat) : Type where
  input : Fin n -> Bool
  directionCount : Nat
  binomial_le_directions :
    Nat.choose (n / 3) (Nat.log 2 n) <= directionCount
  realization :
    RunIndexedEKPDirectionRealization M n input directionCount

namespace RunIndexedEKPBoundaryVisible

/-- A run-indexed visible boundary is polynomially bounded by the DTM time
exponent. -/
theorem directionCount_le_next_power
    {enc : ThreeCNFEncoding} {M : TuringMachine.DTM} {n : Nat}
    (B : RunIndexedEKPBoundaryVisible enc M n)
    (hn2 : 2 <= n) :
    B.directionCount <= n ^ (M.timeBound + 1) := by
  exact le_trans
    B.realization.directionCount_le_timeWindow
    (timeWindow_succ_le_next_power M hn2)

end RunIndexedEKPBoundaryVisible

/-- The run-indexed EKP version of the desired semantic force theorem.

For each polynomial exponent `c`, the theorem asks for some large scale where
every encoded SAT decider realizes the paper-scale EKP boundary in its actual
run.  This is deliberately strong enough to imply the no-decider endpoint if it
were true. -/
def RunIndexedClassicalSATDeciderForcesEKPBoundary
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        Nonempty (RunIndexedEKPBoundaryVisible enc M n)

/-- A poly-time DTM cannot realize the paper-scale binomial EKP boundary by
injecting the directions into its actual run times. -/
theorem no_runIndexedEKPBoundaryVisible_at_paperScale
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * ((M.timeBound + 1) + 1) <= Nat.log 2 n) :
    Not (Nonempty (RunIndexedEKPBoundaryVisible enc M n)) := by
  intro hB
  rcases hB with ⟨B⟩
  have hn2 : 2 <= n :=
    le_trans (by norm_num : 2 <= 2 ^ 20) hn20
  have hdir_le_poly :
      B.directionCount <= n ^ (M.timeBound + 1) :=
    B.directionCount_le_next_power hn2
  have hchoose_le_poly :
      Nat.choose (n / 3) (Nat.log 2 n) <= n ^ (M.timeBound + 1) :=
    le_trans B.binomial_le_directions hdir_le_poly
  have hgap :
      n ^ (M.timeBound + 1) <
        Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent (M.timeBound + 1) n hn20 hlog
  exact (Nat.not_lt_of_ge hchoose_le_poly) hgap

/-- Run-indexed EKP force implies the encoded no-decider endpoint.

This is the formal no-go diagnosis: if "decision equivalence forces EKP
directions" is interpreted as direct coverage by the classical run trace, then
the theorem is already P-vs-NP strength. -/
theorem no_DTMDecidesSATWithEncoding_of_runIndexedEKPForce
    (enc : ThreeCNFEncoding)
    (H : RunIndexedClassicalSATDeciderForcesEKPBoundary enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) := by
  intro hdec
  rcases hdec with ⟨M, hM⟩
  rcases H (M.timeBound + 1) with ⟨n, hn20, hlog, hforce⟩
  exact
    (no_runIndexedEKPBoundaryVisible_at_paperScale
      (enc := enc) (M := M) (n := n) hn20 hlog)
      (hforce M hM)

/-- Conversely, if no encoded SAT-deciding DTM exists, the run-indexed EKP
force statement holds vacuously. -/
theorem runIndexedEKPForce_of_no_DTMDecidesSATWithEncoding
    (enc : ThreeCNFEncoding)
    (hno : Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M)) :
    RunIndexedClassicalSATDeciderForcesEKPBoundary enc := by
  intro c
  let k : Nat := Nat.max 20 (4 * (c + 1))
  let n : Nat := 2 ^ k
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [n, k]
    exact Nat.pow_le_pow_right
      (by norm_num : 1 <= 2)
      (Nat.le_max_left 20 (4 * (c + 1)))
  · dsimp [n, k]
    have hpow :
        2 ^ (4 * (c + 1)) <= 2 ^ Nat.max 20 (4 * (c + 1)) :=
      Nat.pow_le_pow_right
        (by norm_num : 1 <= 2)
        (Nat.le_max_right 20 (4 * (c + 1)))
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  · intro M hM
    exact False.elim (hno ⟨M, hM⟩)

/-- Exact status of the run-indexed EKP semantic-force reading. -/
theorem runIndexedEKPForce_iff_no_DTMDecidesSATWithEncoding
    (enc : ThreeCNFEncoding) :
    RunIndexedClassicalSATDeciderForcesEKPBoundary enc ↔
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M) := by
  constructor
  · exact no_DTMDecidesSATWithEncoding_of_runIndexedEKPForce enc
  · exact runIndexedEKPForce_of_no_DTMDecidesSATWithEncoding enc

/-! ## The surviving non-local target -/

/-- A non-local EKP semantic surface.  Unlike the run-indexed version above,
this does not require directions to inject into actual DTM time indices.  This
is the only form that is not immediately capped by the polynomial run length.

The file does not assert that such coverage exists.  It isolates the genuinely
new theorem shape needed to turn the book's EKP intuition into a classical
P-vs-NP proof. -/
structure NonLocalEKPDirectionCoverage
    (enc : ThreeCNFEncoding) (M : TuringMachine.DTM) (n : Nat) : Type where
  directionCount : Nat
  direction_floor :
    Nat.choose (n / 3) (Nat.log 2 n) <= directionCount
  visible : Fin directionCount -> Prop
  all_visible : forall d : Fin directionCount, visible d

/-- The non-local EKP version of the missing force theorem.  This is the
actual surviving breakthrough target:

`DTMDecidesSATWithEncoding enc M` must produce non-local EKP directional
coverage, not merely a set of directions indexed by the polynomial run trace.
-/
def NonLocalClassicalSATDeciderForcesEKPBoundary
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        Nonempty (NonLocalEKPDirectionCoverage enc M n)

/-- To use non-local EKP coverage for the Theorem-207 route, one still needs a
bridge from EKP coverage to sheet essentiality.  This is the exact
non-natural/non-local semantic theorem that the paper/book would have to
supply. -/
structure NonLocalEKPToTheorem207Essentiality
    (enc : ThreeCNFEncoding) : Type where
  bridge :
    forall {M : TuringMachine.DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns),
      Nonempty (NonLocalEKPDirectionCoverage enc M n) ->
        exists Accepts :
          MvPolynomial
            (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
            Prop,
          Theorem207SheetEssentialForAcceptance Accepts S

/-! ## Non-local EKP bridge endpoint -/

/-- Non-local EKP coverage at a fixed scale, for every encoded SAT-deciding
DTM. -/
def NonLocalEKPBoundaryVisibleAt
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  forall M : TuringMachine.DTM,
    DTMDecidesSATWithEncoding enc M ->
      Nonempty (NonLocalEKPDirectionCoverage enc M n)

/-- Paper-scale non-local EKP coverage.  This is the strengthened form needed
to compose directly with the paper's Theorem-207 bounded-parameter surface. -/
def PaperScaleNonLocalClassicalSATDeciderForcesEKPBoundary
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 804 /\
    4 * (c + 1) <= Nat.log 2 n /\
    NonLocalEKPBoundaryVisibleAt enc n

/-- Non-local EKP coverage plus the essentiality bridge turns an instrumented
Theorem-207 sheet into the classical semantic-force package.

This is the exact place where the book/paper would need a non-natural,
non-local theorem: the output is not just an extractable static sheet, but a
sheet that is acceptance-essential for the classical computation. -/
theorem theorem207ClassicalSemanticForce_of_nonLocalEKP
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (B : NonLocalEKPToTheorem207Essentiality enc)
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (Hcov : Nonempty (NonLocalEKPDirectionCoverage enc M n)) :
    Nonempty (Theorem207ClassicalSemanticForce M n hn hn2 htb hns) := by
  rcases B.bridge S Hcov with ⟨Accepts, hEss⟩
  exact ⟨{
    instrumented := S
    Accepts := Accepts
    essential := hEss
  }⟩

/-- Paper-scale Theorem-207 semantic force for every encoded SAT decider and
every instrumented sheet satisfying the bounded-parameter side conditions. -/
def PaperScaleTheorem207ClassicalSemanticForce
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    exists hn : n >= 2 ^ 804,
    exists hn2 : n >= 2,
    4 * (c + 1) <= Nat.log 2 n /\
    forall (M : TuringMachine.DTM)
      (_hM : DTMDecidesSATWithEncoding enc M)
      (htb : M.timeBound <= 4)
      (hns : M.numStates <= n)
      (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns),
        exists F : Theorem207ClassicalSemanticForce M n hn hn2 htb hns,
          F.instrumented = S

/-- The non-local EKP package composes to the paper-scale classical semantic
force target. -/
theorem paperScaleTheorem207ClassicalSemanticForce_of_nonLocalEKP
    (enc : ThreeCNFEncoding)
    (Hcov : PaperScaleNonLocalClassicalSATDeciderForcesEKPBoundary enc)
    (B : NonLocalEKPToTheorem207Essentiality enc) :
    PaperScaleTheorem207ClassicalSemanticForce enc := by
  intro c
  rcases Hcov c with ⟨n, hn804, hlog, Hat⟩
  have hn2 : n >= 2 :=
    le_trans
      (by
        have hpow : 2 ^ 1 <= 2 ^ 804 :=
          Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by norm_num : 1 <= 804)
        simpa using hpow)
      hn804
  refine ⟨n, hn804, hn2, hlog, ?_⟩
  intro M hM htb hns S
  rcases B.bridge S (Hat M hM) with ⟨Accepts, hEss⟩
  exact ⟨{
    instrumented := S
    Accepts := Accepts
    essential := hEss
  }, rfl⟩

/-- A sheet is removable if no acceptance predicate can make it essential.
This formalizes the static-add-on failure mode: extractability alone does not
make a sheet semantically load-bearing. -/
def Theorem207SheetRemovable
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns) : Prop :=
  forall Accepts :
    MvPolynomial
      (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
      Prop,
    Not (Theorem207SheetEssentialForAcceptance Accepts S)

/-- Removable/static sheets refute the non-local EKP-to-essentiality bridge at
that sheet.  Thus the surviving theorem cannot merely produce directions; it
must prove genuine semantic essentiality of the extracted sheet. -/
theorem false_of_nonLocalEKPBridge_and_removableSheet
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (B : NonLocalEKPToTheorem207Essentiality enc)
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (Hcov : Nonempty (NonLocalEKPDirectionCoverage enc M n))
    (Hremovable : Theorem207SheetRemovable S) :
    False := by
  rcases B.bridge S Hcov with ⟨Accepts, hEss⟩
  exact Hremovable Accepts hEss

/-- Equivalent negated form of the removable-sheet guard. -/
theorem not_nonLocalEKPBridge_of_removableSheet_and_coverage
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (Hcov : Nonempty (NonLocalEKPDirectionCoverage enc M n))
    (Hremovable : Theorem207SheetRemovable S) :
    Not (Nonempty (NonLocalEKPToTheorem207Essentiality enc)) := by
  intro hB
  rcases hB with ⟨B⟩
  exact false_of_nonLocalEKPBridge_and_removableSheet
    B S Hcov Hremovable

/-! ## Kernel-only axiom trace -/

#print axioms RunIndexedEKPDirectionRealization.directionCount_le_timeWindow
#print axioms RunIndexedEKPBoundaryVisible.directionCount_le_next_power
#print axioms no_runIndexedEKPBoundaryVisible_at_paperScale
#print axioms no_DTMDecidesSATWithEncoding_of_runIndexedEKPForce
#print axioms runIndexedEKPForce_of_no_DTMDecidesSATWithEncoding
#print axioms runIndexedEKPForce_iff_no_DTMDecidesSATWithEncoding
#print axioms theorem207ClassicalSemanticForce_of_nonLocalEKP
#print axioms paperScaleTheorem207ClassicalSemanticForce_of_nonLocalEKP
#print axioms false_of_nonLocalEKPBridge_and_removableSheet
#print axioms not_nonLocalEKPBridge_of_removableSheet_and_coverage

end PallLean.Paper93.DeepMath.PathB
