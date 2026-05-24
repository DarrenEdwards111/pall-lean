import PallLean.Paper93.DeepMath.PathB.DynamicCEW
import PallLean.GodMoveCore
import PallLean.PaperFaithfulCompilation
import PallLean.Paper93.DeepMath.PathB.AmplituhedronBarrier

/-!
# Observer-first God-Move bridge to dynamic CEW

This module is the honest observer-first pivot.

The starting object is an observer machine with a dynamic width function.  The
God-Move / holographic / amplituhedron machinery is allowed to enter only as a
certificate extracted from every SAT-deciding observer trajectory.  If such a
universal extraction exists at all polynomial exponents, the dynamic CEW
SAT lower bound follows mechanically.

The file does not construct that universal extraction.  It isolates the exact
theorem that would have to be proved.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Observer machine, deliberately dynamic: the primitive datum is its live
width along computation trajectories, summarized by input length.

The acceptance semantics are over actual binary inputs.  SAT semantics are
added below by choosing an encoding relation from bit strings to `ThreeCNF`
formulas and requiring acceptance exactly on satisfiable encoded formulas. -/
structure ObserverMachine where
  width : DynamicCEW.ObserverWidth
  acceptsInput : (n : Nat) -> (Fin n -> Bool) -> Prop

/-! ## Concrete SAT semantics for observers -/

/-- A relation saying that a binary input encodes a 3-CNF formula.

This is kept as data rather than hard-wiring a particular parser.  The bridge
only needs the two semantic properties listed here: encoded formulas fit in the
input length, and every formula can be padded/encoded at any sufficiently large
length. -/
structure ThreeCNFEncoding where
  Encodes : {n : Nat} -> (Fin n -> Bool) -> ThreeCNF -> Prop
  encoding_fits :
    forall {n : Nat} {input : Fin n -> Bool} {φ : ThreeCNF},
      Encodes input φ -> φ.encodingSize <= n
  complete :
    forall (φ : ThreeCNF) (n : Nat),
      φ.encodingSize <= n -> exists input : Fin n -> Bool, Encodes input φ

/-- Deterministic encodings assign at most one formula to each bit string. -/
def ThreeCNFEncoding.Functional (enc : ThreeCNFEncoding) : Prop :=
  forall {n : Nat} (input : Fin n -> Bool) (φ ψ : ThreeCNF),
    enc.Encodes input φ -> enc.Encodes input ψ -> φ = ψ

/-- Extensional SAT correctness for an observer under a chosen encoding. -/
def ObserverDecidesSAT (enc : ThreeCNFEncoding) (O : ObserverMachine) : Prop :=
  forall {n : Nat} (hn : n >= 1) (input : Fin n -> Bool) (φ : ThreeCNF),
    enc.Encodes input φ -> (O.acceptsInput n input <-> φ.IsSatisfiable)

/-- If an observer decides SAT, it accepts every encoded satisfiable formula. -/
theorem ObserverDecidesSAT.accepts_of_satisfiable
    {enc : ThreeCNFEncoding} {O : ObserverMachine}
    (hdec : ObserverDecidesSAT enc O)
    {n : Nat} (hn : n >= 1) {input : Fin n -> Bool} {φ : ThreeCNF}
    (henc : enc.Encodes input φ) (hsat : φ.IsSatisfiable) :
    O.acceptsInput n input :=
  (hdec hn input φ henc).mpr hsat

/-- If an observer decides SAT, it rejects every encoded unsatisfiable formula. -/
theorem ObserverDecidesSAT.rejects_of_unsatisfiable
    {enc : ThreeCNFEncoding} {O : ObserverMachine}
    (hdec : ObserverDecidesSAT enc O)
    {n : Nat} (hn : n >= 1) {input : Fin n -> Bool} {φ : ThreeCNF}
    (henc : enc.Encodes input φ) (hunsat : Not φ.IsSatisfiable) :
    Not (O.acceptsInput n input) := by
  intro hacc
  exact hunsat ((hdec hn input φ henc).mp hacc)

/-- DTM SAT semantics under the same encoding relation.  This is the
operational version: acceptance must be realized by an actual DTM run. -/
def DTMDecidesSATWithEncoding (enc : ThreeCNFEncoding)
    (M : TuringMachine.DTM) : Prop :=
  forall {n : Nat} (hn : n >= 1) (input : Fin n -> Bool) (φ : ThreeCNF),
    enc.Encodes input φ ->
      (TuringMachine.accepts M n hn input <-> φ.IsSatisfiable)

/-- An observer is operationally SAT-correct when its input acceptance is
realized by a DTM that decides SAT under the encoding. -/
def OperationalObserverDecidesSAT
    (enc : ThreeCNFEncoding) (O : ObserverMachine) : Prop :=
  exists M : TuringMachine.DTM,
    DTMDecidesSATWithEncoding enc M /\
    forall {n : Nat} (hn : n >= 1) (input : Fin n -> Bool),
      O.acceptsInput n input <-> TuringMachine.accepts M n hn input

/-- Operational SAT correctness implies extensional SAT correctness. -/
theorem ObserverDecidesSAT_of_operational
    {enc : ThreeCNFEncoding} {O : ObserverMachine}
    (hop : OperationalObserverDecidesSAT enc O) :
    ObserverDecidesSAT enc O := by
  rcases hop with ⟨M, hMdec, hrealizes⟩
  intro n hn input φ henc
  exact Iff.trans (hrealizes hn input) (hMdec hn input φ henc)

/-- Noncomputable extensional SAT oracle for a functional encoding.

This object is useful as a warning: extensional SAT semantics alone do not
model a procedure.  It accepts an input iff the encoded formula is satisfiable. -/
noncomputable def semanticSATOracleObserver
    (enc : ThreeCNFEncoding) : ObserverMachine where
  width := fun _ => 0
  acceptsInput := fun n input =>
    exists φ : ThreeCNF, enc.Encodes input φ /\ φ.IsSatisfiable

/-- The noncomputable oracle satisfies the extensional SAT specification for
functional encodings, despite having zero dynamic width. -/
theorem semanticSATOracleObserver_decidesSAT
    (enc : ThreeCNFEncoding) (hfunc : enc.Functional) :
    ObserverDecidesSAT enc (semanticSATOracleObserver enc) := by
  intro n hn input φ henc
  constructor
  · intro hacc
    rcases hacc with ⟨ψ, hψenc, hψsat⟩
    have hψeq : ψ = φ := (hfunc input ψ φ hψenc henc)
    simpa [hψeq] using hψsat
  · intro hsat
    exact ⟨φ, henc, hsat⟩

/-- The width functions coming from observers satisfying a semantic decider
predicate. -/
def ObserverWidths (Decides : ObserverMachine -> Prop) :
    DynamicCEW.ObserverWidth -> Prop :=
  fun w => exists O : ObserverMachine, Decides O /\ O.width = w

/-- A single observer has polynomial width with exponent `c`. -/
def ObserverHasPolyWidthExponent (O : ObserverMachine) (c : Nat) : Prop :=
  forall n : Nat, O.width n <= n ^ c

/-- A semantic observer class contains a SAT-deciding observer of exponent `c`. -/
def ObserverSATPolyWidthAtMost
    (SATDecider : ObserverMachine -> Prop) (c : Nat) : Prop :=
  exists O : ObserverMachine, SATDecider O /\ ObserverHasPolyWidthExponent O c

/-- A live boundary minor extracted from an observer trajectory.

The fields `phase_holographic_payload` and `godmove_amplituhedron_payload`
are intentionally abstract: they are the place where the phase / holographic /
amplituhedron construction must land.  The rank fields are the only data the
DCEW lower-bound argument consumes. -/
structure GodMoveHolographicBoundaryMinor
    (O : ObserverMachine) (n : Nat) where
  time : Nat
  liveRank : Nat
  phase_holographic_payload : Prop
  phase_payload_realized : phase_holographic_payload
  godmove_amplituhedron_payload : Prop
  godmove_payload_realized : godmove_amplituhedron_payload
  rank_lower :
    Nat.choose (n / 3) (Nat.log 2 n) <= liveRank
  rank_le_width : liveRank <= O.width n

/-- Fixed-length universal extraction from every SAT observer.  This is the
non-static version of the target: the minor is extracted from the observer's
trajectory, not from a preselected global polynomial object. -/
def SATObserverGodMoveExtractionAt
    (SATDecider : ObserverMachine -> Prop) (n : Nat) : Prop :=
  forall O : ObserverMachine, SATDecider O ->
    Nonempty (GodMoveHolographicBoundaryMinor O n)

/-- Exponent-parametric universal extraction.  This is the real theorem needed
for the full `NP_side_lower_bound`: for each polynomial exponent, there is a
length at which every SAT observer exposes a live God-Move boundary minor above
that polynomial scale. -/
def UniversalSATObserverGodMoveExtraction
    (SATDecider : ObserverMachine -> Prop) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    SATObserverGodMoveExtractionAt SATDecider n

/-- The amplituhedron/God-Move engine plugged into the observer-first lower
bound.  The field is deliberately the observer-extraction theorem itself:
matrix positivity, phase, holography, and God-Move geometry only help once
they produce these trajectory-level boundary minors for every SAT observer. -/
structure AmplituhedronGodMoveObserverEngine
    (SATDecider : ObserverMachine -> Prop) : Prop where
  observer_extraction : UniversalSATObserverGodMoveExtraction SATDecider

/-- Width predicates for extensionally SAT-correct observers. -/
def SemanticSATObserverWidths (enc : ThreeCNFEncoding) :
    DynamicCEW.ObserverWidth -> Prop :=
  ObserverWidths (ObserverDecidesSAT enc)

/-- Width predicates for operationally SAT-correct observers.  This is the
version that rules out noncomputable oracle observers by requiring a backing
DTM execution semantics. -/
def OperationalSATObserverWidths (enc : ThreeCNFEncoding) :
    DynamicCEW.ObserverWidth -> Prop :=
  ObserverWidths (OperationalObserverDecidesSAT enc)

/-- Universal extraction target for the operational SAT semantics. -/
def UniversalOperationalSATObserverGodMoveExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  UniversalSATObserverGodMoveExtraction (OperationalObserverDecidesSAT enc)

/-- A live holographic minor forces the observer width at that length. -/
theorem observer_width_lower_of_godMove_holographic_minor
    {O : ObserverMachine} {n : Nat}
    (minor : GodMoveHolographicBoundaryMinor O n) :
    Nat.choose (n / 3) (Nat.log 2 n) <= O.width n :=
  le_trans minor.rank_lower minor.rank_le_width

/-- Exponent-parametric arithmetic gap used by the observer-width argument. -/
theorem arithmetic_gap_for_exponent
    (c n : Nat)
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (c + 1) <= Nat.log 2 n) :
    n ^ c < Nat.choose (n / 3) (Nat.log 2 n) := by
  have hbin :
      n ^ (Nat.log 2 n / 4) <= Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono :
      Nat.choose (n / 30) (Nat.log 2 n) <=
        Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 <= n / 3)
  have hdiv : c + 1 <= Nat.log 2 n / 4 := by
    omega
  have hn_gt_one : 1 < n := by
    omega
  have hn_ge_one : 1 <= n := by
    omega
  have hstep : n ^ c < n ^ (c + 1) :=
    Nat.pow_lt_pow_right hn_gt_one (by omega : c < c + 1)
  have hpow : n ^ (c + 1) <= n ^ (Nat.log 2 n / 4) :=
    Nat.pow_le_pow_right hn_ge_one hdiv
  exact lt_of_lt_of_le hstep (le_trans hpow (le_trans hbin hmono))

/-- At a fixed length, universal observer extraction rules out DCEW at the
corresponding polynomial bound. -/
theorem not_DCEWatMost_at_exponent_of_extractionAt
    (SATDecider : ObserverMachine -> Prop)
    (c n : Nat)
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (c + 1) <= Nat.log 2 n)
    (hextract : SATObserverGodMoveExtractionAt SATDecider n) :
    Not (DynamicCEW.DCEWatMost (ObserverWidths SATDecider) n (n ^ c)) := by
  intro hcew
  rcases hcew with ⟨w, hw_decides, hw_bound⟩
  rcases hw_decides with ⟨O, hsat, hwidth_eq⟩
  rcases hextract O hsat with ⟨minor⟩
  have hminor_width :
      Nat.choose (n / 3) (Nat.log 2 n) <= O.width n :=
    observer_width_lower_of_godMove_holographic_minor minor
  have hminor_w :
      Nat.choose (n / 3) (Nat.log 2 n) <= w n := by
    simpa [hwidth_eq] using hminor_width
  have hupper :
      Nat.choose (n / 3) (Nat.log 2 n) <= n ^ c :=
    le_trans hminor_w hw_bound
  exact (not_le_of_gt (arithmetic_gap_for_exponent c n hn20 hlog)) hupper

/-- The universal observer-GodMove extraction theorem would prove the SAT
dynamic CEW lower bound. -/
theorem NP_side_lower_bound_of_universalObserverGodMoveExtraction
    (SATDecider : ObserverMachine -> Prop)
    (hextract : UniversalSATObserverGodMoveExtraction SATDecider) :
    DynamicCEW.NP_side_lower_bound (ObserverWidths SATDecider) := by
  intro c
  rcases hextract c with ⟨n, hn20, hlog, hextract_at⟩
  exact ⟨n,
    not_DCEWatMost_at_exponent_of_extractionAt
      SATDecider c n hn20 hlog hextract_at⟩

/-- The amplituhedron/God-Move observer engine is enough only because it
contains the universal observer-extraction theorem as a field. -/
theorem NP_side_lower_bound_of_amplituhedronGodMoveObserverEngine
    (SATDecider : ObserverMachine -> Prop)
    (engine : AmplituhedronGodMoveObserverEngine SATDecider) :
    DynamicCEW.NP_side_lower_bound (ObserverWidths SATDecider) :=
  NP_side_lower_bound_of_universalObserverGodMoveExtraction
    SATDecider engine.observer_extraction

/-- Operational SAT version of the lower-bound bridge.  This is the semantic
target to prove: every DTM-backed SAT observer must expose the high-rank live
boundary minor. -/
theorem NP_side_lower_bound_of_universalOperationalSATObserverGodMoveExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalOperationalSATObserverGodMoveExtraction enc) :
    DynamicCEW.NP_side_lower_bound (OperationalSATObserverWidths enc) :=
  by
    simpa [OperationalSATObserverWidths,
      UniversalOperationalSATObserverGodMoveExtraction] using
      (NP_side_lower_bound_of_universalObserverGodMoveExtraction
        (OperationalObserverDecidesSAT enc) hextract)

/-- With the usual P-side observer calibration, the observer engine gives the
formal DCEW separation criterion. -/
theorem WouldYieldSeparation_of_observerCalibration_and_engine
    (PDecider SATDecider : ObserverMachine -> Prop)
    (hp : DynamicCEW.P_side_bound (ObserverWidths PDecider))
    (engine : AmplituhedronGodMoveObserverEngine SATDecider) :
    DynamicCEW.WouldYieldSeparation
      (ObserverWidths PDecider) (ObserverWidths SATDecider) :=
  ⟨hp, NP_side_lower_bound_of_amplituhedronGodMoveObserverEngine
    SATDecider engine⟩

/-- Paper-scale fixed-exponent version: at `n >= 2^804`, the same argument
recovers the historical `n^200` obstruction. -/
theorem not_DCEWatMost_at_paperScale_200_of_extractionAt
    (SATDecider : ObserverMachine -> Prop)
    (n : Nat)
    (hn804 : n >= 2 ^ 804)
    (hextract : SATObserverGodMoveExtractionAt SATDecider n) :
    Not (DynamicCEW.DCEWatMost (ObserverWidths SATDecider) n (n ^ 200)) := by
  have hn20 : n >= 2 ^ 20 := by
    exact le_trans
      (Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by omega : 20 <= 804))
      hn804
  have hlog : 4 * (200 + 1) <= Nat.log 2 n := by
    have hlog804 : 804 <= Nat.log 2 n :=
      Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn804
    omega
  exact not_DCEWatMost_at_exponent_of_extractionAt
    SATDecider 200 n hn20 hlog hextract

/-- A zero-width observer cannot expose a positive-rank boundary minor.  This
is the basic sanity check showing that the universal extraction theorem needs
real SAT-decider semantics; it is not provable for an arbitrary observer class. -/
theorem not_extractionAt_of_zero_width_observer
    (SATDecider : ObserverMachine -> Prop)
    (O : ObserverMachine) (n : Nat)
    (hsat : SATDecider O)
    (hzero : O.width n = 0)
    (hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (SATObserverGodMoveExtractionAt SATDecider n) := by
  intro hextract
  rcases hextract O hsat with ⟨minor⟩
  have hminor_width :
      Nat.choose (n / 3) (Nat.log 2 n) <= O.width n :=
    observer_width_lower_of_godMove_holographic_minor minor
  have hminor_zero :
      Nat.choose (n / 3) (Nat.log 2 n) <= 0 := by
    simpa [hzero] using hminor_width
  exact (not_le_of_gt hchoose_pos) hminor_zero

/-- Consequently, any observer class that contains a zero-width SAT observer
refutes the universal extraction predicate.  This does not model real SAT; it
shows why the actual proof must use the semantic content of SAT decision. -/
theorem not_universalSATObserverGodMoveExtraction_of_zeroWidthSATObserver
    (SATDecider : ObserverMachine -> Prop)
    (O : ObserverMachine)
    (hsat : SATDecider O)
    (hzero : forall n : Nat, O.width n = 0) :
    Not (UniversalSATObserverGodMoveExtraction SATDecider) := by
  intro hextract
  rcases hextract 0 with ⟨n, hn20, hlog, hextract_at⟩
  have hgap : n ^ 0 < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent 0 n hn20 hlog
  have hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n) := by
    have hn0_pos : 0 < n ^ 0 := by simp
    exact lt_trans hn0_pos hgap
  exact not_extractionAt_of_zero_width_observer
    SATDecider O n hsat (hzero n) hchoose_pos hextract_at

/-- The abstract predicate cannot be proved for arbitrary `SATDecider`
predicates: the trivial predicate contains a zero-width observer. -/
theorem not_universalSATObserverGodMoveExtraction_for_trivial_decider :
    Not (UniversalSATObserverGodMoveExtraction (fun _ : ObserverMachine => True)) := by
  let O : ObserverMachine := {
    width := fun _ => 0
    acceptsInput := fun _ _ => False
  }
  exact not_universalSATObserverGodMoveExtraction_of_zeroWidthSATObserver
    (fun _ : ObserverMachine => True) O trivial (by intro n; rfl)

/-- Extensional SAT semantics alone still do not rule out a zero-width oracle:
for a functional encoding, `semanticSATOracleObserver` is extensionally correct
and has width zero.  Therefore the universal extraction theorem must target the
operational predicate, not merely `ObserverDecidesSAT`. -/
theorem not_universalSATObserverGodMoveExtraction_for_extensionalSATSemantics
    (enc : ThreeCNFEncoding) (hfunc : enc.Functional) :
    Not (UniversalSATObserverGodMoveExtraction (ObserverDecidesSAT enc)) := by
  exact not_universalSATObserverGodMoveExtraction_of_zeroWidthSATObserver
    (ObserverDecidesSAT enc)
    (semanticSATOracleObserver enc)
    (semanticSATOracleObserver_decidesSAT enc hfunc)
    (by intro n; rfl)

#print axioms NP_side_lower_bound_of_universalObserverGodMoveExtraction
#print axioms NP_side_lower_bound_of_universalOperationalSATObserverGodMoveExtraction
#print axioms WouldYieldSeparation_of_observerCalibration_and_engine
#print axioms not_universalSATObserverGodMoveExtraction_for_trivial_decider
#print axioms not_universalSATObserverGodMoveExtraction_for_extensionalSATSemantics

end PallLean.Paper93.DeepMath.PathB
