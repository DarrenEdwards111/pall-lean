import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalCNFAggregator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinInP

/-!
# Charged local SAT verifier: literal-lookup weld

The charged CNF aggregator consumes a nested stream of literal truth values.
This file connects that stream exactly to the semantic SAT verifier and to the
repository's concrete indexed-assignment machine.

For each literal, a canonical `masterM` input is constructed whose locally
computed output is precisely that literal's truth value.  At formula level,
we define the unique evaluated stream required by the aggregator and prove
that aggregating it is exactly the paired SAT verifier language.

The remaining operational obligation is thereby reduced from an unspecified
"SAT verifier machine" to one concrete transducer: locally parse the paired
formula/certificate input and emit this evaluated stream.  Polynomial
computability of that transducer immediately discharges
`LocalSATVerifierInP` by the already-proved reduction closure.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalCNFAggregator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier

/-! ## Exact semantic stream supplied to the aggregator -/

/-- Evaluate every literal of a decoded formula under a false-padded
certificate. -/
def evaluatedFormula (w : List Bool) (F : Formula) : List (List Bool) :=
  F.map fun c => c.map (evalLit fun v => w.getD v false)

theorem evaluatedClause_any (w : List Bool) (c : Clause) :
    (c.map (evalLit fun v => w.getD v false)).any id =
      evalClause (fun v => w.getD v false) c := by
  simp [evalClause]

theorem evaluatedFormula_all_any (w : List Bool) (F : Formula) :
    (evaluatedFormula w F).all (fun c => c.any id) =
      evalFormula (fun v => w.getD v false) F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
      rw [show evaluatedFormula w (c :: F) =
          (c.map (evalLit fun v => w.getD v false)) :: evaluatedFormula w F by rfl,
        List.all_cons, evaluatedClause_any, ih]
      rfl

/-- The canonical truth-value stream obtained from a paired verifier input. -/
def evaluatedVerifierStream (z : List Bool) : List Bool :=
  let xw := unpackWitness z
  encodeFormulaValues (evaluatedFormula xw.2 (decodeFormula xw.1))

/-- The evaluated stream is exactly a many-one semantic reduction from the
paired SAT verifier to the charged CNF aggregator language. -/
theorem verifierLanguage_eq_cnfAggregateLanguage (z : List Bool) :
    verifierLanguage satWitnessVerifier z =
      cnfAggregateLanguage (evaluatedVerifierStream z) := by
  change verifierLanguage satWitnessVerifier z =
    cnfAggregateLanguage (encodeFormulaValues
      (evaluatedFormula (unpackWitness z).2 (decodeFormula (unpackWitness z).1)))
  rw [cnfAggregateLanguage_encode]
  simp only [verifierLanguage, satWitnessVerifier]
  exact (evaluatedFormula_all_any (unpackWitness z).2
    (decodeFormula (unpackWitness z).1)).symm

/-! ## Each literal value is already locally computable -/

/-- A length-`v+1` assignment whose entry `j` says whether certificate bit
`j` matches the literal's satisfying polarity. -/
def signedLookupAssignment (w : List Bool) (v : Nat) (sign : Bool) : List Bool :=
  (List.range (v + 1)).map fun j => w.getD j false == sign

theorem signedLookupAssignment_length (w : List Bool) (v : Nat) (sign : Bool) :
    (signedLookupAssignment w v sign).length = v + 1 := by
  simp [signedLookupAssignment]

theorem signedLookupAssignment_getD (w : List Bool) (v : Nat) (sign : Bool) :
    (signedLookupAssignment w v sign).getD v false =
      evalLit (fun j => w.getD j false) (v, sign) := by
  unfold signedLookupAssignment evalLit
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (Nat.lt_succ_self v)]
  rfl

/-- Canonical input for the proved local indexed-assignment lookup machine. -/
def literalLookupTape (w : List Bool) (l : Lit) : List Bool :=
  encode (signedLookupAssignment w l.1 l.2) l.1

/-- The repository's concrete finite-control `masterM` computes every literal
truth value exactly.  Its clock is quadratic in the unary address/data size. -/
theorem masterM_reads_literal (w : List Bool) (l : Lit) :
    HaltsBy masterM (literalLookupTape w l)
        (2 * (l.1 + 1) + 2 + 1 +
          (clockSum l.1 (signedLookupAssignment w l.1 l.2).length + 7))
    ∧ decideOut masterM (literalLookupTape w l)
        (2 * (l.1 + 1) + 2 + 1 +
          (clockSum l.1 (signedLookupAssignment w l.1 l.2).length + 7)) =
        evalLit (fun j => w.getD j false) l := by
  obtain ⟨v, sign⟩ := l
  have hv : v < (signedLookupAssignment w v sign).length := by
    rw [signedLookupAssignment_length]
    omega
  have h := readAv_encoded (signedLookupAssignment w v sign) v hv
  change HaltsBy masterM
      (encode (signedLookupAssignment w v sign) v)
        (2 * (v + 1) + 2 + 1 +
          (clockSum v (signedLookupAssignment w v sign).length + 7))
    ∧ decideOut masterM (encode (signedLookupAssignment w v sign) v)
        (2 * (v + 1) + 2 + 1 +
          (clockSum v (signedLookupAssignment w v sign).length + 7)) =
        evalLit (fun j => w.getD j false) (v, sign)
  rw [← signedLookupAssignment_getD]
  exact h

theorem masterM_literal_clock_quadratic (w : List Bool) (l : Lit) :
    2 * (l.1 + 1) + 2 + 1 +
        (clockSum l.1 (signedLookupAssignment w l.1 l.2).length + 7)
      ≤ 32 * (l.1 + 2) * (l.1 + 2) + 2 * (l.1 + 1) + 12 := by
  rw [signedLookupAssignment_length]
  exact readAv_clock_poly l.1 (l.1 + 1) (by omega)

/-! ## Exact remaining transducer theorem -/

/-- The concrete operational seam: locally emit the evaluated truth-value
stream from a paired formula/certificate input. -/
def EvaluatedVerifierStreamPolyComputable : Prop :=
  PolyComputable evaluatedVerifierStream

/-- Once that one transducer is built, the charged local SAT verifier is in
the repaired local polynomial-time class. -/
theorem localSATVerifierInP_of_evaluatedStream
    (hstream : EvaluatedVerifierStreamPolyComputable) :
    LocalSATVerifierInP := by
  apply reductionClosure
    (L' := cnfAggregateLanguage)
    (hL' := cnfAggregateLanguage_inP)
  exact ⟨evaluatedVerifierStream, hstream,
    verifierLanguage_eq_cnfAggregateLanguage⟩

/-- Consequently, the stream transducer plus the charged SAT clock lower
bound yields the repaired local NP/P separation. -/
theorem local_NP_not_subset_P_of_stream_and_SAT_lower
    (hstream : EvaluatedVerifierStreamPolyComputable)
    (hlower : LocalSATSuperpolynomialClockLowerBound) :
    ¬ LocalNPCollapse :=
  local_NP_not_subset_P_of_SAT_clock_lower_bound
    (localSATVerifierInP_of_evaluatedStream hstream) hlower

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld.evaluatedFormula_all_any
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld.verifierLanguage_eq_cnfAggregateLanguage
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld.masterM_reads_literal
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld.masterM_literal_clock_quadratic
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld.localSATVerifierInP_of_evaluatedStream
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld.local_NP_not_subset_P_of_stream_and_SAT_lower
