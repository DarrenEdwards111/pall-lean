import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScannable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSeparatingInvariant

/-!
# Concrete MCSP: finite circuits, truth tables, and the honest frontier

This file replaces the proposition-only `MetaComplexityRoute` interface with an
actual minimum-circuit-size language.

* `Gate` is a finite Boolean basis with explicit wire references.
* `Circuit.Valid` enforces the DAG condition: every wire reference points
  strictly backwards.
* `assignments` enumerates all Boolean assignments and `Circuit.truthTable`
  evaluates a circuit on every one of them.
* `Instance` contains an arity, a unary size threshold, and the supplied truth
  table.
* `verifier` is an executable certificate checker.
* `mcsp_in_np_certificate` proves soundness, completeness, a polynomial
  gate-count witness bound, and an explicit polynomial verification-work bound.

The last section names the real frontier, `NoPolyMCSPDecider`, against the
repository's general clocked-machine `InP`.  It is a definition, not a theorem.
Nothing in this file proves it.

## Scope

`mcsp_in_np_certificate` is the concrete verifier-level NP theorem.  A fully
machine-internal `InNP mcspLang` theorem additionally requires compiling this
structural verifier to the repository's chosen local finite-control machine
model with a polynomial simulation theorem.  We do not use the older shortcut
of hiding the complete verification computation inside one arbitrary machine
transition.
-/

namespace PallLean.Paper93.DeepMath.PathB.ConcreteMCSP

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant

/-! ## A concrete finite-basis circuit model -/

/-- A fixed complete Boolean basis.  Natural-number wire references are checked
by `Circuit.Valid` and must point to earlier gates. -/
inductive Gate (n : ℕ) where
  | input : Fin n → Gate n
  | cst : Bool → Gate n
  | neg : ℕ → Gate n
  | conj : ℕ → ℕ → Gate n
  | disj : ℕ → ℕ → Gate n
  | xor : ℕ → ℕ → Gate n
deriving DecidableEq

/-- A circuit is a straight-line list of gates. -/
structure Circuit (n : ℕ) where
  gates : List (Gate n)
deriving DecidableEq

/-- Boolean well-formedness check at position `i`: every referenced wire must
have been produced strictly earlier. -/
def Gate.validAt (i : ℕ) : Gate n → Bool
  | .input _ | .cst _ => true
  | .neg j => decide (j < i)
  | .conj j k | .disj j k | .xor j k => decide (j < i ∧ k < i)

/-- Scan the gate list while tracking its current position. -/
def Circuit.validFrom (i : ℕ) : List (Gate n) → Bool
  | [] => true
  | g :: gs => g.validAt i && validFrom (i + 1) gs

/-- Executable standard acyclic straight-line-program check. -/
def Circuit.valid (c : Circuit n) : Bool := Circuit.validFrom 0 c.gates

/-- Evaluate one gate against the values already produced. -/
def Gate.eval (x : Fin n → Bool) (values : List Bool) : Gate n → Bool
  | .input i => x i
  | .cst b => b
  | .neg j => !(values.getD j false)
  | .conj j k => (values.getD j false) && (values.getD k false)
  | .disj j k => (values.getD j false) || (values.getD k false)
  | .xor j k => Bool.xor (values.getD j false) (values.getD k false)

/-- Evaluate all gates from left to right. -/
def Circuit.run (c : Circuit n) (x : Fin n → Bool) : List Bool :=
  c.gates.foldl (fun values g => values ++ [g.eval x values]) []

/-- The final wire is the circuit output; the empty circuit outputs `false`. -/
def Circuit.output (c : Circuit n) (x : Fin n → Bool) : Bool :=
  (c.run x).getD (c.gates.length - 1) false

/-! ## Explicit truth-table order -/

/-- Prefix one Boolean coordinate to an assignment. -/
def prefixAssignment (b : Bool) (x : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.cases b x

/-- A deterministic enumeration of all `2^n` Boolean assignments. -/
def assignments : (n : ℕ) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n + 1 =>
      (assignments n).flatMap fun x =>
        [prefixAssignment false x, prefixAssignment true x]

@[simp] theorem assignments_length (n : ℕ) : (assignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [assignments, ih, pow_succ]

/-- The full truth table in the fixed `assignments` order. -/
def Circuit.truthTable (c : Circuit n) : List Bool :=
  (assignments n).map c.output

@[simp] theorem Circuit.truthTable_length (c : Circuit n) :
    c.truthTable.length = 2 ^ n := by
  simp [Circuit.truthTable]

/-! ## MCSP instances and executable certificate verification -/

/-- A concrete MCSP instance.  The threshold is encoded in unary below; the
truth table must contain exactly `2^n` bits. -/
structure Instance where
  n : ℕ
  threshold : ℕ
  table : List Bool
deriving DecidableEq

/-- Syntactic well-formedness of the supplied truth table. -/
def Instance.WellFormed (I : Instance) : Prop := I.table.length = 2 ^ I.n

instance (I : Instance) : Decidable I.WellFormed := by
  unfold Instance.WellFormed
  infer_instance

/-- A circuit certificate is accepted exactly when it is small, acyclic, and
has the supplied full truth table. -/
def Verifies (I : Instance) (c : Circuit I.n) : Prop :=
  I.WellFormed ∧ c.gates.length ≤ I.threshold ∧ c.valid = true ∧ c.truthTable = I.table

instance (I : Instance) (c : Circuit I.n) : Decidable (Verifies I c) := by
  unfold Verifies
  infer_instance

/-- Executable Boolean certificate checker. -/
def verifier (I : Instance) (c : Circuit I.n) : Bool :=
  decide (Verifies I c)

@[simp] theorem verifier_eq_true_iff (I : Instance) (c : Circuit I.n) :
    verifier I c = true ↔ Verifies I c := by
  simp [verifier]

/-- The concrete YES predicate for MCSP. -/
def MCSPYes (I : Instance) : Prop := ∃ c : Circuit I.n, Verifies I c

/-- Unary encoding: arity, threshold, then the raw truth table. -/
def Instance.encode (I : Instance) : List Bool :=
  encodeNatBits I.n ++ encodeNatBits I.threshold ++ I.table

/-- Total decoder; malformed words decode to an instance which normally fails
`WellFormed`. -/
def Instance.decode (w : List Bool) : Instance :=
  let r₁ := decodeNatBits w
  let r₂ := decodeNatBits r₁.2
  ⟨r₁.1, r₂.1, r₂.2⟩

@[simp] theorem Instance.decode_encode (I : Instance) :
    Instance.decode (Instance.encode I) = I := by
  simp [Instance.decode, Instance.encode, decodeNatBits_encodeNatBits]

/-- Mathematical Boolean language on encoded words.  Classical choice is used
only to turn the existential language predicate into a Boolean; the verifier
itself above is executable. -/
noncomputable def mcspLang (w : List Bool) : Bool := by
  classical
  exact if MCSPYes (Instance.decode w) then true else false

theorem mcspLang_encode_iff (I : Instance) :
    mcspLang I.encode = true ↔ MCSPYes I := by
  simp [mcspLang]

/-! ## Explicit polynomial certificate accounting -/

/-- The structured input size for the unary-threshold representation. -/
def Instance.inputSize (I : Instance) : ℕ :=
  I.table.length + I.threshold + I.n + 2

/-- Conservative work accounting for verification.  There are `table.length`
assignments; the square covers list-based wire lookup and accumulation. -/
def verifierWork (I : Instance) (c : Circuit I.n) : ℕ :=
  I.table.length * (c.gates.length + 1) ^ 2 + (c.gates.length + 1)

theorem gate_count_le_inputSize {I : Instance} {c : Circuit I.n}
    (hsmall : c.gates.length ≤ I.threshold) :
    c.gates.length + 1 ≤ I.inputSize := by
  unfold Instance.inputSize
  omega

/-- The explicit verifier work is polynomial in the encoded structured input
size whenever the certificate obeys the MCSP threshold. -/
theorem verifierWork_poly {I : Instance} {c : Circuit I.n}
    (hsmall : c.gates.length ≤ I.threshold) :
    verifierWork I c ≤ I.inputSize ^ 3 + I.inputSize := by
  have htable : I.table.length ≤ I.inputSize := by
    unfold Instance.inputSize
    omega
  have hgate : c.gates.length + 1 ≤ I.inputSize :=
    gate_count_le_inputSize hsmall
  have hsquare : (c.gates.length + 1) ^ 2 ≤ I.inputSize ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hgate hgate
  calc
    verifierWork I c
        ≤ I.inputSize * I.inputSize ^ 2 + I.inputSize :=
          Nat.add_le_add (Nat.mul_le_mul htable hsquare) hgate
    _ = I.inputSize ^ 3 + I.inputSize := by ring

/-- **Concrete verifier-level `MCSP ∈ NP`.**  An instance is YES iff it has a
certificate accepted by the executable verifier; every such certificate has
polynomial gate count and the verifier has the displayed polynomial work
bound. -/
theorem mcsp_in_np_certificate (I : Instance) :
    MCSPYes I ↔
      ∃ c : Circuit I.n,
        verifier I c = true ∧
        c.gates.length + 1 ≤ I.inputSize ∧
        verifierWork I c ≤ I.inputSize ^ 3 + I.inputSize := by
  constructor
  · rintro ⟨c, hc⟩
    have hsmall : c.gates.length ≤ I.threshold := hc.2.1
    exact ⟨c, (verifier_eq_true_iff I c).2 hc,
      gate_count_le_inputSize hsmall, verifierWork_poly hsmall⟩
  · rintro ⟨c, hc, -, -⟩
    exact ⟨c, (verifier_eq_true_iff I c).1 hc⟩

/-! ## The one honest frontier -/

/-- **OPEN.**  No polynomial-time clocked machine decides concrete MCSP.
Proving this proposition, after completing the verifier-to-machine NP
compilation, yields `P ≠ NP`. -/
def NoPolyMCSPDecider : Prop := ¬ InP mcspLang

/-- The frontier unfolded: every alleged polynomial-time decider must fail
somewhere.  This theorem only exposes the quantifiers; it does not prove them. -/
theorem noPolyMCSPDecider_iff :
    NoPolyMCSPDecider ↔
      ∀ M : ClockedMachine, IsPolyTime M → ¬ Decides M mcspLang := by
  constructor
  · intro h M hpoly hdec
    exact h ⟨M, hpoly, hdec⟩
  · intro h ⟨M, hpoly, hdec⟩
    exact h M hpoly hdec

/-- Once a faithful machine-level `InNP` compilation of the concrete verifier
is supplied, the frontier is exactly sufficient for `P ≠ NP`. -/
theorem pneqNP_of_concreteMCSP
    (hNP : InNP mcspLang) (hfrontier : NoPolyMCSPDecider) :
    ¬ PeqNP :=
  PneqNP_of_no_InP mcspLang hNP hfrontier

end PallLean.Paper93.DeepMath.PathB.ConcreteMCSP

#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteMCSP.mcsp_in_np_certificate
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteMCSP.noPolyMCSPDecider_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteMCSP.pneqNP_of_concreteMCSP
