import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteMCSP

/-!
# Concrete MCSP: appended-witness codec and exact verifier alignment

`ConcreteMCSP` proves the typed certificate theorem.  An NP machine, however,
receives one bitstring `input ++ witness`.  This file closes that representation
seam without assuming a machine compiler:

* each finite-basis gate has a prefix-consuming unary codec;
* whole circuits have a prefix-consuming codec with proved round trip;
* the MCSP input decoder consumes exactly `2^n` truth-table bits and leaves the
  appended witness untouched;
* `encodedVerifier` parses `input ++ witness`, decodes the circuit, rejects
  trailing garbage, and runs the concrete verifier;
* `encodedVerifier_encode` proves exact agreement with the typed verifier.

The remaining task is operational: construct a fixed finite-control
`ComposableMachine.Machine` implementing `encodedVerifier` with a polynomial
clock.  This file does not replace that construction by an assumption.
-/

namespace PallLean.Paper93.DeepMath.PathB.ConcreteMCSPWitnessCodec

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable
open PallLean.Paper93.DeepMath.PathB.ConcreteMCSP

@[simp] theorem encodeNatBits_length (a : ℕ) :
    (encodeNatBits a).length = a + 1 := by
  simp [encodeNatBits]

/-! ## Gate and circuit witness codecs -/

/-- Unary tagged encoding of a gate.  Tags:
`0=input`, `1=false`, `2=true`, `3=not`, `4=and`, `5=or`, `6=xor`. -/
def encodeGate : Gate n → List Bool
  | .input i => encodeNatBits 0 ++ encodeNatBits i.val
  | .cst false => encodeNatBits 1
  | .cst true => encodeNatBits 2
  | .neg j => encodeNatBits 3 ++ encodeNatBits j
  | .conj j k => encodeNatBits 4 ++ encodeNatBits j ++ encodeNatBits k
  | .disj j k => encodeNatBits 5 ++ encodeNatBits j ++ encodeNatBits k
  | .xor j k => encodeNatBits 6 ++ encodeNatBits j ++ encodeNatBits k

/-- Prefix-consuming gate decoder. -/
def decodeGate (n : ℕ) (w : List Bool) : Option (Gate n × List Bool) :=
  let tag := decodeNatBits w
  match tag.1 with
  | 0 =>
      let a := decodeNatBits tag.2
      if h : a.1 < n then some (.input ⟨a.1, h⟩, a.2) else none
  | 1 => some (.cst false, tag.2)
  | 2 => some (.cst true, tag.2)
  | 3 =>
      let a := decodeNatBits tag.2
      some (.neg a.1, a.2)
  | 4 =>
      let a := decodeNatBits tag.2
      let b := decodeNatBits a.2
      some (.conj a.1 b.1, b.2)
  | 5 =>
      let a := decodeNatBits tag.2
      let b := decodeNatBits a.2
      some (.disj a.1 b.1, b.2)
  | 6 =>
      let a := decodeNatBits tag.2
      let b := decodeNatBits a.2
      some (.xor a.1 b.1, b.2)
  | _ => none

@[simp] theorem decodeGate_encodeGate (g : Gate n) (rest : List Bool) :
    decodeGate n (encodeGate g ++ rest) = some (g, rest) := by
  cases g with
  | input i =>
      simp [encodeGate, decodeGate, decodeNatBits_encodeNatBits, i.isLt]
  | cst b =>
      cases b <;> simp [encodeGate, decodeGate, decodeNatBits_encodeNatBits]
  | neg j =>
      simp [encodeGate, decodeGate, decodeNatBits_encodeNatBits]
  | conj j k =>
      simp [encodeGate, decodeGate, decodeNatBits_encodeNatBits, List.append_assoc]
  | disj j k =>
      simp [encodeGate, decodeGate, decodeNatBits_encodeNatBits, List.append_assoc]
  | xor j k =>
      simp [encodeGate, decodeGate, decodeNatBits_encodeNatBits, List.append_assoc]

/-- Decode exactly `m` gates, leaving the unused suffix. -/
def decodeGates (n : ℕ) : ℕ → List Bool → Option (List (Gate n) × List Bool)
  | 0, w => some ([], w)
  | m + 1, w => do
      let (g, w₁) ← decodeGate n w
      let (gs, w₂) ← decodeGates n m w₁
      pure (g :: gs, w₂)

@[simp] theorem decodeGates_encode (gs : List (Gate n)) (rest : List Bool) :
    decodeGates n gs.length (gs.flatMap encodeGate ++ rest) = some (gs, rest) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.length_cons, List.flatMap_cons, decodeGates]
      rw [List.append_assoc, decodeGate_encodeGate]
      simp [ih]

/-- A circuit witness starts with its gate count, followed by that many gates. -/
def encodeCircuit (c : Circuit n) : List Bool :=
  encodeNatBits c.gates.length ++ c.gates.flatMap encodeGate

/-- Prefix-consuming circuit decoder. -/
def decodeCircuit (n : ℕ) (w : List Bool) : Option (Circuit n × List Bool) :=
  let m := decodeNatBits w
  match decodeGates n m.1 m.2 with
  | some (gs, rest) => some (⟨gs⟩, rest)
  | none => none

@[simp] theorem decodeCircuit_encodeCircuit (c : Circuit n) (rest : List Bool) :
    decodeCircuit n (encodeCircuit c ++ rest) = some (c, rest) := by
  simp [decodeCircuit, encodeCircuit, List.append_assoc, decodeNatBits_encodeNatBits]

/-! ## Prefix-consuming MCSP instance parser -/

/-- Decode the two unary header fields, consume exactly `2^n` table bits, and
return the untouched suffix as the witness region. -/
def decodeInstancePrefix (w : List Bool) : Instance × List Bool :=
  let a := decodeNatBits w
  let b := decodeNatBits a.2
  let table := b.2.take (2 ^ a.1)
  let rest := b.2.drop (2 ^ a.1)
  (⟨a.1, b.1, table⟩, rest)

theorem take_table_append {I : Instance} (hI : I.WellFormed) (w : List Bool) :
    (I.table ++ w).take (2 ^ I.n) = I.table := by
  rw [← hI]
  simp

theorem drop_table_append {I : Instance} (hI : I.WellFormed) (w : List Bool) :
    (I.table ++ w).drop (2 ^ I.n) = w := by
  rw [← hI]
  simp

/-- Exact input/witness split on well-formed encoded instances. -/
@[simp] theorem decodeInstancePrefix_encode {I : Instance} (hI : I.WellFormed)
    (w : List Bool) :
    decodeInstancePrefix (I.encode ++ w) = (I, w) := by
  simp only [decodeInstancePrefix, Instance.encode, List.append_assoc,
    decodeNatBits_encodeNatBits]
  rw [take_table_append hI, drop_table_append hI]

/-! ## The exact encoded verifier -/

/-- Parse the instance prefix, decode one circuit from the witness suffix,
reject trailing garbage, then run the concrete verifier. -/
def encodedVerifier (z : List Bool) : Bool :=
  let p := decodeInstancePrefix z
  match decodeCircuit p.1.n p.2 with
  | some (c, rest) => rest.isEmpty && verifier p.1 c
  | none => false

/-- On canonical `input ++ encoded-circuit` words, the encoded verifier is
definitionally aligned with the typed verifier. -/
theorem encodedVerifier_encode {I : Instance} (hI : I.WellFormed)
    (c : Circuit I.n) :
    encodedVerifier (I.encode ++ encodeCircuit c) = verifier I c := by
  unfold encodedVerifier
  rw [decodeInstancePrefix_encode hI]
  dsimp only
  have hdec : decodeCircuit I.n (encodeCircuit c) = some (c, []) := by
    simpa using decodeCircuit_encodeCircuit c []
  rw [hdec]
  rfl

/-- Soundness of encoded certificates. -/
theorem encodedVerifier_sound {I : Instance} (hI : I.WellFormed)
    {c : Circuit I.n}
    (h : encodedVerifier (I.encode ++ encodeCircuit c) = true) :
    Verifies I c := by
  rw [encodedVerifier_encode hI] at h
  exact (verifier_eq_true_iff I c).1 h

/-- Completeness of encoded certificates. -/
theorem encodedVerifier_complete {I : Instance} {c : Circuit I.n}
    (h : Verifies I c) :
    encodedVerifier (I.encode ++ encodeCircuit c) = true := by
  rw [encodedVerifier_encode h.1]
  exact (verifier_eq_true_iff I c).2 h

/-- On well-formed instances, the concrete MCSP predicate is exactly acceptance
of some canonically encoded circuit witness. -/
theorem mcsp_iff_encoded_certificate (I : Instance) (hI : I.WellFormed) :
    MCSPYes I ↔
      ∃ c : Circuit I.n,
        encodedVerifier (I.encode ++ encodeCircuit c) = true := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, encodedVerifier_complete hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, encodedVerifier_sound hI hc⟩

/-! ## Polynomial witness length -/

/-- All wire references in a gate are below `B`. -/
def RefsBelow (B : ℕ) : Gate n → Prop
  | .input _ | .cst _ => True
  | .neg j => j < B
  | .conj j k | .disj j k | .xor j k => j < B ∧ k < B

/-- A valid suffix only refers inside the full prefix-plus-suffix range. -/
theorem validFrom_refsBelow {gs : List (Gate n)} {i : ℕ}
    (h : Circuit.validFrom i gs = true) :
    ∀ g ∈ gs, RefsBelow (i + gs.length) g := by
  induction gs generalizing i with
  | nil => simp
  | cons g gs ih =>
      simp only [Circuit.validFrom, Bool.and_eq_true] at h
      obtain ⟨hg, hgs⟩ := h
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        cases g <;> simp [RefsBelow, Gate.validAt] at hg ⊢ <;> omega
      · have H := ih hgs q hq
        rw [List.length_cons]
        rw [show i + (gs.length + 1) = i + 1 + gs.length by omega]
        exact H

/-- Every reference in a valid circuit is below its gate count. -/
theorem valid_refsBelow {c : Circuit n} (h : c.valid = true) :
    ∀ g ∈ c.gates, RefsBelow c.gates.length g := by
  unfold Circuit.valid at h
  have H := validFrom_refsBelow h
  simpa using H

/-- Each gate encoding is linearly bounded by the arity and the common wire
bound. -/
theorem encodeGate_length_le {g : Gate n} {B : ℕ} (h : RefsBelow B g) :
    (encodeGate g).length ≤ 2 * (n + B + 10) := by
  cases g with
  | input i =>
      simp [encodeGate, RefsBelow, encodeNatBits_length] at h ⊢
      omega
  | cst b =>
    cases b with
    | false =>
      simp [encodeGate, encodeNatBits_length]
    | true =>
      simp [encodeGate, encodeNatBits_length]
      omega
  | neg j =>
      simp [encodeGate, RefsBelow, encodeNatBits_length] at h ⊢
      omega
  | conj j k =>
      simp [encodeGate, RefsBelow, encodeNatBits_length] at h ⊢
      omega
  | disj j k =>
      simp [encodeGate, RefsBelow, encodeNatBits_length] at h ⊢
      omega
  | xor j k =>
      simp [encodeGate, RefsBelow, encodeNatBits_length] at h ⊢
      omega

/-- Encoding a list of bounded-reference gates costs at most its length times
the uniform per-gate bound. -/
theorem flatMap_encodeGate_length_le (gs : List (Gate n)) (B : ℕ)
    (h : ∀ g ∈ gs, RefsBelow B g) :
    (gs.flatMap encodeGate).length ≤ gs.length * (2 * (n + B + 10)) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      have hg := encodeGate_length_le (h g (by simp))
      have htail : ∀ q ∈ gs, RefsBelow B q :=
        fun q hq => h q (by simp [hq])
      have ht := ih htail
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith

/-- The canonical input encoding length is exactly the structured input size. -/
theorem encode_length (I : Instance) : I.encode.length = I.inputSize := by
  simp [Instance.encode, Instance.inputSize, encodeNatBits_length]
  omega

/-- A uniform polynomial witness budget. -/
def mcspWitnessBound (N : ℕ) : ℕ := 3 * (N + 10) ^ 3

/-- A verified circuit certificate has a polynomial-size canonical bit
encoding. -/
theorem encodeCircuit_length_poly {I : Instance} {c : Circuit I.n}
    (h : Verifies I c) :
    (encodeCircuit c).length ≤ mcspWitnessBound I.inputSize := by
  let m := c.gates.length
  let N := I.inputSize
  have hmS : m ≤ I.threshold := h.2.1
  have hmN : m ≤ N := by
    dsimp [m, N]
    unfold Instance.inputSize
    omega
  have hnN : I.n ≤ N := by
    dsimp [N]
    unfold Instance.inputSize
    omega
  have href : ∀ g ∈ c.gates, RefsBelow m g := by
    dsimp [m]
    exact valid_refsBelow h.2.2.1
  have hflat :
      (c.gates.flatMap encodeGate).length
        ≤ m * (2 * (I.n + m + 10)) := by
    exact flatMap_encodeGate_length_le c.gates m href
  have hheader : (encodeNatBits m).length = m + 1 := by
    simp [encodeNatBits_length]
  let X := I.inputSize + 10
  have hmX : m ≤ X := by
    dsimp [X]
    omega
  have hK : 2 * (I.n + m + 10) ≤ 4 * X := by
    dsimp [X]
    omega
  have hflatX :
      (c.gates.flatMap encodeGate).length ≤ 4 * X ^ 2 := by
    calc
      (c.gates.flatMap encodeGate).length
          ≤ m * (2 * (I.n + m + 10)) := hflat
      _ ≤ X * (4 * X) := Nat.mul_le_mul hmX hK
      _ = 4 * X ^ 2 := by ring
  have hheadX : m + 1 ≤ X := by
    dsimp [X]
    omega
  have h4 : 4 ≤ X := by
    dsimp [X]
    omega
  have hquad : 4 * X ^ 2 ≤ X ^ 3 := by
    calc
      4 * X ^ 2 ≤ X * X ^ 2 := Nat.mul_le_mul_right (X ^ 2) h4
      _ = X ^ 3 := by ring
  have hlin : X ≤ X ^ 3 := by
    have hx : 1 ≤ X := by omega
    have hx2 : 1 ≤ X ^ 2 := Nat.one_le_pow 2 X hx
    calc
      X = X * 1 := by simp
      _ ≤ X * X ^ 2 := Nat.mul_le_mul_left X hx2
      _ = X ^ 3 := by ring
  unfold encodeCircuit mcspWitnessBound
  rw [List.length_append, hheader]
  calc
    m + 1 + (c.gates.flatMap encodeGate).length
        ≤ X + 4 * X ^ 2 := Nat.add_le_add hheadX hflatX
    _ ≤ X ^ 3 + X ^ 3 := Nat.add_le_add hlin hquad
    _ ≤ 3 * X ^ 3 := by omega

/-- The chosen witness budget is polynomially bounded. -/
theorem mcspWitnessBound_poly :
    PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant.PolyBounded
      mcspWitnessBound := by
  refine ⟨3000, 3, fun N => ?_⟩
  have h : N + 10 ≤ 10 * (N + 1) := by omega
  have hp : (N + 10) ^ 3 ≤ (10 * (N + 1)) ^ 3 :=
    Nat.pow_le_pow_left h 3
  unfold mcspWitnessBound
  calc
    3 * (N + 10) ^ 3 ≤ 3 * (10 * (N + 1)) ^ 3 :=
      Nat.mul_le_mul_left 3 hp
    _ = 3000 * (N + 1) ^ 3 := by ring

/-- Acceptance of an arbitrary appended witness means that it decodes to one
complete circuit (with no trailing garbage) accepted by the typed verifier. -/
theorem encodedVerifier_accept_iff {I : Instance} (hI : I.WellFormed)
    (w : List Bool) :
    encodedVerifier (I.encode ++ w) = true ↔
      ∃ c : Circuit I.n,
        decodeCircuit I.n w = some (c, []) ∧ Verifies I c := by
  unfold encodedVerifier
  rw [decodeInstancePrefix_encode hI]
  dsimp only
  cases hdec : decodeCircuit I.n w with
  | none =>
      simp
  | some p =>
      rcases p with ⟨c, rest⟩
      constructor
      · intro h
        have hand : rest.isEmpty = true ∧ verifier I c = true := by
          simpa only [Bool.and_eq_true] using h
        have hrest : rest = [] := by
          simpa using hand.1
        subst rest
        exact ⟨c, rfl, (verifier_eq_true_iff I c).1 hand.2⟩
      · rintro ⟨c', hc', hv⟩
        have hp : (c, rest) = (c', []) := Option.some.inj hc'
        cases hp
        simp [(verifier_eq_true_iff I c).2 hv]

/-- **Encoded verifier-level `MCSP ∈ NP`.**  On a well-formed input word,
concrete MCSP holds iff some polynomial-length appended bitstring is accepted by
the exact executable encoded verifier. -/
theorem mcsp_in_np_encoded (I : Instance) (hI : I.WellFormed) :
    MCSPYes I ↔
      ∃ w : List Bool,
        w.length ≤ mcspWitnessBound I.encode.length ∧
        encodedVerifier (I.encode ++ w) = true := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨encodeCircuit c, ?_, encodedVerifier_complete hc⟩
    rw [encode_length]
    exact encodeCircuit_length_poly hc
  · rintro ⟨w, _, hw⟩
    obtain ⟨c, _, hc⟩ := (encodedVerifier_accept_iff hI w).1 hw
    exact ⟨c, hc⟩

end PallLean.Paper93.DeepMath.PathB.ConcreteMCSPWitnessCodec

#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteMCSPWitnessCodec.decodeCircuit_encodeCircuit
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteMCSPWitnessCodec.encodedVerifier_encode
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteMCSPWitnessCodec.mcsp_iff_encoded_certificate
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteMCSPWitnessCodec.encodeCircuit_length_poly
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteMCSPWitnessCodec.mcsp_in_np_encoded
