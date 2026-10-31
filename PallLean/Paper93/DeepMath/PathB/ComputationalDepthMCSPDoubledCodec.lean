import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteMCSPWitnessCodec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinDoubled

/-!
# Concrete MCSP: a self-delimiting truth-table codec

The original concrete MCSP encoding puts a raw truth table immediately before
an appended circuit witness.  Its mathematical prefix decoder can locate the
boundary from `2^n`, but a two-symbol finite-control tape has no spare marker
symbol.  This file gives the machine-facing representation used by the
finite-control verifier:

* header naturals retain the existing unary encoding;
* each truth-table bit is doubled (`b ↦ bb`);
* the unequal pair `01` terminates the table;
* a prefix decoder is proved to recover the table and leave every appended
  witness bit untouched;
* the doubled encoded verifier is proved exactly equivalent to the existing
  typed verifier and, on canonical instances, to the raw encoded verifier.

This is a representation bridge, not a complexity assumption and not an
MCSP lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPDoubledCodec

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable
open PallLean.Paper93.DeepMath.PathB.ConcreteMCSP
open PallLean.Paper93.DeepMath.PathB.ConcreteMCSPWitnessCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled

/-! ## Prefix-consuming doubled-data decoder -/

/-- Consume equal pairs as data and stop at the first unequal pair.  The
unequal marker itself is consumed; the second component is the untouched
suffix after it.  On malformed odd inputs, the unpaired suffix is left
untouched. -/
def decodeDPrefix : List Bool → List Bool × List Bool
  | a :: b :: xs =>
      if a = b then
        let p := decodeDPrefix xs
        (a :: p.1, p.2)
      else
        ([], xs)
  | xs => ([], xs)

/-- Doubled data followed by arbitrary bits is decoded exactly, including an
exact suffix split at the `01` marker. -/
@[simp] theorem decodeDPrefix_encodeD (table rest : List Bool) :
    decodeDPrefix (encodeD table ++ rest) = (table, rest) := by
  induction table with
  | nil =>
      simp [encodeD, decodeDPrefix]
  | cons b table ih =>
      simp [encodeD, decodeDPrefix, ih]

/-! ## Doubled MCSP instances -/

/-- Machine-facing MCSP encoding with a locally detectable table boundary. -/
def encodeInstanceD (I : Instance) : List Bool :=
  encodeNatBits I.n ++ encodeNatBits I.threshold ++ encodeD I.table

/-- Prefix decoder for a doubled MCSP instance followed by an arbitrary
witness. -/
def decodeInstanceDPrefix (w : List Bool) : Instance × List Bool :=
  let a := decodeNatBits w
  let b := decodeNatBits a.2
  let t := decodeDPrefix b.2
  (⟨a.1, b.1, t.1⟩, t.2)

/-- Canonical doubled inputs recover the exact instance and preserve the
appended witness byte-for-byte. -/
@[simp] theorem decodeInstanceDPrefix_encode (I : Instance) (w : List Bool) :
    decodeInstanceDPrefix (encodeInstanceD I ++ w) = (I, w) := by
  simp [decodeInstanceDPrefix, encodeInstanceD, List.append_assoc,
    decodeNatBits_encodeNatBits]

/-- Total decoder for standalone doubled MCSP words. -/
def decodeInstanceD (w : List Bool) : Instance :=
  (decodeInstanceDPrefix w).1

@[simp] theorem decodeInstanceD_encode (I : Instance) :
    decodeInstanceD (encodeInstanceD I) = I := by
  have h := congrArg Prod.fst (decodeInstanceDPrefix_encode I [])
  simpa [decodeInstanceD] using h

/-! ## Exact verifier alignment -/

/-- Decode the doubled instance, decode one complete circuit from the suffix,
and run the same typed verifier as the raw codec. -/
def encodedVerifierD (z : List Bool) : Bool :=
  let p := decodeInstanceDPrefix z
  match decodeCircuit p.1.n p.2 with
  | some (c, rest) => rest.isEmpty && verifier p.1 c
  | none => false

theorem encodedVerifierD_encode (I : Instance) (c : Circuit I.n) :
    encodedVerifierD (encodeInstanceD I ++ encodeCircuit c) = verifier I c := by
  unfold encodedVerifierD
  rw [decodeInstanceDPrefix_encode]
  dsimp only
  have hdec : decodeCircuit I.n (encodeCircuit c) = some (c, []) := by
    simpa using decodeCircuit_encodeCircuit c []
  rw [hdec]
  rfl

/-- The raw and doubled canonical encodings accept exactly the same typed
certificate. -/
theorem encodedVerifierD_eq_raw {I : Instance} (hI : I.WellFormed)
    (c : Circuit I.n) :
    encodedVerifierD (encodeInstanceD I ++ encodeCircuit c) =
      encodedVerifier (I.encode ++ encodeCircuit c) := by
  rw [encodedVerifierD_encode, encodedVerifier_encode hI]

theorem encodedVerifierD_sound {I : Instance} {c : Circuit I.n}
    (h : encodedVerifierD (encodeInstanceD I ++ encodeCircuit c) = true) :
    Verifies I c := by
  rw [encodedVerifierD_encode] at h
  exact (verifier_eq_true_iff I c).1 h

theorem encodedVerifierD_complete {I : Instance} {c : Circuit I.n}
    (h : Verifies I c) :
    encodedVerifierD (encodeInstanceD I ++ encodeCircuit c) = true := by
  rw [encodedVerifierD_encode]
  exact (verifier_eq_true_iff I c).2 h

theorem mcsp_iff_doubled_certificate (I : Instance) :
    MCSPYes I ↔
      ∃ c : Circuit I.n,
        encodedVerifierD (encodeInstanceD I ++ encodeCircuit c) = true := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, encodedVerifierD_complete hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, encodedVerifierD_sound hc⟩

/-! ## Size accounting -/

@[simp] theorem encodeInstanceD_length (I : Instance) :
    (encodeInstanceD I).length =
      I.n + I.threshold + 2 * I.table.length + 4 := by
  simp [encodeInstanceD, encodeNatBits_length, encodeD_length]
  omega

/-- The doubled representation has at most twice the raw representation plus
a constant. -/
theorem encodeInstanceD_length_le (I : Instance) :
    (encodeInstanceD I).length ≤ 2 * I.encode.length + 2 := by
  simp [encodeInstanceD_length, Instance.encode, encodeNatBits_length]
  omega

/-- Conversely, the raw canonical representation is no longer than the
doubled one. -/
theorem encode_length_le_encodeInstanceD (I : Instance) :
    I.encode.length ≤ (encodeInstanceD I).length := by
  simp [encodeInstanceD_length, Instance.encode, encodeNatBits_length]
  omega

end PallLean.Paper93.DeepMath.PathB.MCSPDoubledCodec

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPDoubledCodec.decodeDPrefix_encodeD
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPDoubledCodec.decodeInstanceDPrefix_encode
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPDoubledCodec.encodedVerifierD_eq_raw
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPDoubledCodec.mcsp_iff_doubled_certificate
