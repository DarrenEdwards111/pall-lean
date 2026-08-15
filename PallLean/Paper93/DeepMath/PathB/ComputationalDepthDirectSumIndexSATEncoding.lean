import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDirectSumIndexCommunication
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMachineSemantics

/-!
# Explicit split-preserving direct-sum INDEX to SAT/CNF encoding

Alice's `copies * m` data bits and Bob's one-hot query bits are encoded in two
separate, fixed-length blocks.  Their concatenation is mapped to a zero-variable
CNF: the empty conjunction when the selected INDEX bit is true, and a CNF
containing the empty clause when it is false.  Thus the generated CNF is
satisfiable exactly when the direct-sum INDEX answer is true.

The reduction is intentionally elementary: INDEX itself is easy to reduce to
SAT.  Its role is to discharge the language-level `SplitEmbedding` socket while
preserving the Alice/Bob partition used by the communication lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.DirectSumIndexSATEncoding

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.DirectSumIndexCommunication
open PallLean.Paper93.DeepMath.PathB.OneWayCommLB

/-- Canonical flattening of a block/coordinate pair. -/
noncomputable def flattenIndex (copies m : Nat) :
    (Fin copies × Fin m) ≃ Fin (copies * m) := by
  simpa using Fintype.equivFin (Fin copies × Fin m)

/-- Alice's block is the flattened direct-sum data table. -/
noncomputable def encodeIndexAlice (copies m : Nat)
    (data : Fin copies → Fin m → Bool) : Fin (copies * m) → Bool :=
  fun i =>
    let q := (flattenIndex copies m).symm i
    data q.1 q.2

/-- Bob's block is a one-hot encoding of the selected block/coordinate pair. -/
noncomputable def encodeIndexBob (copies m : Nat) (query : Fin copies × Fin m) :
    Fin (copies * m) → Bool :=
  fun i => decide ((flattenIndex copies m).symm i = query)

theorem encodeIndexAlice_injective (copies m : Nat) :
    Function.Injective (encodeIndexAlice copies m) := by
  intro left right h
  funext block bit
  have hi := congrFun h (flattenIndex copies m (block, bit))
  simpa [encodeIndexAlice] using hi

theorem encodeIndexBob_injective (copies m : Nat) :
    Function.Injective (encodeIndexBob copies m) := by
  intro left right h
  have hi := congrFun h (flattenIndex copies m left)
  simpa [encodeIndexBob] using hi

/-- The exact split input presented to the SAT slice. -/
noncomputable def encodedIndexInput (copies m : Nat)
    (data : Fin copies → Fin m → Bool) (query : Fin copies × Fin m) : List Bool :=
  List.ofFn (encodeIndexAlice copies m data) ++
    List.ofFn (encodeIndexBob copies m query)

/-- Recognize an encoded direct-sum INDEX input and return its selected bit.
The existential is finite and the split encodings are injective, so the answer
is unambiguous on the image of `encodedIndexInput`. -/
noncomputable def encodedIndexAnswer (copies m : Nat) (bits : List Bool) : Bool :=
  if ∃ (data : Fin copies → Fin m → Bool) (query : Fin copies × Fin m),
      bits = encodedIndexInput copies m data query ∧
        directSumIndex copies m data query = true
  then true else false

/-- A zero-variable CNF whose satisfiability is exactly the supplied bit. -/
def bitCNF (b : Bool) : CNF where
  vars := 0
  clauses := if b then [] else [[]]

theorem bitCNF_eval_nil (b : Bool) : (bitCNF b).eval [] = b := by
  cases b <;> rfl

theorem bitCNF_satisfiable_iff (b : Bool) :
    Satisfiable (bitCNF b) ↔ b = true := by
  constructor
  · rintro ⟨assignment, hlen, heval⟩
    have : assignment = [] := List.eq_nil_of_length_eq_zero (by simpa [bitCNF] using hlen)
    subst assignment
    simpa [bitCNF_eval_nil] using heval
  · intro hb
    subst b
    exact ⟨[], rfl, rfl⟩

/-- The concrete CNF generated from the two encoded input blocks. -/
noncomputable def encodedIndexCNF (copies m : Nat) (bits : List Bool) : CNF :=
  bitCNF (encodedIndexAnswer copies m bits)

/-- Boolean SAT language slice for the generated CNFs. -/
noncomputable def directSumIndexSATSlice (copies m : Nat) (bits : List Bool) : Bool :=
  (encodedIndexCNF copies m bits).eval []

theorem encodedIndexAnswer_correct (copies m : Nat)
    (data : Fin copies → Fin m → Bool) (query : Fin copies × Fin m) :
    encodedIndexAnswer copies m (encodedIndexInput copies m data query) =
      directSumIndex copies m data query := by
  classical
  by_cases hbit : directSumIndex copies m data query = true
  · have hex : ∃ (data' : Fin copies → Fin m → Bool)
        (block : Fin copies) (bit : Fin m),
        encodedIndexInput copies m data query =
            encodedIndexInput copies m data' (block, bit) ∧
          directSumIndex copies m data' (block, bit) = true :=
      ⟨data, query.1, query.2, by cases query; rfl, by simpa using hbit⟩
    simp [encodedIndexAnswer, hex, hbit]
  · have hfalse : directSumIndex copies m data query = false :=
      Bool.eq_false_of_not_eq_true hbit
    rw [hfalse]
    simp only [encodedIndexAnswer]
    split
    · rename_i hex
      rcases hex with ⟨data', query', heq, htrue⟩
      have hAlice :
          List.ofFn (encodeIndexAlice copies m data) =
            List.ofFn (encodeIndexAlice copies m data') := by
        have := congrArg (List.take (copies * m)) heq
        simpa [encodedIndexInput] using this
      have hBob :
          List.ofFn (encodeIndexBob copies m query) =
            List.ofFn (encodeIndexBob copies m query') := by
        have := congrArg (List.drop (copies * m)) heq
        simpa [encodedIndexInput] using this
      have hdata : data = data' := encodeIndexAlice_injective copies m (by
        simpa using hAlice)
      have hquery : query = query' := encodeIndexBob_injective copies m (by
        simpa using hBob)
      subst data'
      subst query'
      exact (hbit htrue).elim
    · rfl

theorem directSumIndexSATSlice_correct (copies m : Nat)
    (data : Fin copies → Fin m → Bool) (query : Fin copies × Fin m) :
    directSumIndexSATSlice copies m (encodedIndexInput copies m data query) =
      directSumIndex copies m data query := by
  rw [directSumIndexSATSlice, encodedIndexCNF, bitCNF_eval_nil,
    encodedIndexAnswer_correct]

theorem encodedIndexCNF_satisfiable_iff (copies m : Nat)
    (data : Fin copies → Fin m → Bool) (query : Fin copies × Fin m) :
    Satisfiable (encodedIndexCNF copies m (encodedIndexInput copies m data query)) ↔
      directSumIndex copies m data query = true := by
  rw [encodedIndexCNF, bitCNF_satisfiable_iff, encodedIndexAnswer_correct]

/-- Explicit split-preserving embedding of direct-sum INDEX into the generated
SAT/CNF language slice. -/
noncomputable def directSumIndexSATEmbedding (copies m : Nat) :
    SplitEmbedding (directSumIndexSATSlice copies m)
      copies m (copies * m) (copies * m) where
  encodeAlice := encodeIndexAlice copies m
  encodeBob := encodeIndexBob copies m
  correct := directSumIndexSATSlice_correct copies m

/-- The concrete generated SAT slice inherits the full direct-sum message
lower bound through the explicit split embedding. -/
theorem directSumIndexSATSlice_messages_ge (copies m messages : Nat)
    (P : OneWayProtocol (Fin (copies * m) → Bool)
      (Fin (copies * m) → Bool) messages)
    (hP : Computes P (fun u v =>
      directSumIndexSATSlice copies m (List.ofFn u ++ List.ofFn v))) :
    2 ^ (m * copies) ≤ messages :=
  messages_ge_of_splitEmbedding (directSumIndexSATEmbedding copies m) P hP

/-- Bit form of the concrete SAT-slice communication lower bound. -/
theorem directSumIndexSATSlice_bits_ge (copies m messages : Nat)
    (P : OneWayProtocol (Fin (copies * m) → Bool)
      (Fin (copies * m) → Bool) messages)
    (hP : Computes P (fun u v =>
      directSumIndexSATSlice copies m (List.ofFn u ++ List.ofFn v))) :
    m * copies ≤ Nat.log 2 messages := by
  have h := directSumIndexSATSlice_messages_ge copies m messages P hP
  calc
    m * copies = Nat.log 2 (2 ^ (m * copies)) :=
      (Nat.log_pow (by norm_num : 1 < 2) (m * copies)).symm
    _ ≤ Nat.log 2 messages := Nat.log_mono_right h

end PallLean.Paper93.DeepMath.PathB.DirectSumIndexSATEncoding

#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexSATEncoding.encodedIndexAnswer_correct
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexSATEncoding.directSumIndexSATSlice_correct
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexSATEncoding.encodedIndexCNF_satisfiable_iff
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexSATEncoding.directSumIndexSATEmbedding
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexSATEncoding.directSumIndexSATSlice_messages_ge
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexSATEncoding.directSumIndexSATSlice_bits_ge
