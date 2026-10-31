import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOneWayCommLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsOneWayComm

/-!
# Direct-sum INDEX communication lower bound

This module formalizes the strongest restricted target selected by the sixth
Curiosity search.  Alice holds `copies` independent `m`-bit blocks.  Bob asks
for one bit from one block.  All `2^(m*copies)` Alice inputs induce distinct
Bob-side subfunctions, so every exact deterministic one-way protocol needs at
least that many messages.

An explicit split-preserving embedding transfers the bound to any language
slice, including a SAT encoding once such an embedding is constructed.  The
embedding is deliberately visible; ordinary SAT correctness does not create it.
-/

namespace PallLean.Paper93.DeepMath.PathB.DirectSumIndexCommunication

open PallLean.Paper93.DeepMath.PathB.OneWayCommLB
open PallLean.Paper93.DeepMath.PathB.PvsOneWayComm

/-- Bob selects one of `copies` independent data blocks and one coordinate in
that block. -/
def directSumIndex (copies m : Nat) :
    (Fin copies → Fin m → Bool) → (Fin copies × Fin m) → Bool :=
  fun data query => data query.1 query.2

/-- Distinct direct-sum data vectors induce distinct query-answer functions. -/
theorem directSumIndex_row_injective (copies m : Nat) :
    Function.Injective
      (fun data : Fin copies → Fin m → Bool =>
        fun query => directSumIndex copies m data query) := by
  intro left right h
  funext block bit
  exact congrFun h (block, bit)

/-- There are exactly `2^(m*copies)` distinct direct-sum INDEX rows. -/
theorem subfuns_directSumIndex_card (copies m : Nat) :
    (subfuns (directSumIndex copies m)).card = 2 ^ (m * copies) := by
  unfold subfuns
  rw [Finset.card_image_of_injective _ (directSumIndex_row_injective copies m)]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  exact (pow_mul 2 m copies).symm

/-- Exact direct-sum theorem: a one-way protocol needs one distinct message for
every independent data vector. -/
theorem directSumIndex_oneWay_messages_ge (copies m messages : Nat)
    (P : OneWayProtocol (Fin copies → Fin m → Bool) (Fin copies × Fin m) messages)
    (hP : Computes P (directSumIndex copies m)) :
    2 ^ (m * copies) ≤ messages := by
  rw [← subfuns_directSumIndex_card copies m]
  exact oneWay_card_ge (directSumIndex copies m) P hP

/-- Bit form of the direct-sum lower bound. -/
theorem directSumIndex_oneWay_bits_ge (copies m messages : Nat)
    (P : OneWayProtocol (Fin copies → Fin m → Bool) (Fin copies × Fin m) messages)
    (hP : Computes P (directSumIndex copies m)) :
    m * copies ≤ Nat.log 2 messages := by
  have h := directSumIndex_oneWay_messages_ge copies m messages P hP
  calc
    m * copies = Nat.log 2 (2 ^ (m * copies)) :=
      (Nat.log_pow (by norm_num : 1 < 2) (m * copies)).symm
    _ ≤ Nat.log 2 messages := Nat.log_mono_right h

/-- A split-preserving embedding of direct-sum INDEX into a language slice. -/
structure SplitEmbedding (L : List Bool → Bool)
    (copies m aliceBits bobBits : Nat) where
  encodeAlice : (Fin copies → Fin m → Bool) → Fin aliceBits → Bool
  encodeBob : (Fin copies × Fin m) → Fin bobBits → Bool
  correct : ∀ data query,
    L (List.ofFn (encodeAlice data) ++ List.ofFn (encodeBob query)) =
      directSumIndex copies m data query

/-- A one-way protocol for a language slice pulls back along a split embedding
to a protocol for direct-sum INDEX. -/
def SplitEmbedding.pullback {L : List Bool → Bool}
    {copies m aliceBits bobBits messages : Nat}
    (E : SplitEmbedding L copies m aliceBits bobBits)
    (P : OneWayProtocol (Fin aliceBits → Bool) (Fin bobBits → Bool) messages) :
    OneWayProtocol (Fin copies → Fin m → Bool) (Fin copies × Fin m) messages where
  msg data := P.msg (E.encodeAlice data)
  out message query := P.out message (E.encodeBob query)

theorem SplitEmbedding.pullback_computes {L : List Bool → Bool}
    {copies m aliceBits bobBits messages : Nat}
    (E : SplitEmbedding L copies m aliceBits bobBits)
    (P : OneWayProtocol (Fin aliceBits → Bool) (Fin bobBits → Bool) messages)
    (hP : Computes P (fun u v => L (List.ofFn u ++ List.ofFn v))) :
    Computes (E.pullback P) (directSumIndex copies m) := by
  intro data query
  change P.out (P.msg (E.encodeAlice data)) (E.encodeBob query) = _
  calc
    P.out (P.msg (E.encodeAlice data)) (E.encodeBob query) =
        L (List.ofFn (E.encodeAlice data) ++ List.ofFn (E.encodeBob query)) :=
      hP (E.encodeAlice data) (E.encodeBob query)
    _ = directSumIndex copies m data query := E.correct data query

/-- Transfer theorem: any language slice containing the explicit direct-sum
INDEX embedding needs at least `2^(m*copies)` messages. -/
theorem messages_ge_of_splitEmbedding {L : List Bool → Bool}
    {copies m aliceBits bobBits messages : Nat}
    (E : SplitEmbedding L copies m aliceBits bobBits)
    (P : OneWayProtocol (Fin aliceBits → Bool) (Fin bobBits → Bool) messages)
    (hP : Computes P (fun u v => L (List.ofFn u ++ List.ofFn v))) :
    2 ^ (m * copies) ≤ messages :=
  directSumIndex_oneWay_messages_ge copies m messages (E.pullback P)
    (E.pullback_computes P hP)

end PallLean.Paper93.DeepMath.PathB.DirectSumIndexCommunication

#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexCommunication.subfuns_directSumIndex_card
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexCommunication.directSumIndex_oneWay_messages_ge
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexCommunication.directSumIndex_oneWay_bits_ge
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumIndexCommunication.messages_ge_of_splitEmbedding
