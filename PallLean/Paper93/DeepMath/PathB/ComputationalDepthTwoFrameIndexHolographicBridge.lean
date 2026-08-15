import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDebtGaugeInvariance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDirectSumIndexCommunication

/-!
# Two-frame holographic INDEX bridge

This module formalizes the strongest restricted two-frame pattern selected by
the holographic Curiosity audit:

* an explicit split-preserving direct-sum INDEX embedding supplies independent
  residual rows;
* a fine observer frame records their orientation-conflict debt;
* a lossless relabel followed by a lossy projection cannot reduce that debt;
* an `s`-bit boundary has at most `2^s` states;
* the same boundary is an exact one-way protocol for the language slice.

Consequently both the holographic debt route and the communication route force
`m * copies ≤ s`.  A subcritical boundary `s < m * copies` is impossible.

The forced projection/cut and exact orientation-debt certificate are explicit.
They hold for restricted formula/streaming/branching models with such a cut;
ordinary polynomial-time SAT correctness does not supply them automatically.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoFrameIndexHolographicBridge

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt
open PallLean.Paper93.DeepMath.PathB.DebtGaugeInvariance
open PallLean.Paper93.DeepMath.PathB.DirectSumIndexCommunication
open PallLean.Paper93.DeepMath.PathB.OneWayCommLB

/-- A certified two-frame realization of a direct-sum INDEX language slice.
The fine frame exposes every independent orientation; the projected frame is
the bounded observer boundary actually used by the protocol. -/
structure CertifiedTwoFrameIndexRun
    (L : List Bool → Bool) (copies m aliceBits bobBits s : Nat)
    (X FineLabel RelabeledLabel BoundaryLabel : Type*)
    [DecidableEq FineLabel] [DecidableEq RelabeledLabel]
    [DecidableEq BoundaryLabel] where
  embedding : SplitEmbedding L copies m aliceBits bobBits
  protocol : OneWayProtocol (Fin aliceBits → Bool) (Fin bobBits → Bool) (2 ^ s)
  protocol_correct :
    Computes protocol (fun u v => L (List.ofFn u ++ List.ofFn v))
  conflicts : Finset (X × X)
  fineView : X → FineLabel
  relabel : FineLabel → RelabeledLabel
  relabel_injective : Function.Injective relabel
  boundaryView : X → BoundaryLabel
  projection_lossy : ∀ x y,
    relabel (fineView x) = relabel (fineView y) →
      boundaryView x = boundaryView y
  /-- The independent residual rows appear as concrete fine-frame debt. -/
  orientation_conflict_load :
    debtCount conflicts fineView = 2 ^ (m * copies)
  /-- An `s`-bit boundary can expose at most `2^s` distinct debt units. -/
  bounded_boundary_capacity : debtCount conflicts boundaryView ≤ 2 ^ s

namespace CertifiedTwoFrameIndexRun

variable {L : List Bool → Bool} {copies m aliceBits bobBits s : Nat}
variable {X FineLabel RelabeledLabel BoundaryLabel : Type*}
variable [DecidableEq FineLabel] [DecidableEq RelabeledLabel]
variable [DecidableEq BoundaryLabel]

/-- Gauge-invariant debt plus lossy projection forces the full INDEX load to
remain visible at the bounded observer boundary. -/
theorem holographic_load_le_boundary
    (R : CertifiedTwoFrameIndexRun L copies m aliceBits bobBits s
      X FineLabel RelabeledLabel BoundaryLabel) :
    2 ^ (m * copies) ≤ 2 ^ s := by
  rw [← R.orientation_conflict_load]
  exact (debtCount_le_of_frameChange R.conflicts R.fineView R.relabel
    R.relabel_injective R.boundaryView R.projection_lossy).trans
      R.bounded_boundary_capacity

/-- Independently, pulling the boundary protocol back through the explicit
split embedding yields the same message-capacity inequality. -/
theorem communication_load_le_boundary
    (R : CertifiedTwoFrameIndexRun L copies m aliceBits bobBits s
      X FineLabel RelabeledLabel BoundaryLabel) :
    2 ^ (m * copies) ≤ 2 ^ s :=
  messages_ge_of_splitEmbedding R.embedding R.protocol R.protocol_correct

/-- The exact bit consequence: the boundary needs at least one bit for every
independent INDEX coordinate. -/
theorem required_boundary_bits
    (R : CertifiedTwoFrameIndexRun L copies m aliceBits bobBits s
      X FineLabel RelabeledLabel BoundaryLabel) :
    m * copies ≤ s := by
  have h := directSumIndex_oneWay_bits_ge copies m (2 ^ s)
    (R.embedding.pullback R.protocol)
    (R.embedding.pullback_computes R.protocol R.protocol_correct)
  simpa using h

/-- End-to-end restricted exclusion: no exact two-frame realization can carry
`m * copies` independent residual orientations through fewer than that many
boundary bits. -/
theorem no_subcritical_twoFrameIndexRun
    (hsubcritical : s < m * copies) :
    ¬ Nonempty
      (CertifiedTwoFrameIndexRun L copies m aliceBits bobBits s
        X FineLabel RelabeledLabel BoundaryLabel) := by
  rintro ⟨R⟩
  exact (Nat.not_le_of_lt hsubcritical) R.required_boundary_bits

end CertifiedTwoFrameIndexRun

end PallLean.Paper93.DeepMath.PathB.TwoFrameIndexHolographicBridge

#print axioms PallLean.Paper93.DeepMath.PathB.TwoFrameIndexHolographicBridge.CertifiedTwoFrameIndexRun.holographic_load_le_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.TwoFrameIndexHolographicBridge.CertifiedTwoFrameIndexRun.communication_load_le_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.TwoFrameIndexHolographicBridge.CertifiedTwoFrameIndexRun.required_boundary_bits
#print axioms PallLean.Paper93.DeepMath.PathB.TwoFrameIndexHolographicBridge.CertifiedTwoFrameIndexRun.no_subcritical_twoFrameIndexRun
