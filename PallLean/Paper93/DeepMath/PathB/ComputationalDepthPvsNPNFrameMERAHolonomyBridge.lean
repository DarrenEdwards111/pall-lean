import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameRestrictedMERADecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderAmplificationBoundary
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypergraphHolonomySPDP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMathlibCandidates

/-!
# Restricted MERA: local-SPDP collapse and the holonomy replacement

The parity-core bridge supplies a concrete exponential rank, but its rows are linear and easy.  The
next proposed target is the high-degree affine/Tseitin indicator residual.  The repository's existing
`ExpanderAmplificationBoundary` proves that a fixed-order SPDP probe sees none of a high-distance
residual: its projected rank is at most one.

This file connects that negative theorem to the restricted MERA ceiling, then tests the global
holonomy replacement.  A canonical family of separated cycles realizes every `n`-bit holonomy
signature, hence has exactly `2^n` holonomy classes.  This decoder-independent exponential demand
eventually exceeds every fixed-bond, fixed-cone, logarithmic-depth MERA accessible-rank ceiling.

The result is deliberately restricted.  Holonomy escapes the *local projection* failure, but the
canonical signature is efficiently computable and is not an NP-complete language lower bound.
Applying it to SAT still needs a correctness-to-holonomy transport theorem for a genuine NP-complete
residual family.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection
open PallLean.Paper93.DeepMath.PathB.ExpanderAmplificationBoundary
open PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder

abbrev MERAFamily := BoundedBondLocalMERADecoderFamily

/-! ## Fixed-order SPDP cannot supply the high-distance MERA obstruction -/

/-- A high-distance residual below the SPDP probe radius has projected rank at most the restricted
MERA polynomial ceiling.  Thus this fixed-order local projection cannot furnish the strict rank gap
needed by `not_preservesRequiredRank_of_exceeds_ceiling`. -/
theorem highDistance_spdpRank_le_MERA_ceiling
    (M : MERAFamily) {a : Nat} {A : Type*} [Fintype A]
    (k d delta : Nat) (matrix : A → (Fin a → Bool) → Bool)
    (hdistance : MinSupportWeight matrix delta) (hbelow : k + d < delta)
    (n : Nat) (hn : 1 ≤ n) :
    pcrank (spdpProj a k d) matrix ≤ n ^ M.polyExponent := by
  have hcollapse : pcrank (spdpProj a k d) matrix ≤ 1 :=
    highDistance_spdp_collapse k d delta matrix hdistance hbelow
  exact le_trans hcollapse (Nat.one_le_pow _ _ hn)

/-- Consequently the high-distance fixed-order SPDP rank cannot exceed the MERA ceiling at any
positive comparison size. -/
theorem not_MERA_ceiling_lt_highDistance_spdpRank
    (M : MERAFamily) {a : Nat} {A : Type*} [Fintype A]
    (k d delta : Nat) (matrix : A → (Fin a → Bool) → Bool)
    (hdistance : MinSupportWeight matrix delta) (hbelow : k + d < delta)
    (n : Nat) (hn : 1 ≤ n) :
    ¬ n ^ M.polyExponent < pcrank (spdpProj a k d) matrix := by
  exact not_lt_of_ge
    (highDistance_spdpRank_le_MERA_ceiling M k d delta matrix hdistance hbelow n hn)

/-! ## A global holonomy signature has exponential rank -/

/-- Canonical separated cycles: cycle `i` consists of its own representative `i`.  The point is not
graph expansion here; it is a minimal exact witness that independent holonomy coordinates realize all
Boolean signatures. -/
def canonicalDisjointCycles (n : Nat) : DisjointCycles (Fin n) n where
  cycle := fun i => {i}
  rep := id
  rep_mem := fun i => by simp
  rep_only_own := fun i j hij => by simpa using hij

/-- Number of distinct holonomy signatures realized by the canonical `n`-cycle family. -/
def holonomyPatternRank (n : Nat) : Nat :=
  (Finset.univ.image (fun charge : Fin n → Bool =>
    holSig (canonicalDisjointCycles n).cycle charge)).card

/-- **Global holonomy survival.**  The canonical family realizes exactly all `2^n` signatures. -/
theorem holonomyPatternRank_eq_two_pow (n : Nat) :
    holonomyPatternRank n = 2 ^ n := by
  classical
  have himage :
      Finset.univ.image (fun charge : Fin n → Bool =>
        holSig (canonicalDisjointCycles n).cycle charge) =
      (Finset.univ : Finset (Fin n → Bool)) := by
    apply Finset.eq_univ_of_forall
    intro target
    obtain ⟨charge, hcharge⟩ :=
      holonomy_realizes_all (canonicalDisjointCycles n) target
    exact Finset.mem_image.mpr ⟨charge, Finset.mem_univ charge, hcharge⟩
  unfold holonomyPatternRank
  rw [himage, Finset.card_univ, Fintype.card_fun]
  simp [Fintype.card_bool, Fintype.card_fin]

/-- The concrete exponential holonomy demand eventually exceeds every fixed restricted MERA
polynomial ceiling. -/
theorem exists_holonomyRank_exceeds_MERA_ceiling (M : MERAFamily) :
    ∃ n : Nat, 1 ≤ n ∧ n ^ M.polyExponent < holonomyPatternRank n := by
  obtain ⟨n, hn, hgap⟩ :=
    Nat.exists_poly_lt_pow (p := 2) (by omega) 1 M.polyExponent 0
  refine ⟨n, hn, ?_⟩
  simpa [holonomyPatternRank_eq_two_pow] using hgap

/-- **Restricted MERA holonomy lower bound.**  No fixed-bond, fixed-cone,
logarithmic-depth local MERA family preserves all independent holonomy classes. -/
theorem not_preserves_holonomyPatternRank (M : MERAFamily) :
    ¬ M.PreservesRequiredRank holonomyPatternRank := by
  obtain ⟨n, hn, hgap⟩ := exists_holonomyRank_exceeds_MERA_ceiling M
  exact M.not_preservesRequiredRank_of_exceeds_ceiling holonomyPatternRank n hn hgap

/-- Pointwise failure: every restricted MERA family has some size where its accessible rank is
strictly below the number of realized holonomy signatures. -/
theorem exists_holonomyRank_exceeds_accessibleRank (M : MERAFamily) :
    ∃ n : Nat, M.accessibleRank n < holonomyPatternRank n := by
  obtain ⟨n, hn, hgap⟩ := exists_holonomyRank_exceeds_MERA_ceiling M
  exact ⟨n, lt_of_le_of_lt (M.accessibleRank_le_poly n hn) hgap⟩

/-! ## Exact SAT transport frontier -/

/-- The separate, unproved decision-invariance obligation: SAT correctness for `D` forces the
task-relevant holonomy distinctions to survive in its restricted MERA realization. -/
def SATCorrectnessTransportsHolonomyRank
    (U : MachineModel) (D : DecisionMachine U) (M : MERAFamily) : Prop :=
  DecidesSAT U D → M.PreservesRequiredRank holonomyPatternRank

/-- A restricted MERA SAT machine with a correctness-to-holonomy transport certificate cannot exist. -/
theorem not_decidesSAT_of_holonomy_transport
    {U : MachineModel} {D : DecisionMachine U} (M : MERAFamily)
    (htransport : SATCorrectnessTransportsHolonomyRank U D M) :
    ¬ DecidesSAT U D := by
  intro hD
  exact (not_preserves_holonomyPatternRank M) (htransport hD)

/-- The explicitly restricted solver class: machines supplied with a bounded-bond local MERA
realization and a task-holonomy transport certificate. -/
def HasHolonomyFaithfulRestrictedMERA
    (U : MachineModel) (D : DecisionMachine U) : Prop :=
  ∃ M : MERAFamily, SATCorrectnessTransportsHolonomyRank U D M

/-- No solver in the holonomy-faithful restricted MERA class decides SAT. -/
theorem no_SAT_decider_with_holonomyFaithfulRestrictedMERA
    {U : MachineModel} :
    ¬ ∃ D : DecisionMachine U,
      HasHolonomyFaithfulRestrictedMERA U D ∧ DecidesSAT U D := by
  rintro ⟨D, ⟨M, htransport⟩, hD⟩
  exact (not_decidesSAT_of_holonomy_transport M htransport) hD

/-!
## Verdict

The high-degree affine-indicator continuation cannot work with fixed-order local SPDP: the existing
distance theorem forces rank `≤ 1`, and this file proves that rank never exceeds a positive MERA
polynomial ceiling.  Holonomy is a mathematically valid replacement for that local projection and has
`2^n` concrete classes, enough to beat restricted MERA.

What remains is not rank arithmetic.  It is proving that a genuine NP-complete residual family carries
these independent holonomy labels *and* that correctness of an arbitrary decoder in the intended model
forces their preservation.  Neither generic SAT correctness nor polynomial runtime implies that
transport automatically.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge.highDistance_spdpRank_le_MERA_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge.not_MERA_ceiling_lt_highDistance_spdpRank
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge.holonomyPatternRank_eq_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge.exists_holonomyRank_exceeds_MERA_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge.not_preserves_holonomyPatternRank
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge.exists_holonomyRank_exceeds_accessibleRank
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge.not_decidesSAT_of_holonomy_transport
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge.no_SAT_decider_with_holonomyFaithfulRestrictedMERA
