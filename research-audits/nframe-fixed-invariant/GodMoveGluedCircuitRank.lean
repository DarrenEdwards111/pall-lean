import GodMoveCircuitGluing
import GodMoveCircuitInterface

/-!
# The actual glued circuit factors through its computed Boolean ports

This connects the gate-by-gate gluing proof to the joint-state factorization.
The left side computes the ports from its real gate trace. The right side
reads those values, including repeated uses of the same left wire. No abstract
factorization or rank premise is supplied in place of the circuit semantics.

The resulting rank is a two-input response-matrix rank. It is not identified
with production N-Frame rank, and no arbitrary SAT separator theorem follows.
-/

namespace GodMoveGluedCircuitRank

open GodMoveCircuitGluing GodMoveCircuitInterface GodMoveBooleanInterpolation
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {a b r : ℕ}

def gluedResponse (cL : List (CGate a)) (ports : Fin r → Fin cL.length)
    (cR : List (CGate (r + b))) : Matrix (Assignment a) (Assignment b) ℚ :=
  fun x y => bit (output (glue cL ports cR) (Fin.append x y))

def finish (cR : List (CGate (r + b))) (s : Assignment r) (y : Assignment b) : Bool :=
  output cR (rightInput s y)

/-- The factorization is derived from the constructed circuit's actual output. -/
theorem gluedResponse_eq_response (cL : List (CGate a))
    (ports : Fin r → Fin cL.length) (cR : List (CGate (r + b))) (hR : cR ≠ []) :
    gluedResponse cL ports cR = response (portValues cL ports) (finish cR) := by
  ext x y
  simp only [gluedResponse, response, finish, output_glue_append cL ports cR hR]

theorem gluedResponse_factorization (cL : List (CGate a))
    (ports : Fin r → Fin cL.length) (cR : List (CGate (r + b))) (hR : cR ≠ []) :
    gluedResponse cL ports cR = selector (portValues cL ports) * continuation (finish cR) := by
  rw [gluedResponse_eq_response cL ports cR hR, response_factorization]

/-- The number of simultaneous Boolean port states supplies the bound. -/
theorem gluedResponse_rank_le_states (cL : List (CGate a))
    (ports : Fin r → Fin cL.length) (cR : List (CGate (r + b))) (hR : cR ≠ []) :
    (gluedResponse cL ports cR).rank ≤ 2 ^ r := by
  rw [gluedResponse_eq_response cL ports cR hR]
  exact response_rank_le_states _ _

/-- The same circuit also factors through its complete left wire trace.
Repeating a port never creates additional left wires. -/
theorem gluedResponse_eq_full_trace (cL : List (CGate a))
    (ports : Fin r → Fin cL.length) (cR : List (CGate (r + b))) (hR : cR ≠ []) :
    gluedResponse cL ports cR = response (portValues cL id)
      (fun state y => finish cR (fun i => state (ports i)) y) := by
  rw [gluedResponse_eq_response cL ports cR hR]
  rfl

theorem gluedResponse_rank_le_left_wire_states (cL : List (CGate a))
    (ports : Fin r → Fin cL.length) (cR : List (CGate (r + b))) (hR : cR ≠ []) :
    (gluedResponse cL ports cR).rank ≤ 2 ^ cL.length := by
  rw [gluedResponse_eq_full_trace cL ports cR hR]
  exact response_rank_le_states _ _

/-- A proved logarithmic port bound would give polynomial response rank for
these actual circuits. That structural premise is not inferred from fan-in. -/
theorem gluedResponse_rank_le_power (cL : List (CGate a))
    (ports : Fin r → Fin cL.length) (cR : List (CGate (r + b))) (hR : cR ≠ [])
    (n c : ℕ) (hn : n ≠ 0) (hr : r ≤ c * Nat.log 2 n) :
    (gluedResponse cL ports cR).rank ≤ n ^ c := by
  rw [gluedResponse_eq_response cL ports cR hR]
  exact response_rank_le_power_of_logarithmic_ports _ _ n c hn hr

/-- What a q-dimensional minor actually forces at this Boolean cut. -/
theorem gluedResponse_rank_requires_bits (cL : List (CGate a))
    (ports : Fin r → Fin cL.length) (cR : List (CGate (r + b))) (hR : cR ≠ [])
    (q : ℕ) (hq : q ≤ (gluedResponse cL ports cR).rank) : Nat.clog 2 q ≤ r := by
  rw [gluedResponse_eq_response cL ports cR hR] at hq
  exact response_rank_requires_bits _ _ hq

end GodMoveGluedCircuitRank

#print axioms GodMoveGluedCircuitRank.gluedResponse_eq_response
#print axioms GodMoveGluedCircuitRank.gluedResponse_factorization
#print axioms GodMoveGluedCircuitRank.gluedResponse_rank_le_states
#print axioms GodMoveGluedCircuitRank.gluedResponse_eq_full_trace
#print axioms GodMoveGluedCircuitRank.gluedResponse_rank_le_left_wire_states
#print axioms GodMoveGluedCircuitRank.gluedResponse_rank_le_power
#print axioms GodMoveGluedCircuitRank.gluedResponse_rank_requires_bits
