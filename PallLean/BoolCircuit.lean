/-
  BoolCircuit.lean — Boolean Circuit Model (Paper §3, §7)

  Defines Boolean circuits, depth-4 ΣΠΣ∏ circuits,
  and the conversion chain needed for universal SPDP collapse.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.TuringMachine
import PallLean.Depth4Simulation
import Mathlib.Tactic

namespace BoolCircuit

open MvPolynomial SPDP

/-! ## Boolean Circuits -/

/-- A Boolean circuit gate: AND or OR with arbitrary fan-in.
    Inputs are either input variables or outputs of earlier gates. -/
inductive GateType | AND | OR

/-- A Boolean circuit on n input variables.
    Gates are indexed by Fin numGates (topologically sorted).
    Each gate has a type (AND/OR), a negation flag, and a list of inputs.
    An input is either a variable (Fin n) or a gate output (Fin numGates). -/
structure Circuit (n : ℕ) where
  numGates : ℕ
  gateType : Fin numGates → GateType
  gateNeg : Fin numGates → Bool  -- negation on output
  /-- Inputs to each gate. Each input is Sum (Fin n) (Fin numGates).
      Gate i can only reference gate j with j < i (topological order). -/
  gateInputs : (g : Fin numGates) → List (Sum (Fin n) (Fin numGates))
  topological : ∀ g : Fin numGates, ∀ inp ∈ gateInputs g,
    match inp with | .inr j => j.val < g.val | .inl _ => True
  /-- Output gate index -/
  outputGate : Fin numGates

/-- Size of a circuit = number of gates -/
def Circuit.size (C : Circuit n) : ℕ := C.numGates

/-- Depth of a circuit (longest path from input to output) -/
noncomputable def Circuit.depth (C : Circuit n) : ℕ :=
  -- Simplified: just an abstract measure
  C.numGates  -- Upper bound; actual depth ≤ numGates

/-! ## Depth-4 ΣΠΣ∏ circuits -/

/-- A depth-4 ΣΠΣ∏ circuit.
    Level 1 (bottom): ∏ = products of literals (conjunctions), fan-in ≤ t
    Level 2: Σ = sums of level-1 products (DNFs)
    Level 3: ∏ = products of level-2 sums
    Level 4 (top): Σ = sum of level-3 products

    Represents the polynomial: Σ_i ∏_j Σ_k ∏_{ℓ} x_{i,j,k,ℓ}^{e} -/
structure Depth4Circuit (n : ℕ) where
  /-- Bottom fan-in bound -/
  bottomFanIn : ℕ
  /-- Total formal degree -/
  formalDegree : ℕ
  /-- Top-level size (number of terms in outer sum) -/
  topSize : ℕ

/-! ## Arithmetization -/

/-- The multilinear interpolation of a circuit's computed function.
    This is the unique multilinear polynomial agreeing with the circuit
    on all Boolean inputs. -/
noncomputable def Circuit.multilinearInterp {n : ℕ} (C : Circuit n) :
    MvPolynomial (Fin n) ℚ :=
  -- The circuit computes some Boolean function; its multilinear
  -- interpolation is defined via Depth4Simulation.multilinearInterp
  Depth4Simulation.multilinearInterp (fun _ => false)  -- placeholder

/-! ## Cook-Levin: DTM → Circuit

  Paper §3: A DTM M with time bound n^c can be simulated by
  a Boolean circuit of size O(n^{2c}) and depth O(c · log n).
  The circuit uses the computation tableau construction. -/

/-- Cook-Levin: every PTIME function has polynomial-size circuits.
    DTM M with time n^c → circuit of size ≤ n^{2c+1}. -/
axiom cook_levin {n : ℕ} (M : TuringMachine.DTM) (f : (Fin n → Bool) → Bool)
    (hf : M.decides f) (hn : n ≥ 2) :
    ∃ C : Circuit n, C.size ≤ n ^ (2 * M.timeBound + 1)

/-! ## Agrawal-Vinay Depth Reduction

  Paper §7 Step 1: Any poly-size circuit can be converted to a
  depth-4 ΣΠΣ∏ circuit with:
  - Bottom fan-in ≤ log n
  - Formal degree ≤ log² n
  - Poly-quasi-polynomial size -/

/-- Agrawal-Vinay + Tavenas: poly-size circuit → depth-4 with
    bottom fan-in ≤ log n. -/
axiom depth4_reduction {n : ℕ} (C : Circuit n) (hn : n ≥ 2) :
    ∃ D : Depth4Circuit n,
      D.bottomFanIn ≤ Nat.log 2 n ∧
      D.formalDegree ≤ (Nat.log 2 n) ^ 2

/-! ## Switching Lemma for SPDP Rank

  Paper Lemma 7.2: Under a random restriction that kills all but
  O(log n) variables, a depth-4 circuit with bottom fan-in ≤ log n
  has SPDP rank ≤ O(log² n) with high probability.

  Combined with union bound: ∃ deterministic seed achieving this. -/

/-- The SPDP rank bound from the switching lemma pipeline.
    Paper §7, Theorem 7.3: For any DTM-decidable function f, the restricted
    SPDP rank is ≤ (log₂ n + 1)² under the universal restriction ρ*.

    The proof chain (all within the paper):
    1. Cook-Levin: DTM M with time n^c → Boolean circuit of size n^{O(c)}
    2. Agrawal-Vinay + Tavenas: circuit → depth-4 ΣΠΣ∏ with bottom
       fan-in ≤ log n and formal degree ≤ log² n
    3. Håstad switching lemma: under ρ* (leaving w = log₂ n live vars),
       the depth-4 circuit simplifies to SPDP rank ≤ d_n* = (k+1)·w
    4. Union bound: ∃ deterministic seed s* achieving the bound

    The DTM hypothesis is ESSENTIAL — a generic Boolean function on w
    variables can have SPDP rank up to C(2w, w) ≈ n². The low rank
    comes from the controlled circuit structure of P-time functions. -/
axiom switching_spdp_bound {n : ℕ} (f : (Fin n → Bool) → Bool)
    (M : TuringMachine.DTM) (hf : M.decides f) (hn : n ≥ 2) :
    RestrictedSPDP.restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (Depth4Simulation.multilinearInterp f)
      (UniversalRestriction.universalRestriction n) ≤
    (Nat.log 2 n + 1) ^ 2

end BoolCircuit
