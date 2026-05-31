import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationExpSize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4SwitchingCore

/-!
# Rung 3 (toward depth-3): the collapse-under-restrictions interface + conditional bridge

**STATUS: REAL ΣΠΣ SYNTAX + HONEST CONDITIONAL BRIDGE.  THE COLLAPSE FIELD IS THE
OPEN GATE (Håstad-style switching), NOT A PROVED THEOREM.**

The completed BSW rung gives an exponential size lower bound for *resolution /
list-derivation* refutations of expander-Tseitin (`LDeriv.tseitin_size_lower`,
`LDeriv.tseitin_size_exp`).  The natural next rung is depth-3 circuits/proofs.
A genuine depth-3 lower bound needs a **new** ingredient — a switching/collapse
lemma showing that a depth-3 object simplifies, under restrictions, to a
width-small list-derivation object — which is *not* an extension of BSW.

Following the cautious plan, this file does **not** attempt that lemma.  Instead
it:

1. fixes a **real** ΣΠΣ depth-3 syntax (`Depth3.Circuit`) with Boolean semantics,
   size, and bottom width — so the substrate is genuine, not abstract;
2. states the **exact collapse hypothesis** as an interface
   (`Depth3CollapseModel`): every "refuting" circuit yields, after restrictions, a
   genuine `LDeriv` refutation of the Tseitin axioms of bounded length;
3. proves the **conditional bridge**: *given* the collapse hypothesis, the BSW
   rung forces the collapse bound (hence the circuit size) to be exponentially
   large.

**Honesty note.**  The interface per se proves nothing: it is satisfied trivially
(e.g. `Circuit := Empty`, or a huge `collapseLen`).  *All* the mathematical
content is in discharging `collapse` for a concrete depth-3 model with a small
`collapseLen` — that is precisely the switching lemma, and it is left open here.
This file establishes only the conditional implication and does **not** claim any
unconditional depth-3 lower bound (and nothing about P vs NP).
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

/-! ## A real ΣΠΣ depth-3 syntax (the substrate) -/

namespace Depth3

/-- Bottom level: an OR of literals. -/
structure Clause (n : ℕ) where
  lits : List (Rung4Literal n)

/-- Middle level: an AND of clauses. -/
structure Term (n : ℕ) where
  clauses : List (Clause n)

/-- Top level: an OR of terms.  A ΣΠΣ (OR–AND–OR) depth-3 circuit. -/
structure Circuit (n : ℕ) where
  terms : List (Term n)

/-- Evaluate a bottom clause as a disjunction of literals. -/
def Clause.eval {n : ℕ} (C : Clause n) (x : Fin n → Bool) : Bool :=
  C.lits.any (fun ℓ => ℓ.eval x)

/-- Evaluate a middle term as a conjunction of clauses. -/
def Term.eval {n : ℕ} (T : Term n) (x : Fin n → Bool) : Bool :=
  T.clauses.all (fun C => C.eval x)

/-- Evaluate the ΣΠΣ circuit as a disjunction of terms. -/
def Circuit.eval {n : ℕ} (D : Circuit n) (x : Fin n → Bool) : Bool :=
  D.terms.any (fun T => T.eval x)

/-- Bottom width of a clause (number of literal occurrences). -/
def Clause.width {n : ℕ} (C : Clause n) : ℕ := C.lits.length

/-- Bottom width of the circuit: the largest bottom clause. -/
def Circuit.bottomWidth {n : ℕ} (D : Circuit n) : ℕ :=
  (D.terms.flatMap (fun T => T.clauses.map Clause.width)).foldr max 0

/-- Size of the circuit: total literal occurrences across all bottom clauses. -/
def Circuit.size {n : ℕ} (D : Circuit n) : ℕ :=
  (D.terms.flatMap (fun T => T.clauses.map Clause.width)).sum

end Depth3

/-! ## The collapse-under-restrictions interface

The model abstracts over the depth-3 object type and over what "refutes the
Tseitin instance" means, and packages the Tseitin axioms together with the
**collapse hypothesis** as a structure field.  Discharging that field is the open
switching/collapse lemma. -/

/-- **Depth-3 collapse model for an expander-Tseitin instance.**  A class of
depth-3 objects together with the hypothesis that any refuting object collapses
(under restrictions) to a genuine `LDeriv` refutation of the Tseitin axioms of
bounded length.  The `collapse` field is the open gate (the switching lemma). -/
structure Depth3CollapseModel {V Edge : Type*} [Fintype V] [DecidableEq V]
    [Fintype Edge] [DecidableEq Edge] [Nonempty Edge]
    (G : TseitinGraph V Edge) (charge : V → ZMod 2) where
  /-- The class of depth-3 objects (e.g. `Depth3.Circuit _`). -/
  Circuit : Type
  /-- A size measure on the objects. -/
  size : Circuit → ℕ
  /-- What it means for an object to refute the Tseitin instance. -/
  Refutes : Circuit → Prop
  /-- The Tseitin axioms as an explicit clause list. -/
  Ax : List (ResolutionClause (TLit Edge))
  /-- Each axiom is implied by a single vertex constraint (genuine Tseitin CNF). -/
  hAxiom : ∀ C, C ∈ Ax → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C
  /-- An upper bound on axiom widths. -/
  w₀ : ℕ
  hw0 : ∀ C, C ∈ Ax → ResolutionClause.width C ≤ w₀
  /-- The collapsed-refutation length bound as a function of object size. -/
  collapseLen : ℕ → ℕ
  /-- **THE OPEN GATE.**  Every refuting object collapses to a genuine list-derivation
  refutation of the Tseitin axioms of length `≤ collapseLen (size D)`. -/
  collapse : ∀ D : Circuit, Refutes D →
    ∃ L, LDeriv tcompl (· ∈ Ax) L ∧ (∅ : ResolutionClause (TLit Edge)) ∈ L ∧
      L.length ≤ collapseLen (size D)

namespace Depth3CollapseModel

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
  [Nonempty Edge] {G : TseitinGraph V Edge} {charge : V → ZMod 2}

/-- **Conditional bridge (length form).**  *Given* the collapse hypothesis, the BSW
size lower bound forces the collapse bound: `n^b ≤ (n-d)^b · collapseLen (size D)`
whenever the width budget `w₀ + d + b` stays below the expander lower bound `c·t`. -/
theorem size_lower_length (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (M : Depth3CollapseModel G charge)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {d b : ℕ} (hd : 0 < d) (hsmall : M.w₀ + d + b < c * t)
    (D : M.Circuit) (hD : M.Refutes D) :
    Fintype.card (TLit Edge) ^ b
      ≤ (Fintype.card (TLit Edge) - d) ^ b * M.collapseLen (M.size D) := by
  obtain ⟨L, hLD, hmt, hlen⟩ := M.collapse D hD
  calc Fintype.card (TLit Edge) ^ b
      ≤ (Fintype.card (TLit Edge) - d) ^ b * L.length :=
        LDeriv.tseitin_size_lower G charge hunsat M.Ax M.hAxiom hc hexp ht2 hcard M.hw0 hd hLD hmt
          hsmall
    _ ≤ (Fintype.card (TLit Edge) - d) ^ b * M.collapseLen (M.size D) :=
        Nat.mul_le_mul_left _ hlen

/-- **Conditional bridge (explicit exponential).**  *Given* the collapse hypothesis,
the collapse bound is exponentially large: `2^j ≤ collapseLen (size D)` whenever the
doubling condition `n-d ≤ k·d` holds and `w₀ + d + k·j < c·t`.  If the model's
`collapseLen` is at most polynomial, this is an exponential lower bound on circuit
size. -/
theorem size_lower_exp (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (M : Depth3CollapseModel G charge)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {d k j : ℕ} (hd : 0 < d) (hk1 : 1 ≤ k)
    (hdn : d < Fintype.card (TLit Edge))
    (hkd : Fintype.card (TLit Edge) - d ≤ k * d)
    (hsmall : M.w₀ + d + k * j < c * t)
    (D : M.Circuit) (hD : M.Refutes D) :
    2 ^ j ≤ M.collapseLen (M.size D) := by
  obtain ⟨L, hLD, hmt, hlen⟩ := M.collapse D hD
  exact le_trans
    (LDeriv.tseitin_size_exp G charge hunsat M.Ax M.hAxiom hc hexp ht2 hcard M.hw0 hd hk1 hdn hkd
      hLD hmt hsmall)
    hlen

/-- **Specialisation: identity-bounded collapse.**  If the collapse does not blow up
the refutation length beyond the object size (`collapseLen n ≤ n`), the conditional
bridge yields an exponential lower bound directly on the object size:
`2^j ≤ size D`. -/
theorem size_lower_exp_of_le_id (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (M : Depth3CollapseModel G charge) (hlen_id : ∀ s, M.collapseLen s ≤ s)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {d k j : ℕ} (hd : 0 < d) (hk1 : 1 ≤ k)
    (hdn : d < Fintype.card (TLit Edge))
    (hkd : Fintype.card (TLit Edge) - d ≤ k * d)
    (hsmall : M.w₀ + d + k * j < c * t)
    (D : M.Circuit) (hD : M.Refutes D) :
    2 ^ j ≤ M.size D :=
  le_trans (size_lower_exp hunsat M hc hexp ht2 hcard hd hk1 hdn hkd hsmall D hD)
    (hlen_id (M.size D))

end Depth3CollapseModel

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3CollapseModel.size_lower_length
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3CollapseModel.size_lower_exp
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3CollapseModel.size_lower_exp_of_le_id
