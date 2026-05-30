import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionSemanticMeasure
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinWidthKernel

/-!
# Expander-Tseitin resolution width (2): the expansion → width link

The Tseitin instantiation of the generic semantic measure, and the
Ben-Sasson–Wigderson **flip argument**: for a *minimal* set `S` of vertex
constraints semantically implying a clause `C`, every boundary edge of `S` is a
variable of `C`.  Hence `width C ≥ |∂S| ≥ c·|S| = c·μ(C)` (expansion), which
supplies the `hwide` hypothesis of `proofWidth_ge_of_medium_wide`.

Tseitin semantics: assignments are `Edge → ZMod 2`; a literal `(e,b)` asserts
`x_e = b`; the constraint at vertex `v` is the parity `⊕_{e ∋ v} x_e = charge v`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinResolution

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- A Tseitin literal: `(e, b)` asserts `x_e = b`. -/
abbrev TLit (Edge : Type*) := Edge × ZMod 2

/-- Satisfaction: assignment `a` satisfies literal `(e,b)` iff `a e = b`. -/
def TSat (a : Edge → ZMod 2) (l : TLit Edge) : Prop := a l.1 = l.2

/-- Complement of a literal: flip the asserted value. -/
def tcompl (l : TLit Edge) : TLit Edge := (l.1, l.2 + 1)

/-- The F₂ parity at vertex `v` under assignment `a`: `⊕_{e ∋ v} a e`. -/
def parity (G : TseitinGraph V Edge) (a : Edge → ZMod 2) (v : V) : ZMod 2 :=
  ∑ e, G.constraint v e * a e

/-- The Tseitin constraint at `v`: the parity equals the charge. -/
def TConstr (G : TseitinGraph V Edge) (charge : V → ZMod 2) (v : V) (a : Edge → ZMod 2) : Prop :=
  parity G a v = charge v

/-- Literal-complement consistency: a literal and its complement are never both
satisfied (`a e = b` and `a e = b+1` is impossible in `ZMod 2`). -/
theorem tsat_tcompl (a : Edge → ZMod 2) (l : TLit Edge) :
    TSat a l → ¬ TSat a (tcompl l) := by
  intro h hc
  simp only [TSat, tcompl] at h hc
  rw [h] at hc
  have hne : ∀ x : ZMod 2, x ≠ x + 1 := by decide
  exact hne l.2 hc

/-- **Single-edge flip and parity.**  Flipping the value of one edge `e` changes
the parity at `v` by exactly `constraint v e` (i.e. by `1` iff `e` is incident to
`v`). -/
theorem parity_update (G : TseitinGraph V Edge) (a : Edge → ZMod 2) (e : Edge) (v : V) :
    parity G (Function.update a e (a e + 1)) v = parity G a v + G.constraint v e := by
  unfold parity
  have key : ∀ e', G.constraint v e' * (Function.update a e (a e + 1)) e'
      = G.constraint v e' * a e' + (if e' = e then G.constraint v e' else 0) := by
    intro e'
    rw [Function.update_apply]
    by_cases h : e' = e
    · subst h; simp; ring
    · simp [h]
  rw [Finset.sum_congr rfl (fun e' _ => key e'), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ e (fun e' => G.constraint v e')]
  simp

end PallLean.Paper93.DeepMath.PathB.TseitinResolution
