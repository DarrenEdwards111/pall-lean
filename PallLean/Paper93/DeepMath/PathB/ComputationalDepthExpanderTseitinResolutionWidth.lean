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

/-- **BSW flip lemma.**  If `S` semantically implies clause `C` and is *minimal*
(no `S.erase v` implies `C`), then every boundary edge `e ∈ ∂S` is a variable of
`C` (some literal `(e, b) ∈ C`).  Proof: minimality gives an assignment `a`
satisfying `S \ {v}` (where `v` is `e`'s endpoint in `S`) but not `C`, hence not
`v`'s constraint; flipping `a` on `e` repairs `v`'s parity without disturbing the
rest of `S`, so the flipped assignment satisfies `S`, hence `C` — and the only
change was at `e`, so `C` must mention `e`. -/
theorem boundary_edge_mem_clause (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (C : ResolutionClause (TLit Edge)) (S : Finset V)
    (hS : SemanticMeasure.Implies TSat (TConstr G charge) S C)
    (hmin : ∀ v ∈ S, ¬ SemanticMeasure.Implies TSat (TConstr G charge) (S.erase v) C)
    {e : Edge} (he : e ∈ G.boundary S) :
    ∃ b, (e, b) ∈ C := by
  rw [TseitinGraph.boundary, Finset.mem_filter] at he
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp he.2
  have hmem : v ∈ G.endpoints e ∩ S := hv ▸ Finset.mem_singleton_self v
  have hve : v ∈ G.endpoints e := (Finset.mem_inter.mp hmem).1
  have hvS : v ∈ S := (Finset.mem_inter.mp hmem).2
  -- minimality: an assignment satisfying `S \ {v}` but not `C`
  have hm := hmin v hvS
  rw [SemanticMeasure.Implies] at hm
  push_neg at hm
  obtain ⟨a, ha_erase, ha_notC⟩ := hm
  -- it cannot satisfy `v`'s constraint (else it would satisfy `C`)
  have hvnot : ¬ TConstr G charge v a := by
    intro hcontra
    refine ha_notC (hS a (fun u hu => ?_))
    rcases eq_or_ne u v with h | h
    · exact h ▸ hcontra
    · exact ha_erase u (Finset.mem_erase.mpr ⟨h, hu⟩)
  -- flip `a` on `e`: repairs `v`, leaves the rest of `S` untouched
  set a' := Function.update a e (a e + 1) with ha'
  have ha'_all : ∀ u ∈ S, TConstr G charge u a' := by
    intro u hu
    rcases eq_or_ne u v with h | h
    · rw [h]
      have hc1 : G.constraint v e = 1 := by unfold TseitinGraph.constraint; rw [if_pos hve]
      have hpar : parity G a v = charge v + 1 := by
        have hzm : ∀ x y : ZMod 2, x ≠ y → x = y + 1 := by decide
        exact hzm _ _ hvnot
      have hzz : (1 : ZMod 2) + 1 = 0 := by decide
      simp only [TConstr, ha', parity_update, hc1, hpar]
      rw [add_assoc, hzz, add_zero]
    · have hune : u ∉ G.endpoints e := by
        intro hue
        have : u ∈ G.endpoints e ∩ S := Finset.mem_inter.mpr ⟨hue, hu⟩
        rw [hv] at this
        exact h (Finset.mem_singleton.mp this)
      have hc0 : G.constraint u e = 0 := by unfold TseitinGraph.constraint; rw [if_neg hune]
      simp only [TConstr, ha', parity_update, hc0, add_zero]
      exact ha_erase u (Finset.mem_erase.mpr ⟨h, hu⟩)
  -- the flipped assignment satisfies `C`; the only changed edge is `e`
  obtain ⟨l, hlC, hl⟩ := hS a' ha'_all
  rcases eq_or_ne l.1 e with hle | hle
  · exact ⟨l.2, by rw [← hle]; exact hlC⟩
  · exfalso
    refine ha_notC ⟨l, hlC, ?_⟩
    have hagree : a l.1 = a' l.1 := by rw [ha', Function.update_apply, if_neg hle]
    simp only [TSat] at hl ⊢
    rw [hagree]; exact hl

/-- The edge boundary of a minimal implying set injects into the clause (each
boundary edge is a variable), so `|∂S| ≤ width C`. -/
theorem boundary_card_le_width (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (C : ResolutionClause (TLit Edge)) (S : Finset V)
    (hS : SemanticMeasure.Implies TSat (TConstr G charge) S C)
    (hmin : ∀ v ∈ S, ¬ SemanticMeasure.Implies TSat (TConstr G charge) (S.erase v) C) :
    (G.boundary S).card ≤ ResolutionClause.width C := by
  classical
  have hsub : G.boundary S ⊆ C.image Prod.fst := by
    intro e he
    obtain ⟨b, hb⟩ := boundary_edge_mem_clause G charge C S hS hmin he
    exact Finset.mem_image.mpr ⟨(e, b), hb, rfl⟩
  calc (G.boundary S).card
      ≤ (C.image Prod.fst).card := Finset.card_le_card hsub
    _ ≤ C.card := Finset.card_image_le
    _ = ResolutionClause.width C := rfl

/-- **Expansion ⇒ width link** (`hwide`).  On an expander, every clause of medium
measure (`t ≤ μ C < 2t`, with `1 ≤ t` and `4t ≤ |V|`) has width `≥ c·t`.  The
minimal implying set has card `μ C ∈ [t,2t)`, its boundary injects into the
clause, and expansion bounds the boundary below by `c·μ C ≥ c·t`. -/
theorem width_ge_of_medium (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    {c t : ℕ} (hexp : G.HasExpansion c) (ht1 : 1 ≤ t) (hcard : 4 * t ≤ Fintype.card V)
    {C : ResolutionClause (TLit Edge)}
    (hlo : t ≤ SemanticMeasure.measure TSat (TConstr G charge) C)
    (hhi : SemanticMeasure.measure TSat (TConstr G charge) C < 2 * t) :
    c * t ≤ ResolutionClause.width C := by
  obtain ⟨S, hSimp, hScard⟩ :=
    SemanticMeasure.exists_implies_measure TSat (TConstr G charge) hunsat C
  have htS : t ≤ S.card := by rw [hScard]; exact hlo
  have hSpos : 1 ≤ S.card := le_trans ht1 htS
  have hShalf : 2 * S.card ≤ Fintype.card V := by
    have : S.card < 2 * t := by rw [hScard]; exact hhi
    omega
  have hmin : ∀ v ∈ S, ¬ SemanticMeasure.Implies TSat (TConstr G charge) (S.erase v) C := by
    intro v hv himp
    have hle := SemanticMeasure.measure_le_of_implies TSat (TConstr G charge) himp
    rw [Finset.card_erase_of_mem hv, hScard] at hle
    omega
  calc c * t ≤ c * S.card := by gcongr
    _ ≤ (G.boundary S).card := hexp S hSpos hShalf
    _ ≤ ResolutionClause.width C := boundary_card_le_width G charge C S hSimp hmin

end PallLean.Paper93.DeepMath.PathB.TseitinResolution
