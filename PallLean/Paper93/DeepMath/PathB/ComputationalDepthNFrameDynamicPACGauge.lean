import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameInterfacedTripleEngine

/-!
# N-Frame: the dynamic PAC/gauge layer — no-cancellation in cell language

HAL's Track C module 1+2, at honest strength.  This file is a **dictionary**, like the dynamic-SPDP
bridge: it packages the proved interfaced-cut theorems in the PAC/gauge ("positivity prevents
destructive interference") language of the global God-move programme, and it **names** the global
targets as explicit `Prop` definitions without claiming them.

The proved local layer (all restatements of finished theorems):

  `InterfacedFactorization` — the cut object: `f = op (g|_A, h|_B)` with shared interface `A ∩ B`.
  `CellCrossesCut` — a two-coordinate cell crosses when each coordinate is invisible to the opposite
        factor (`p ∉ B`, `q ∉ A`, either orientation) — the interface-blind crossing notion.
  `pac_no_cancellation_sign` — sign-pair cells cannot cross: `sat3_sign_pair_dodge` restated.
  `pac_no_cancellation_selector` — same-block and cross-block selector cells cannot **both** cross:
        `sat3_selector_pair_dodge` restated.
  `pac_sign_spread` — the sign-cell family globally forces alignment-or-`Ω(m)`-interface:
        `sat3_sign_alignment_or_interface` restated.

The named global targets (definitions, **not** theorems — nothing here asserts them):

  `Essential` — a coordinate the function actually reads.
  `GlobalPACInterfaceBound N` — HAL's `every_adversarial_cut_crosses_many_positive_cells` cash-out:
        every interfaced factorization with essential coordinates on **both** exclusive sides pays an
        `Ω(m)` interface.  The sign-graph dichotomy proves the sign-restricted instance; the full
        statement needs the remaining families lifted (mixed sign↔selector, pinned-selector, slot
        probes) and their cell-graph counting.

## On the expander/Ramanujan layer

The sign-cell graph is the complete graph minus one edge — **denser than any Ramanujan expander** — so
the sign-spread counting was done directly, with no expander abstraction.  An abstract
`CellExpander` layer earns its place only when a lifted family has a *sparse* cell graph; adding the
structure before a theorem needs it would be scaffolding, not mathematics (the lesson of the HM
socket).  No continuous amplituhedron geometry is formalized — motivation language only.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The dictionary: definitions -/

/-- An interfaced factorization: `f = op (g|_A, h|_B)`, shared interface `A ∩ B`. -/
def InterfacedFactorization {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A B : Finset (Fin n)) (op : Bool → Bool → Bool)
    (g h : (Fin n → Bool) → Bool) : Prop :=
  (∀ x y : Fin n → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y) ∧
  (∀ x y : Fin n → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y) ∧
  (∀ x, f x = op (g x) (h x))

/-- A two-coordinate cell crosses the cut when each coordinate is invisible to the opposite factor —
either orientation.  This is the interface-blind crossing notion: `A ∩ B` plays no role. -/
def CellCrossesCut {n : ℕ} (A B : Finset (Fin n)) (p q : Fin n) : Prop :=
  (p ∉ B ∧ q ∉ A) ∨ (q ∉ B ∧ p ∉ A)

/-- A coordinate the function actually reads. -/
def Essential {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!(x i)))

/-! ### The proved local PAC layer -/

/-- **PAC NO-CANCELLATION, SIGN CELLS (proved)**: no sign-pair cell crosses an interfaced
factorization of SAT — fragmentation cannot cancel it. -/
theorem pac_no_cancellation_sign (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hfac : InterfacedFactorization (sat3Family N) A B op g h)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) :
    ¬ CellCrossesCut A B
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      (sat3SignBit N cIdx) := by
  obtain ⟨hg, hh, hf⟩ := hfac
  exact sat3_sign_pair_dodge N hv hm3 hk op g h A B hg hh hf cIdx j₀

/-- **PAC NO-CANCELLATION, SELECTOR CELLS (proved)**: a same-block and a cross-block selector cell
cannot both cross an interfaced factorization of SAT. -/
theorem pac_no_cancellation_selector (N : ℕ) (hv : 1 ≤ sat3V N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hfac : InterfacedFactorization (sat3Family N) A B op g h)
    (c : Fin (sat3M N)) (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N))
    (hne : sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)
      ≠ sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
    (c₁ c₂ : Fin (sat3M N)) (hc : c₁.val ≠ c₂.val)
    (t₃ t₄ : Fin 3) (j₃ j₄ : Fin (sat3V N)) :
    ¬ (CellCrossesCut A B
        (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega))
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
      ∧ CellCrossesCut A B
        (sat3Bit N c₁ t₃ j₃.val (by have := j₃.isLt; omega))
        (sat3Bit N c₂ t₄ j₄.val (by have := j₄.isLt; omega))) := by
  obtain ⟨hg, hh, hf⟩ := hfac
  exact sat3_selector_pair_dodge N hv op g h A B hg hh hf
    c t₁ t₂ j₁ j₂ hne c₁ c₂ hc t₃ t₄ j₃ j₄

/-- **PAC SIGN SPREAD (proved)**: the sign-cell family globally forces alignment or an `Ω(m)`
interface — the sign-restricted instance of the global PAC bound. -/
theorem pac_sign_spread (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hfac : InterfacedFactorization (sat3Family N) A B op g h) :
    (∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ A \ B) ∨
    (∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ B \ A) ∨
    sat3M N ≤ (A ∩ B).card + 4 := by
  obtain ⟨hg, hh, hf⟩ := hfac
  exact sat3_sign_alignment_or_interface N hv hm3 hk op g h A B hg hh hf

/-! ### The named global targets — definitions only, not claimed -/

/-- **THE GLOBAL PAC TARGET (named, NOT proved)**: every interfaced factorization of SAT with
essential coordinates on both exclusive sides pays an `Ω(m)` interface.  This is HAL's
`every_adversarial_cut_crosses_many_positive_cells` cash-out; proving it is the lift of the whole
Track A residual chain plus cell-graph counting.  The sign-restricted instance is `pac_sign_spread`. -/
def GlobalPACInterfaceBound (N : ℕ) : Prop :=
  ∀ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N)),
    InterfacedFactorization (sat3Family N) A B op g h →
    (∃ p : Fin N, Essential (sat3Family N) p ∧ p ∈ A \ B) →
    (∃ q : Fin N, Essential (sat3Family N) q ∧ q ∈ B \ A) →
    sat3M N ≤ 8 * ((A ∩ B).card + 1)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.pac_no_cancellation_sign
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.pac_no_cancellation_selector
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.pac_sign_spread
