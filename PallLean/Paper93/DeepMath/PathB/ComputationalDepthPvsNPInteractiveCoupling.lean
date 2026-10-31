import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPMultiPassCoupling

/-!
# Interactive (two-way) coupling: the rectangle/fooling lower bound

The one-way multi-pass model let each crossing state depend only on the prefix.  A *faithful* multi-pass
machine may, on later passes, carry state that depends on suffix information gathered on earlier passes — this
is exactly a **two-way deterministic communication protocol**.  Its transcript is an alternating message
sequence, and the defining structural fact is the **rectangle property**: the set of inputs producing a given
transcript is a combinatorial rectangle.

This file formalises that model (`CommProtocol`, with the rectangle property as its defining field) and proves
the standard **fooling-set communication lower bound**: a communication fooling set of size `F` forces at least
`F` distinct transcripts.  For the concrete `equalityCNF` SAT family the diagonal is a fooling set of size
`2^n`, so any protocol deciding it has `≥ 2^n` transcripts — hence for a bounded-round, bounded-width protocol
`width ^ rounds ≥ 2^n`.

The interactive bound *subsumes* the one-way multi-pass bound (any adaptive pass structure is a protocol), and
`eqProtocol` witnesses that the model is non-vacuous (a concrete protocol with the rectangle property).

## Honest scope

This is deterministic **two-way communication complexity** for `equalityCNF`-SAT — a genuine, faithful,
interactive strengthening of the streaming bound.  It still does **not** reach `P`.  A `P`-time algorithm is
*not* a bounded-communication protocol: with random access, polynomially many adaptive passes, and polynomial
workspace it has communication `≥ n` available for free, so `width ^ rounds ≥ 2^n` is satisfied trivially.
`EQ ∈ P` already; the bound constrains only the *communication/round/width* resource, not *time*.  Not
`SAT ∉ P`, not `P ≠ NP`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling

open PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPMultiPassCoupling
open SATDepthMachine

/-- A deterministic two-way communication protocol on split input `(a, b)`.  `rectangle` is the defining
structural property: equal transcripts on `(a₁,b₁)` and `(a₂,b₂)` force the same transcript on the swapped
pair `(a₁,b₂)` — i.e. transcript classes are combinatorial rectangles.  `out` reads the decision off the
transcript. -/
structure CommProtocol (p q : Nat) where
  Transcript : Type
  fintype : Fintype Transcript
  transcript : (Fin p → Bool) → (Fin q → Bool) → Transcript
  rectangle : ∀ a₁ a₂ b₁ b₂,
    transcript a₁ b₁ = transcript a₂ b₂ → transcript a₁ b₂ = transcript a₁ b₁
  out : Transcript → Bool

namespace CommProtocol

/-- The decided value: read the decision off the transcript. -/
def eval {p q : Nat} (P : CommProtocol p q) (a : Fin p → Bool) (b : Fin q → Bool) : Bool :=
  P.out (P.transcript a b)

end CommProtocol

/-- A **communication fooling set** for `f` with value `v`: every element has value `v`, and any two distinct
elements are separated by a swap (the hallmark that forces many rectangles). -/
def CommFooling {p q : Nat} (f : (Fin p → Bool) → (Fin q → Bool) → Bool) (v : Bool)
    (S : Finset ((Fin p → Bool) × (Fin q → Bool))) : Prop :=
  (∀ x ∈ S, f x.1 x.2 = v) ∧
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x.1 y.2 ≠ v ∨ f y.1 x.2 ≠ v)

/-- **The interactive coupling.**  On a communication fooling set the transcript map is injective: two distinct
fooling elements cannot share a transcript, because the rectangle property would then force both swapped
values to be `v`, contradicting the fooling separation. -/
theorem transcript_injOn {p q : Nat} (P : CommProtocol p q)
    {f : (Fin p → Bool) → (Fin q → Bool) → Bool} (hc : ∀ a b, P.eval a b = f a b)
    {v : Bool} {S : Finset ((Fin p → Bool) × (Fin q → Bool))} (hS : CommFooling f v S) :
    Set.InjOn (fun x : (Fin p → Bool) × (Fin q → Bool) => P.transcript x.1 x.2) (↑S) := by
  intro x hx y hy hTeq
  by_contra hne
  simp only [Finset.mem_coe] at hx hy
  have hr1 : P.transcript x.1 y.2 = P.transcript x.1 x.2 := P.rectangle x.1 y.1 x.2 y.2 hTeq
  have hr2 : P.transcript y.1 x.2 = P.transcript y.1 y.2 := P.rectangle y.1 x.1 y.2 x.2 hTeq.symm
  have hfxy : f x.1 y.2 = v := by
    have he : P.eval x.1 y.2 = P.eval x.1 x.2 := by simp only [CommProtocol.eval, hr1]
    rw [← hc x.1 y.2, he, hc x.1 x.2]; exact hS.1 x hx
  have hfyx : f y.1 x.2 = v := by
    have he : P.eval y.1 x.2 = P.eval y.1 y.2 := by simp only [CommProtocol.eval, hr2]
    rw [← hc y.1 x.2, he, hc y.1 y.2]; exact hS.1 y hy
  rcases hS.2 x hx y hy hne with h | h
  · exact h hfxy
  · exact h hfyx

/-- **Fooling-set communication lower bound.**  A protocol computing `f` has at least `|fooling set|` distinct
transcripts. -/
theorem card_le_transcript {p q : Nat} (P : CommProtocol p q)
    {f : (Fin p → Bool) → (Fin q → Bool) → Bool} (hc : ∀ a b, P.eval a b = f a b)
    {v : Bool} {S : Finset ((Fin p → Bool) × (Fin q → Bool))} (hS : CommFooling f v S) :
    S.card ≤ @Fintype.card P.Transcript P.fintype := by
  letI := P.fintype
  calc S.card ≤ (Finset.univ : Finset P.Transcript).card :=
        Finset.card_le_card_of_injOn (fun x => P.transcript x.1 x.2)
          (fun _ _ => Finset.mem_univ _) (transcript_injOn P hc hS)
    _ = Fintype.card P.Transcript := Finset.card_univ

/-! ## The equality diagonal is a communication fooling set of size `2^n` -/

/-- The diagonal `{(z, z)}`. -/
def eqDiagonal (n : Nat) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  Finset.univ.image (fun z => (z, z))

theorem eqDiagonal_card (n : Nat) : (eqDiagonal n).card = 2 ^ n := by
  rw [eqDiagonal, Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1),
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem comm_fooling_EQ (n : Nat) : CommFooling (EQ n) true (eqDiagonal n) := by
  constructor
  · rintro ⟨a, b⟩ hx
    simp only [eqDiagonal, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨z, hz⟩ := hx
    rw [← hz]; simp [EQ]
  · rintro ⟨a₁, b₁⟩ hx ⟨a₂, b₂⟩ hy hne
    simp only [eqDiagonal, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨z₁, hz₁⟩ := hx
    obtain ⟨z₂, hz₂⟩ := hy
    rw [Prod.mk.injEq] at hz₁ hz₂
    obtain ⟨rfl, rfl⟩ := hz₁
    obtain ⟨rfl, rfl⟩ := hz₂
    have hz : z₁ ≠ z₂ := fun h => hne (by rw [h])
    left; simp [EQ, hz]

/-- **Any protocol computing `EQ` needs `2^n` transcripts.** -/
theorem eq_needs_two_pow_transcripts (n : Nat) (P : CommProtocol n n)
    (hc : ∀ a b, P.eval a b = EQ n a b) :
    2 ^ n ≤ @Fintype.card P.Transcript P.fintype := by
  have h := card_le_transcript P hc (comm_fooling_EQ n)
  rwa [eqDiagonal_card] at h

/-- **Interactive SAT lower bound.**  Any two-way protocol deciding the `equalityCNF` SAT family has at least
`2^n` transcripts. -/
theorem equalitySAT_interactive_lower_bound (n : Nat) (P : CommProtocol n n)
    (hSAT : ∀ a b, P.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    2 ^ n ≤ @Fintype.card P.Transcript P.fintype :=
  eq_needs_two_pow_transcripts n P (eval_eq_EQ_of_satIff P.eval hSAT)

/-- **Bounded-round / bounded-width corollary.**  If the transcript is a `rounds`-tuple of width-`|State|`
messages, then `width ^ rounds ≥ 2^n`. -/
theorem equalitySAT_rounds_width_tradeoff (n rounds : Nat) (State : Type) [Fintype State]
    (P : CommProtocol n n) (hT : P.Transcript = (Fin rounds → State))
    (hcard : @Fintype.card P.Transcript P.fintype = (Fintype.card State) ^ rounds)
    (hSAT : ∀ a b, P.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    2 ^ n ≤ (Fintype.card State) ^ rounds := by
  rw [← hcard]; exact equalitySAT_interactive_lower_bound n P hSAT

/-! ## Non-vacuity: a concrete protocol with the rectangle property -/

/-- The honest equality protocol: Alice sends `a`; Bob appends the decision bit.  The transcript is
`(a, decide (a = b))`, and its rectangle property holds. -/
def eqProtocol (n : Nat) : CommProtocol n n where
  Transcript := (Fin n → Bool) × Bool
  fintype := inferInstance
  transcript := fun a b => (a, decide (a = b))
  rectangle := by
    intro a₁ a₂ b₁ b₂ h
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, hbit⟩ := h
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [decide_eq_decide] at hbit ⊢
    rw [hbit]
  out := Prod.snd

theorem eqProtocol_computes (n : Nat) : ∀ a b, (eqProtocol n).eval a b = EQ n a b :=
  fun _ _ => rfl

end PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling.transcript_injOn
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling.eq_needs_two_pow_transcripts
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling.equalitySAT_interactive_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling.eqProtocol_computes
