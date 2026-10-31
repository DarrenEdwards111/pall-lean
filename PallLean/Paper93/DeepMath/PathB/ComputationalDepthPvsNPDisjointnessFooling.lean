import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPInteractiveCoupling

/-!
# Disjointness: the communication lower bound the fooling method is built for

Completing the communication trio:

* **Equality** — its matrix is the identity: the `2^n` diagonal ones are *both* a fooling set and a full-rank
  witness, so fooling and rank agree.
* **Inner product** — its (signed) matrix is Hadamard: full rank `2^n` but no transparent large fooling set, so
  only the algebraic-rank method delivers the bound.
* **Disjointness** `DISJ(x,y) = ⋀ᵢ ¬(xᵢ ∧ yᵢ)` — the mirror case: the **fooling** method gives the tight bound
  directly, through the classical **complement fooling set** `{(S, Sᶜ) : S ⊆ [n]}` of size `2^n`.

For disjointness the rectangle/fooling argument is exactly the natural tool: `DISJ(S, Sᶜ) = 1` (a set is
disjoint from its complement), while for `S ≠ T` at least one of the swaps `DISJ(S, Tᶜ)`, `DISJ(T, Sᶜ)` is `0`
(they equal `1` iff `S ⊆ T`, resp. `T ⊆ S`, and `S ⊆ T ∧ T ⊆ S ⇒ S = T`).  This reuses the interactive
coupling's `CommFooling`/`card_le_transcript` verbatim.

## Result

`disj_fooling_lower_bound : 2^n ≤ #transcripts` for any protocol computing `DISJ`, from the size-`2^n`
complement fooling set.

## Honest scope

Deterministic two-party communication complexity for disjointness, via the fooling-set method — the case that
the method is tight for.  It does **not** reach `P` (`DISJ ∈ P`; a `P`-time machine is not a bounded-
communication protocol).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDisjointnessFooling

open PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling

/-- **Set disjointness**: `x` and `y` (as subsets of `[n]`) share no element. -/
def DISJ (n : Nat) (x y : Fin n → Bool) : Bool := decide (∀ i, (x i && y i) = false)

/-- Pointwise complement of a subset. -/
def compl {n : Nat} (S : Fin n → Bool) : Fin n → Bool := fun i => !(S i)

/-- The **complement fooling set** `{(S, Sᶜ) : S}`. -/
def disjFooling (n : Nat) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  Finset.univ.image (fun S : Fin n → Bool => (S, compl S))

theorem disjFooling_card (n : Nat) : (disjFooling n).card = 2 ^ n := by
  rw [disjFooling,
    Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1),
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **The complement diagonal is a fooling set for `DISJ` with value `true`.** -/
theorem comm_fooling_DISJ (n : Nat) : CommFooling (DISJ n) true (disjFooling n) := by
  constructor
  · rintro ⟨a, b⟩ hx
    simp only [disjFooling, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨S, hS⟩ := hx
    rw [Prod.mk.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    simp only [DISJ, compl, decide_eq_true_eq]
    intro i
    cases S i <;> simp
  · rintro ⟨a₁, b₁⟩ hx ⟨a₂, b₂⟩ hy hne
    simp only [disjFooling, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨S, hS⟩ := hx
    obtain ⟨T, hT⟩ := hy
    rw [Prod.mk.injEq] at hS hT
    obtain ⟨rfl, rfl⟩ := hS
    obtain ⟨rfl, rfl⟩ := hT
    have hST : S ≠ T := fun h => hne (by rw [h])
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hST
    funext i
    simp only [DISJ, compl, decide_eq_true_eq] at h1 h2
    have e1 := h1 i
    have e2 := h2 i
    cases hs : S i <;> cases ht : T i <;> simp_all

/-- **Disjointness needs `2^n` transcripts.**  The complement fooling set has size `2^n`, and any protocol
computing `DISJ` has at least `|fooling set|` transcripts — the case where the fooling method is tight. -/
theorem disj_fooling_lower_bound (n : Nat) (P : CommProtocol n n)
    (hc : ∀ a b, P.eval a b = DISJ n a b) :
    2 ^ n ≤ @Fintype.card P.Transcript P.fintype := by
  have h := card_le_transcript P hc (comm_fooling_DISJ n)
  rwa [disjFooling_card] at h

/-- **Bounded-round / bounded-width corollary.**  A `rounds`-round width-`|State|` protocol for `DISJ` needs
`width ^ rounds ≥ 2^n`. -/
theorem disj_rounds_width_tradeoff (n rounds : Nat) (State : Type) [Fintype State]
    (P : CommProtocol n n) (hcard : @Fintype.card P.Transcript P.fintype = (Fintype.card State) ^ rounds)
    (hc : ∀ a b, P.eval a b = DISJ n a b) :
    2 ^ n ≤ (Fintype.card State) ^ rounds := by
  rw [← hcard]; exact disj_fooling_lower_bound n P hc

end PallLean.Paper93.DeepMath.PathB.PvsNPDisjointnessFooling

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDisjointnessFooling.disjFooling_card
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDisjointnessFooling.comm_fooling_DISJ
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDisjointnessFooling.disj_fooling_lower_bound
