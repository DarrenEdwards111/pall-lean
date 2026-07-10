import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Boundary-fooling width lower bound — the *de-socketed* rank argument

The MERA/holonomy files ruled out a bounded-rank decoder that **exactly recovers all `2^n` signatures**, then
tried to reach SAT through a `compile : DecidesSAT → Nonempty (decoder)` field.  That field is not merely
circular: exact recovery of an `n`-bit signature is a *recovery* task, whereas a SAT decider returns *one*
bit, so no SAT decider ever supplies it — the certified class is vacuous.

This file keeps the genuine core of that argument — *a deterministic boundary that must remember enough about
a prefix to answer every suffix needs at least as many states as the prefix has distinguishable behaviours* —
and makes it **constructive and non-vacuous**:

* `LayeredBoundaryDecider` is a concrete structure whose boundary state type is an explicit field (not an
  assumed `Nonempty`);
* `Fooling` is a real combinatorial fooling set;
* `card_ge_fooling` proves the width lower bound **by injectivity of the actual `mid` map** — no impossible
  object is postulated;
* `eqDecider` **exhibits a real decider**, so the model is non-vacuous (the socket's class was empty);
* `no_small_decider_for_EQ` is the genuine restricted lower bound.

## Honest scope

This is a classical **bounded-width / one-way-communication / OBDD-cut** lower bound for the equality function
`EQ`: any deterministic decider whose decision factors through a single prefix state needs `≥ 2^n` states to
compute `EQ` on `n+n` bits.  It is real, `sorry`-free mathematics and it is the correct *constructed* form of
the rank argument.

It is **not** a statement about SAT or `P` vs `NP`.  `EQ` is trivial for a general machine; the bound
constrains only the bounded-width model.  Reaching SAT this way would need an `OBDD`-hard *satisfiability*
sub-family — which the parity-CNF reduction does **not** provide (parity-CNF satisfiability is `⊕`, which has
width-`2` OBDDs).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB

/-- A deterministic decider whose answer on `(a, b)` factors through **one boundary state** `mid a`, read
after the prefix `a` and before the suffix `b`.  The boundary state type is a concrete field. -/
structure LayeredBoundaryDecider (p q : Nat) where
  State : Type
  fintype : Fintype State
  mid : (Fin p → Bool) → State
  finish : State → (Fin q → Bool) → Bool

namespace LayeredBoundaryDecider

/-- The decided value: read `a` into a boundary state, then answer `b`. -/
def eval {p q : Nat} (D : LayeredBoundaryDecider p q)
    (a : Fin p → Bool) (b : Fin q → Bool) : Bool :=
  D.finish (D.mid a) b

end LayeredBoundaryDecider

/-- A **fooling set** for `f` at the prefix cut: every two distinct prefixes in `S` are separated by some
suffix. -/
def Fooling {p q : Nat} (f : (Fin p → Bool) → (Fin q → Bool) → Bool)
    (S : Finset (Fin p → Bool)) : Prop :=
  ∀ a₁ ∈ S, ∀ a₂ ∈ S, a₁ ≠ a₂ → ∃ b, f a₁ b ≠ f a₂ b

/-- **The width lower bound (constructed).**  If `D` computes `f` and `S` is a fooling set for `f`, then the
`mid` map is injective on `S`, so `D` has at least `|S|` boundary states. -/
theorem card_ge_fooling {p q : Nat} (D : LayeredBoundaryDecider p q)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool)
    (hf : ∀ a b, D.eval a b = f a b)
    (S : Finset (Fin p → Bool)) (hS : Fooling f S) :
    S.card ≤ @Fintype.card D.State D.fintype := by
  letI := D.fintype
  have hinj : Set.InjOn D.mid ↑S := by
    intro a₁ h₁ a₂ h₂ hmid
    by_contra hne
    obtain ⟨b, hb⟩ := hS a₁ h₁ a₂ h₂ hne
    apply hb
    have hev : D.eval a₁ b = D.eval a₂ b := by
      simp only [LayeredBoundaryDecider.eval, hmid]
    rw [hf a₁ b, hf a₂ b] at hev
    exact hev
  calc S.card ≤ (Finset.univ : Finset D.State).card :=
        Finset.card_le_card_of_injOn D.mid (fun a _ => Finset.mem_univ _) hinj
    _ = Fintype.card D.State := Finset.card_univ

/-! ## The equality function is fully fooling -/

/-- Equality of two `n`-bit strings. -/
def EQ (n : Nat) : (Fin n → Bool) → (Fin n → Bool) → Bool := fun a b => decide (a = b)

/-- **Every distinct pair of prefixes is separated:** the whole prefix cube is a fooling set for `EQ`. -/
theorem fooling_EQ (n : Nat) : Fooling (EQ n) Finset.univ := by
  intro a₁ _ a₂ _ hne
  exact ⟨a₁, by simp [EQ, Ne.symm hne]⟩

/-- **`EQ` needs `2^n` boundary states.** -/
theorem card_ge_two_pow_of_computes_EQ (n : Nat) (D : LayeredBoundaryDecider n n)
    (hf : ∀ a b, D.eval a b = EQ n a b) :
    2 ^ n ≤ @Fintype.card D.State D.fintype := by
  have h := card_ge_fooling D (EQ n) hf Finset.univ (fooling_EQ n)
  rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h

/-! ## Non-vacuity: a real decider exists (unlike the socket's empty class) -/

/-- A concrete decider that computes `EQ` with exactly `2^n` boundary states. -/
def eqDecider (n : Nat) : LayeredBoundaryDecider n n where
  State := Fin n → Bool
  fintype := inferInstance
  mid := id
  finish := fun a b => decide (a = b)

theorem eqDecider_computes (n : Nat) :
    ∀ a b, (eqDecider n).eval a b = EQ n a b := fun _ _ => rfl

theorem eqDecider_card (n : Nat) :
    @Fintype.card (eqDecider n).State (eqDecider n).fintype = 2 ^ n := by
  simp [eqDecider, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-! ## The genuine restricted lower bound -/

/-- **No sub-`2^n`-width decider computes `EQ`.**  Constructed, non-vacuous, non-circular: the boundary state
type is real, `eqDecider` witnesses that a `2^n`-state decider exists, and any strictly smaller one provably
fails on `EQ`. -/
theorem no_small_decider_for_EQ (n : Nat) (D : LayeredBoundaryDecider n n)
    (hsmall : @Fintype.card D.State D.fintype < 2 ^ n) :
    ¬ (∀ a b, D.eval a b = EQ n a b) :=
  fun hf => absurd (card_ge_two_pow_of_computes_EQ n D hf) (not_le.mpr hsmall)

/-- Class-level form: there is no bounded-width (`< 2^n`) decider for `EQ`. -/
theorem no_bounded_width_EQ_decider (n : Nat) :
    ¬ ∃ D : LayeredBoundaryDecider n n,
      @Fintype.card D.State D.fintype < 2 ^ n ∧ (∀ a b, D.eval a b = EQ n a b) := by
  rintro ⟨D, hsmall, hf⟩
  exact no_small_decider_for_EQ n D hsmall hf

end PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB.card_ge_fooling
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB.card_ge_two_pow_of_computes_EQ
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB.eqDecider_computes
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB.no_bounded_width_EQ_decider
