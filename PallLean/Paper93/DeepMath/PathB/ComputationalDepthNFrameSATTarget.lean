import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDispatchMux

/-!
# N-Frame: the definite SAT target (mountain-path step 1)

HAL's step 1: fix the exact target — a definite encoding, a definite size parameter, one definite `Prop`.  This file
supplies it: a fixed 3-CNF encoding as a concrete Boolean family `sat3Family`, and **the** target
`sat3Target := NFrameCircuitLowerBoundTarget sat3Family`.

**The encoding** (arity `N`): `v := √N` variables, clause width `D := 3(v+1)` bits, `m := N/D` clauses (trailing bits
ignored).  A literal slot is `v` selector bits plus a sign bit; a literal evaluates on assignment `a` as
`⋁ᵢ (selᵢ ∧ (aᵢ ⊕ sign))`; a clause is the OR of its 3 slots; the instance is the AND of its clauses;
`sat3Family N x = true` iff some assignment satisfies the encoded instance.

  `sat3Bit` — the fixed bit layout (index lemma proved).
  `sat3Family` — the family, total and decidable by construction.
  `sat3Family_iff` / `sat3Family_of_witness` — **PROVED**: the family means exactly satisfiability of the encoding.
  `sat3Target` — **the mountain, as one definite `Prop`**: `∀ k, ∃ N, Nᵏ + k < cbudget (sat3Family N)`.
  `sat3Target_no_decider` — **PROVED**: the conditional theorem instantiated at the definite target.

## Honest scope

The encoding choices (√N variables, selector-vector literals) are for formal definiteness; any polynomially equivalent
encoding yields a polynomially equivalent target.  `sat3Target` is open — it *is* the super-polynomial circuit lower
bound.  Nothing here proves it; this file only removes the last schematic freedom from its statement.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The number of variables at arity `N`. -/
def sat3V (N : ℕ) : ℕ := Nat.sqrt N

/-- The clause width in bits: 3 slots of `v` selectors + sign. -/
def sat3D (N : ℕ) : ℕ := 3 * (sat3V N + 1)

/-- The number of clauses. -/
def sat3M (N : ℕ) : ℕ := N / sat3D N

theorem sat3Bit_lt (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    c.val * sat3D N + t.val * (sat3V N + 1) + f < N := by
  have h1 : t.val * (sat3V N + 1) + f < sat3D N := by
    have ht := t.isLt
    have h2 : t.val * (sat3V N + 1) ≤ 2 * (sat3V N + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    show t.val * (sat3V N + 1) + f < 3 * (sat3V N + 1)
    omega
  have h3 : c.val * sat3D N + (t.val * (sat3V N + 1) + f) < (c.val + 1) * sat3D N := by
    rw [Nat.succ_mul]
    omega
  have h4 : (c.val + 1) * sat3D N ≤ sat3M N * sat3D N :=
    Nat.mul_le_mul_right _ (by have := c.isLt; omega)
  have h5 : sat3M N * sat3D N ≤ N := Nat.div_mul_le_self N (sat3D N)
  omega

/-- The fixed bit layout: field `f` of literal slot `t` of clause `c` (fields `0..v−1` = selectors, field `v` = sign). -/
def sat3Bit (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) : Fin N :=
  ⟨c.val * sat3D N + t.val * (sat3V N + 1) + f, sat3Bit_lt N c t f hf⟩

/-- A literal slot's value on assignment `a`: `⋁ᵢ (selᵢ ∧ (aᵢ ⊕ sign))`. -/
def sat3Lit (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N)) (t : Fin 3) : Bool :=
  (List.finRange (sat3V N)).any fun i =>
    x (sat3Bit N c t i.val (by have := i.isLt; omega))
      && xor (a i) (x (sat3Bit N c t (sat3V N) (by omega)))

/-- The encoded instance's value on assignment `a`: AND of clauses, each the OR of its 3 slots. -/
def sat3Eval (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool) : Bool :=
  (List.finRange (sat3M N)).all fun c =>
    (List.finRange 3).any fun t => sat3Lit N x a c t

/-- **The definite SAT family**: `sat3Family N x = true` iff some assignment satisfies the instance encoded by `x`. -/
def sat3Family (N : ℕ) : (Fin N → Bool) → Bool :=
  fun x => @decide (∃ a : Fin (sat3V N) → Bool, sat3Eval N x a = true)
    Fintype.decidableExistsFintype

/-- **The family means satisfiability (proved).** -/
theorem sat3Family_iff (N : ℕ) (x : Fin N → Bool) :
    sat3Family N x = true ↔ ∃ a : Fin (sat3V N) → Bool, sat3Eval N x a = true := by
  unfold sat3Family
  constructor
  · exact of_decide_eq_true
  · exact fun h => decide_eq_true h

/-- **Witness direction (proved).** -/
theorem sat3Family_of_witness (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (ha : sat3Eval N x a = true) : sat3Family N x = true :=
  (sat3Family_iff N x).mpr ⟨a, ha⟩

/-- **THE MOUNTAIN, as one definite `Prop`**: the encoded 3-SAT family has super-polynomial circuit energy —
`∀ k, ∃ N, Nᵏ + k < cbudget (sat3Family N)`.  Open; equal in content to the general circuit lower bound. -/
def sat3Target : Prop := NFrameCircuitLowerBoundTarget sat3Family

/-- **The conditional theorem at the definite target (proved)**: `sat3Target` plus the (now TM/RAM-discharged)
simulation shape rules out every polynomial-time decider of the family. -/
theorem sat3Target_no_decider {M : Type*} (PolyTime decides : M → Prop)
    (simulation : ∀ m, PolyTime m → decides m → PolyCBudget sat3Family)
    (target : sat3Target) :
    ¬ ∃ m, PolyTime m ∧ decides m :=
  target_closes_bridge PolyTime decides sat3Family simulation target

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Bit_lt
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Family_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Target_no_decider
