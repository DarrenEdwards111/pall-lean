import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Entering the superpolynomial regime — honestly: Shannon's counting lower bound

Every *explicit* lower bound in the corpus is polynomial (Khrapchenko `n²`, Andreev `n^{5/2}`).  The one
place a **superpolynomial general-circuit lower bound is unconditionally provable** is Shannon's counting
argument: there are `2^(2^n)` Boolean functions on `n` bits but only `2^L` descriptions of `L` bits, so if
`L < 2^n` some function has no `L`-bit description — and since a polynomial-size circuit is describable in
polynomially many bits `≪ 2^n`, that function requires *superpolynomial* circuits.

This is a real entry into the superpolynomial regime.  Its cost is stated exactly: the witness is
**non-explicit** (produced by pigeonhole, not named).  The wall — `P ≠ NP` — needs an *explicit* hard
function *in NP*; Shannon gives hardness without explicitness.

## What is proved

* **`exists_hard`** — a pigeonhole: if `card P < card F`, some `f : F` is missed by `decode : P → F`.
* **`card_functions`** — `card ((Fin n → Bool) → Bool) = 2^(2^n)`.
* **`shannon_hard`** — if `L < 2^n`, then for *any* decoder of `L`-bit descriptions some Boolean function
  is undescribable: `∃ f, ∀ p : Fin L → Bool, decode p ≠ f`.  A superpolynomial (indeed exponential)
  hardness statement, unconditional.

## Honest scope

A genuine superpolynomial general-circuit lower bound — the only kind provable unconditionally — with its
gap named exactly: **non-explicit**.  It enters the superpolynomial regime for real, and shows the wall
between here and `P ≠ NP` is *explicitness* (an NP witness), not the existence of hardness.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ShannonSuperpoly

/-- **Counting pigeonhole (proved).**  A map from a smaller finite type cannot be surjective, so some
target is missed. -/
theorem exists_hard {P F : Type*} [Fintype P] [Fintype F] (decode : P → F)
    (hcard : Fintype.card P < Fintype.card F) :
    ∃ f : F, ∀ p : P, decode p ≠ f := by
  by_contra h
  push_neg at h
  have hsurj : Function.Surjective decode := h
  have := Fintype.card_le_of_surjective decode hsurj
  omega

/-- **The number of Boolean functions on `n` bits is `2^(2^n)` (proved).** -/
theorem card_functions (n : ℕ) :
    Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **Shannon's counting lower bound (proved).**  If `L < 2^n`, then for every way of decoding `L`-bit
descriptions into Boolean functions, some function has no description — a superpolynomial hardness
statement.  (A poly-size circuit needs only `poly(n) ≪ 2^n` description bits, so the hard function
requires superpolynomial circuits.)  The witness is non-explicit: existence by pigeonhole. -/
theorem shannon_hard (n L : ℕ) (hL : L < 2 ^ n)
    (decode : (Fin L → Bool) → ((Fin n → Bool) → Bool)) :
    ∃ f : (Fin n → Bool) → Bool, ∀ p : (Fin L → Bool), decode p ≠ f := by
  apply exists_hard decode
  rw [card_functions]
  have hP : Fintype.card (Fin L → Bool) = 2 ^ L := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hP]
  exact Nat.pow_lt_pow_right (by norm_num) hL

end PallLean.Paper93.DeepMath.PathB.ShannonSuperpoly

#print axioms PallLean.Paper93.DeepMath.PathB.ShannonSuperpoly.shannon_hard
