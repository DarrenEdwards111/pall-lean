import Mathlib.Data.Finset.Card

/-!
# The independently-incompressible certificate, in a restricted case

The certificate the wall actually needs is **not** correlation (that is the damping) but its opposite:
the copies must be *independently incompressible* — each carries its own irreducible cost, and there is no
shared structure to exploit, so the costs **add**.  Here we build exactly that, restricted, and — the key
point — we do **not** assume superadditivity: we **derive** it from two verifiable structural facts.

## The two facts that force additivity

Model each copy by a finite set of **witness gates** it must contain:

* **incompressibility (per copy):** each copy needs at least `single` witness gates — `single ≤ |wᵢ|`.
  (For a genuinely hard copy this is a real circuit lower bound: it cannot be compressed below `single`.)
* **independence (across copies):** the witness sets are **disjoint** — `w₁ ∩ w₂ = ∅`.  Disjoint input
  blocks leave no gate two copies could share; there is no correlation to exploit.

From these two, additivity is **forced**, not assumed: `|w₁ ∪ w₂| = |w₁| + |w₂| ≥ 2·single`, and since the
witness gates are all real gates of the batch circuit, `batch ≥ 2·single`.  No mass production.

## What is proved

* **`incompressible_pair_superadditive`** — disjoint witnesses + per-copy incompressibility ⟹
  `2·single ≤ batch`.  The additivity comes from `|w₁ ∪ w₂| = |w₁| + |w₂|` for disjoint sets — a theorem,
  not a hypothesis.
* **`incompressible_pair_no_mass_production`** — hence `¬ (batch < 2·single)`: the two-copy step cannot be
  flattened.  This is the independently-incompressible certificate, working.
* **`incompressibleWitness`** — non-vacuous: concrete disjoint witness sets `{0,1,2}`, `{3,4,5}` give a
  genuine instance (`single = 3`, `batch = 6`).

## Honest scope — the two inputs are exactly what SAT withholds

This is a real certificate, and it is genuinely stronger than the earlier lens version: superadditivity is
**derived**.  But it needs two inputs, and SAT's tower withholds both:

1. **the per-copy incompressibility `single ≤ |wᵢ|`** is itself a *circuit lower bound* for the base
   function — for a hard base that is exactly the thing we cannot prove (a small `cost_super` instance);
2. **disjointness** fails for SAT's tower, whose copies **share inputs** (composition feeds the same
   variables), so witness gates need not be disjoint.

So the independently-incompressible certificate is built and works **for disjoint copies of functions with
a known lower bound** — the read-once / bounded-sharing regime, exactly not-SAT.  It is the right object,
and it makes precise that a certificate for SAT needs a per-copy lower bound plus genuine independence —
both of which, for SAT's shared-input tower of a hard base, are `cost_super`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.IncompressibleCertificate

/-- The **independently-incompressible certificate** for a two-copy batch: each copy owns a set of witness
gates (`w₁`, `w₂`), the sets are disjoint (independence — no shared structure), each is large
(incompressibility — `single ≤ |wᵢ|`), and all witness gates are real gates of the batch (`valid`). -/
structure IncompressiblePair (batch single : ℕ) where
  /-- copy 1's witness gates -/
  w1 : Finset ℕ
  /-- copy 2's witness gates -/
  w2 : Finset ℕ
  /-- independence: the witnesses share nothing -/
  disjoint : w1 ∩ w2 = ∅
  /-- copy 1 is incompressible: it needs at least `single` witness gates -/
  hard1 : single ≤ w1.card
  /-- copy 2 is incompressible -/
  hard2 : single ≤ w2.card
  /-- the witness gates are all real gates of the batch circuit -/
  valid : (w1 ∪ w2).card ≤ batch

/-- **Independence + incompressibility force additivity (proved).**  For a two-copy batch with disjoint
witness sets, each of size `≥ single`, the batch cost is `≥ 2·single`.  Superadditivity is *derived* from
`|w₁ ∪ w₂| = |w₁| + |w₂|` (disjoint), not assumed. -/
theorem incompressible_pair_superadditive (batch single : ℕ)
    (C : IncompressiblePair batch single) : 2 * single ≤ batch := by
  have hcard : (C.w1 ∪ C.w2).card = C.w1.card + C.w2.card := by
    have h := Finset.card_union_add_card_inter C.w1 C.w2
    rw [C.disjoint, Finset.card_empty] at h
    omega
  calc 2 * single = single + single := by omega
    _ ≤ C.w1.card + C.w2.card := Nat.add_le_add C.hard1 C.hard2
    _ = (C.w1 ∪ C.w2).card := hcard.symm
    _ ≤ batch := C.valid

/-- **No flattening from the certificate (proved).**  The independently-incompressible two-copy batch
cannot be mass-produced: `¬ (batch < 2·single)`. -/
theorem incompressible_pair_no_mass_production (batch single : ℕ)
    (C : IncompressiblePair batch single) : ¬ (batch < 2 * single) := by
  have := incompressible_pair_superadditive batch single C
  omega

/-- **The certificate is non-vacuous (proved).**  Concrete disjoint witness sets `{0,1,2}` and `{3,4,5}`:
two copies, each incompressible with `single = 3`, batch `6` — additivity holds on the nose. -/
def incompressibleWitness : IncompressiblePair 6 3 where
  w1 := {0, 1, 2}
  w2 := {3, 4, 5}
  disjoint := by decide
  hard1 := by decide
  hard2 := by decide
  valid := by decide

end PallLean.Paper93.DeepMath.PathB.IncompressibleCertificate

#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCertificate.incompressible_pair_superadditive
#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCertificate.incompressible_pair_no_mass_production
