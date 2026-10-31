import Mathlib.Data.Nat.Basic

/-!
# Entanglement as a mass-production certificate: two notions, opposite directions

The one open mechanism is unbounded sharing = Uhlig mass production.  A **clean certificate** that a batch
*cannot* be mass-produced is exactly what a proof needs, and Darren proposes **entanglement**.  It is the
right instinct — but "entanglement" splits into two notions that point *opposite* ways, and only one is
the certificate.

## Two notions

* **Correlation / classical redundancy** (the copies are the *same*, or strongly correlated).  This is
  what mass production **exploits**: identical copies are computed once and fanned out.  Correlation is the
  *damping*, not a barrier to it — the wrong polarity for a certificate.  (Cf. `EntanglementNoChannel`:
  correlation is not a communication channel; here it is worse — it is a *sharing enabler*.)
* **Genuine non-separability** (the `k`-copy problem does not *factor* — no product structure a shared
  sub-circuit could exploit).  This is the right shape: non-separable ⟹ superadditive cost ⟹ no sharing
  saving.  But — proved below — a non-separability certificate is *logically equivalent* to "no
  flattening" itself.  It is the correct object; it is not a shortcut around the bound; it **is** the bound.

## What is proved

* **`correlation_is_the_damping`** — perfect correlation flattens: two identical copies cost `single + 2`
  (compute once, fan out), which beats `2·single` once `single ≥ 3`.  Naive "entanglement = correlation"
  is the *mechanism* of mass production, not a certificate against it.
* **`entanglement_rules_out_mass_production`** — a genuine non-separability certificate (`Entangled`: a
  valid, superadditive lower bound) does rule it out: `¬ MassProduces`.  Right shape.
* **`entanglement_iff_no_flattening`** — the catch, both directions: such a certificate exists **iff**
  `∀ k, k·single ≤ batch k`, i.e. iff there is no mass production.  So "SAT's tower is entangled" is not a
  route *to* the bound; it *is* the bound.

## Honest scope — the certificate is intrinsic (the ReusePairTrap)

Entanglement is genuinely the right *kind* of certificate — a valid, superadditive, non-separable measure
— but that is precisely the **intrinsic** measure the `ReusePairTrap`/`LensTension` line already pinned:
every *concrete* lens caps (support at `n`, Khrapchenko at `n²`), and a count that both lower-bounds cost
and survives reuse must be intrinsic (like `kw`/`cbudget`).  Operational entanglement (correlation) fails
validity — it is the damping.  Structural entanglement (non-separability) is valid and superadditive, but
`entanglement_iff_no_flattening` shows it is *equivalent* to the very superadditivity we are trying to
prove.  So a genuine entanglement certificate for SAT's tower is exactly `cost_super`.  The instinct is
correct — the missing object is a certificate — but it is the intrinsic one, and proving SAT carries it is
the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementCertificate

/-- **Uhlig mass production** (flattening): the `k`-copy circuit undercuts `k` independent copies. -/
def MassProduces (batch : ℕ → ℕ) (single : ℕ) : Prop := ∃ k, batch k < k * single

/-- **Correlation is the damping (proved).**  Two *identical* (perfectly correlated) copies are computed
once and fanned out, costing `single + 2` (one computation, two output wires), which is *below* `2·single`
whenever `single ≥ 3`.  So classical correlation — the naive reading of "entanglement" — is exactly the
mechanism of mass production, not a certificate against it.  Wrong polarity. -/
theorem correlation_is_the_damping (single : ℕ) (hs : 3 ≤ single) :
    (single + 2) < 2 * single := by omega

/-- A **genuine entanglement (non-separability) certificate**: a measure `ent` that lower-bounds the batch
cost and is superadditive — each `k`-batch carries at least `k` copies' worth of irreducible content,
because it does not factor. -/
structure Entangled (batch : ℕ → ℕ) (single : ℕ) where
  /-- the non-separability measure -/
  ent : ℕ → ℕ
  /-- it lower-bounds cost (valid) -/
  valid : ∀ k, ent k ≤ batch k
  /-- non-separable ⟹ superadditive: no product structure to share -/
  superadd : ∀ k, k * single ≤ ent k

/-- **Genuine entanglement rules out mass production (proved).**  A non-separability certificate forces
`k · single ≤ batch k`, so no Uhlig saving: `¬ MassProduces`.  This is the *right shape* of certificate —
non-separability, not correlation. -/
theorem entanglement_rules_out_mass_production (batch : ℕ → ℕ) (single : ℕ)
    (E : Entangled batch single) : ¬ MassProduces batch single :=
  fun ⟨k, hk⟩ => absurd (le_trans (E.superadd k) (E.valid k)) (by omega)

/-- **The certificate IS the bound (proved, both directions).**  A genuine entanglement certificate exists
**iff** the batch is superadditive `∀ k, k·single ≤ batch k` — i.e. iff there is no mass production (take
`ent := batch` for the reverse direction).  So "SAT's tower is entangled" is not a route *to* the lower
bound; it *is* the lower bound.  Entanglement is the right object, and it is the wall, not a way around. -/
theorem entanglement_iff_no_flattening (batch : ℕ → ℕ) (single : ℕ) :
    Nonempty (Entangled batch single) ↔ (∀ k, k * single ≤ batch k) := by
  constructor
  · intro hE k
    cases hE with
    | intro E => exact le_trans (E.superadd k) (E.valid k)
  · intro h
    exact ⟨{ ent := batch, valid := fun k => Nat.le_refl _, superadd := h }⟩

end PallLean.Paper93.DeepMath.PathB.EntanglementCertificate

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementCertificate.correlation_is_the_damping
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementCertificate.entanglement_rules_out_mass_production
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementCertificate.entanglement_iff_no_flattening
