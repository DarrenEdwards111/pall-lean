import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConservedChargeSpec

/-!
# Does the N-Frame Lagrangian supply the conserved charge? Noether says which charge — and it splits

Darren's move: a Lagrangian with a symmetry yields a conserved charge (Noether), so the N-Frame action
`S = ∫(L_eff + L_H)` should *supply* the charge `Q` the spec needs.  Structurally that is exactly right —
a Lagrangian does give a conserved charge.  This file formalizes *which* charge, honestly.

By Noether the conserved charge splits along the action: `Q = Q_eff + Q_H`, the currents of the
Turing-computable `L_eff` and the hypercomputational `L_H`.  And the conserved-charge spec
(`ConservedChargeSpec`) forces the charge to be **non-natural** (`charge_forces_non_natural`).  So:

* if the charge is **purely `L_eff`** (`Q_H = 0`), it is efficiently computable — a natural property —
  and the barrier kills it;
* therefore a valid charge must have **`Q_H ≠ 0`** — it must draw on the hypercomputational `L_H`, which
  is outside the standard model where P vs NP is defined.

* **`noether_charge_needs_hyper` (proved)** — exactly this: under the barrier + crypto, if the charge
  decomposes as `Q_eff + Q_H` with `Q_eff` efficient, then `Q_H` is **not** identically zero.  The
  N-Frame conserved charge must use `L_H`.

## Honest scope

So yes — the N-Frame Lagrangian fits the *shape*: Noether gives it a conserved charge.  But its
computable current `L_eff` is barriered (natural proofs) and its non-natural current `L_H` is
hypercomputational (outside the model).  Neither is the in-model, non-natural charge the spec demands —
the spec wants a charge that is non-natural yet still *standard-model* (like the `Classical` indicator:
non-constructive but in-model), and the Lagrangian's non-natural offering *overshoots* into
hypercomputation.  This is the `LagrangianDilemma` (`ca7f5764`), now read as Noether's theorem for the
conserved charge.  Nothing here supplies `Q`, and nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargeNoether

open PallLean.Paper93.DeepMath.PathB.ConservedChargeSpec

variable {Fn Rep : Type} {computes : Rep → Fn → Prop} {rrank : Rep → ℕ}
  {Easy : Fn → Prop} {sat : Fn}

/-- **Noether's theorem for the conserved charge (proved).**  Split the N-Frame charge along the action,
`Q = Q_eff + Q_H` (currents of `L_eff` and `L_H`).  If the computable current `Q_eff` is efficient and
the whole charge meets the spec, then under the barrier the hypercomputational current `Q_H` is **not**
identically zero: the charge must draw on `L_H`.  A purely-`L_eff` (computable) conserved charge is
barriered. -/
theorem noether_charge_needs_hyper {Efficient : (Fn → ℕ) → Prop} {Crypto : Prop}
    (barrier : ChargeBarrier Fn Rep computes rrank Easy sat Efficient Crypto) (hC : Crypto)
    (cc : ConservedCharge Fn Rep computes rrank Easy sat)
    (Qeff QH : Fn → ℕ) (heff : Efficient Qeff)
    (decomp : cc.Q = fun f => Qeff f + QH f) :
    ¬ (∀ f, QH f = 0) := by
  intro hall
  have hre : cc.Q = Qeff := by
    funext f; simp only [decomp, hall, Nat.add_zero]
  exact charge_forces_non_natural barrier hC cc (by rw [hre]; exact heff)

/-- **The purely-computable charge is impossible (proved).**  If the N-Frame charge is entirely its
computable current (`Q = Q_eff`, `Q_eff` efficient), the barrier rules it out.  The Lagrangian's
Turing-computable part alone cannot be the conserved charge. -/
theorem pure_Leff_charge_barriered {Efficient : (Fn → ℕ) → Prop} {Crypto : Prop}
    (barrier : ChargeBarrier Fn Rep computes rrank Easy sat Efficient Crypto) (hC : Crypto)
    (cc : ConservedCharge Fn Rep computes rrank Easy sat)
    (heff : Efficient cc.Q) : False :=
  charge_forces_non_natural barrier hC cc heff

end PallLean.Paper93.DeepMath.PathB.NFrameChargeNoether

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargeNoether.noether_charge_needs_hyper
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargeNoether.pure_Leff_charge_barriered
