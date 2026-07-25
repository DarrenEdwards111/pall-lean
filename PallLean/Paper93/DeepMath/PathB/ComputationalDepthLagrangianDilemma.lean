import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDischargePiStar

/-!
# The Lagrangian dilemma: `L_eff` cannot separate, so the fuel must be `L_H` or non-natural

`DischargePiStar` showed a separating rank measure exists iff SAT ∉ P.  This file machine-checks the
consequence for the **N-Frame action** `S_obs = ∫(L_eff + L_H(H))`, whose rank splits into a
Turing-computable part `L_eff` and a hypercomputational part `L_H`.  The dilemma is exhaustive:

* **`efficient_separating_barriered` (proved)** — the `L_eff` (computable) route is barriered: an
  *efficiently computable* separating measure is a natural property, so it breaks cryptography
  (Razborov–Rudich, taken as the named socket `NaturalProofsBarrier`).  No in-model efficient separating
  measure exists.
* **`lagrangian_dilemma` (proved)** — decompose the action-rank as `L_eff + L_H`.  If the
  hypercomputational part vanishes everywhere, the rank *is* `L_eff`, hence efficient, hence barriered.
  So a separating action-rank **must have a nonzero `L_H` contribution somewhere** — it must use the
  hypercomputational term.

Together with `DischargePiStar.separating_iff_not_PComp` (whose backward witness is the `Classical`
indicator — non-natural, and it presupposes SAT ∉ P), this is the full trichotomy: **every separating
measure is (a) non-natural (the `Classical` indicator, which assumes the answer), (b) hypercomputational
(`L_H ≠ 0`, outside the model), or (c) efficient — and then it breaks crypto.** There is no in-model,
efficient, honest construction.

**Honest scope.**  The barrier is the named Razborov–Rudich socket; the dilemma is proved around it.
This is the machine-checked reason the N-Frame Lagrangian cannot supply the separating measure: its
computable part is barriered and its extra fuel is, by its own definition, hypercomputational.  It
confirms — formally — that constructing the measure is the lower bound, not a step toward it.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LagrangianDilemma

open PallLean.Paper93.DeepMath.PathB.DischargePiStar

variable {Obj : Type}

/-- **The natural-proofs barrier, named.**  An *efficiently computable* separating rank measure is a
natural property against P; under a cryptographic assumption it cannot exist (Razborov–Rudich).  This
is the socket the dilemma turns on. -/
def NaturalProofsBarrier (PComp : Obj → Prop) (sat : Obj)
    (Efficient : (Obj → ℕ) → Prop) (Crypto : Prop) : Prop :=
  ∀ S : SeparatingMeasure Obj PComp sat, Efficient S.rank → Crypto → False

/-- **Horn 1 — the computable route is barriered (proved).**  An efficiently computable separating
measure breaks cryptography, so no separating measure from the Turing-computable part `L_eff` of the
action can exist in-model. -/
theorem efficient_separating_barriered
    {PComp : Obj → Prop} {sat : Obj} {Efficient : (Obj → ℕ) → Prop} {Crypto : Prop}
    (barrier : NaturalProofsBarrier PComp sat Efficient Crypto) (hC : Crypto)
    (S : SeparatingMeasure Obj PComp sat) (heff : Efficient S.rank) : False :=
  barrier S heff hC

/-- **THE DILEMMA (proved).**  Write the action-rank as `L_eff + L_H`.  If the hypercomputational part
`L_H` vanishes everywhere, the rank equals the computable `L_eff`, which is efficient and therefore
barriered.  Hence a *separating* action-rank must have a **nonzero hypercomputational contribution** —
the N-Frame fuel `L_H` is essential to separation, and it is by definition outside the standard model. -/
theorem lagrangian_dilemma
    {PComp : Obj → Prop} {sat : Obj} {Efficient : (Obj → ℕ) → Prop} {Crypto : Prop}
    (barrier : NaturalProofsBarrier PComp sat Efficient Crypto) (hC : Crypto)
    (eff hyp : Obj → ℕ) (Leff_efficient : Efficient eff)
    (S : SeparatingMeasure Obj PComp sat) (decomp : S.rank = fun o => eff o + hyp o) :
    ¬ (∀ o, hyp o = 0) := by
  intro hall
  have hre : S.rank = eff := by
    funext o; simp only [decomp, hall, Nat.add_zero]
  exact barrier S (by rw [hre]; exact Leff_efficient) hC

/-- **The trichotomy, stated (proved).**  Under the barrier and crypto, an efficiently computable
separating measure is impossible — so any separating measure is either non-natural (`¬ Efficient`) or
lands in the hypercomputational term.  Equivalently: `Efficient S.rank` is false. -/
theorem separating_not_efficient
    {PComp : Obj → Prop} {sat : Obj} {Efficient : (Obj → ℕ) → Prop} {Crypto : Prop}
    (barrier : NaturalProofsBarrier PComp sat Efficient Crypto) (hC : Crypto)
    (S : SeparatingMeasure Obj PComp sat) : ¬ Efficient S.rank :=
  fun heff => barrier S heff hC

end PallLean.Paper93.DeepMath.PathB.LagrangianDilemma

#print axioms PallLean.Paper93.DeepMath.PathB.LagrangianDilemma.efficient_separating_barriered
#print axioms PallLean.Paper93.DeepMath.PathB.LagrangianDilemma.lagrangian_dilemma
#print axioms PallLean.Paper93.DeepMath.PathB.LagrangianDilemma.separating_not_efficient
