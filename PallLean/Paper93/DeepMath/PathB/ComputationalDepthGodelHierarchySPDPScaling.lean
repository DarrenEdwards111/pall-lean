import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderAmplificationBoundary

/-!
# Gödel‑hierarchy / scaling dynamic SPDP — the ascending projection tower

Fixed‑order SPDP failed because it sees only a bounded Hamming ball (`…AffineIndicatorCollapse`,
`…ExpanderAmplificationBoundary`).  Book 1's **Gödel hierarchy** suggests the fix: don't use one fixed projection,
use an *ascending tower* `levelProj 0 ≤ levelProj 1 ≤ …` whose derivative order / shift radius grows with the
level (≈ observer / meta‑system strength).  This file builds that tower and proves it does what fixed SPDP could
not — **visibility increases with level** — while naming the one missing theorem precisely.

`SPDPLevel = (k, d)`; `levelProj a L = spdpProj a L.k L.d`; `godelLevel n = (log₂ n, log₂ n)` is the canonical
ascending tower.

## What is proved (clean axioms, no `sorry`)

* `levelProj_monotone` — **higher levels see at least as much**: `L₁.k ≤ L₂.k → L₁.d ≤ L₂.d ⇒
  pcrank (levelProj L₁) M ≤ pcrank (levelProj L₂) M`.  (Lower‑level features are coordinates of higher‑level
  features — via `pcrank_le_of_factor`.)  The tower is genuinely ascending.  *[milestone 1]*
* `levelProj_lowLevel_collapse` — **low levels stay blind**: a high‑distance residual (`MinSupportWeight M Δ`)
  collapses (`pcrank ≤ 1`) at every level with `L.k + L.d < Δ`.  Records the no‑go for sub‑distance levels.
* `spdp_full_radius_injective` / `levelProj_full_radius_eq_crank` — **the top of the tower sees everything**: at
  radius `d = a` the projection is injective and `pcrank = crank`.  So between a sub‑distance level (total
  collapse) and the full level (full rank) the rank *turns on as the level rises past the distance*.  *[milestone 2]*
* `levelProj_feature_bound` — the feature space at level `L` is `≤ 2^{|{S:|S|≤L.k}| · |{y:hw y≤L.d}|}`; at the
  Gödel level `(log₂ n, log₂ n)` this is `2^{quasi‑poly}` (honest: quasi‑polynomial, not polynomial).

## The live theorem, named (not proved)

* `PolyTimeLowGodelSPDP` — every poly‑time observer's Gödel‑level pcrank is polynomial (the A1 side).
* `HardFamilyHighGodelSPDP` — the hard family's Gödel‑level pcrank is super‑polynomial (the A3 side).
* `godelSPDP_no_shared_rank` — the two are **incompatible for one rank function**: a poly‑bounded Gödel‑pcrank
  cannot equal a super‑polynomial one.  So *if* both hold, the hard family's Gödel‑pcrank is not any poly
  observer's — i.e. the hard family is not poly‑observable.  This is the conditional separation; both fields are
  named hypotheses, exactly as in the Book 1 bridge.

## Honest verdict

The Gödel tower really does what fixed SPDP couldn't: `levelProj_monotone` + `levelProj_full_radius_eq_crank`
prove visibility *rises* with level, so a sufficiently high level *does* see the hard residuals
(`levelProj_lowLevel_collapse` shows exactly which levels are still blind).  But the missing theorem is unchanged
in spirit and now sharply located: **does the Gödel‑scaled level `(log₂ n, log₂ n)` keep poly‑time computations at
polynomial pcrank (A1) while the hard family is already super‑polynomial (A3)?**  The feature bound warns the
honest danger — at the log level the budget is `2^{quasi‑poly}`, so the A1 side is *quasi‑polynomial* unless a
sharper count is proven.  That sweet‑spot (P collapses, NP survives, budget controlled) is the `ScalingSPDPBridge`
— still the one irreducible `P ≠ NP`‑strength step.  This file converts "use an ascending tower" from metaphor
into a proved monotone hierarchy with the bridge isolated as `PolyTimeLowGodelSPDP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.LowDegreeProjection
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection
open PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse
open PallLean.Paper93.DeepMath.PathB.ExpanderAmplificationBoundary

/-- A level of the SPDP tower: derivative order `k` and shift radius `d`. -/
structure SPDPLevel where
  k : ℕ
  d : ℕ

/-- The projection at a given level. -/
def levelProj (a : ℕ) (L : SPDPLevel) := spdpProj a L.k L.d

/-- The canonical Gödel‑hierarchy level: order and radius both `log₂ n`. -/
def godelLevel (n : ℕ) : SPDPLevel := ⟨Nat.log 2 n, Nat.log 2 n⟩

variable {a : ℕ}

/-- **The tower is ascending (proved): higher levels see at least as much.**  A lower‑level feature is a
coordinate of a higher‑level feature, so `pcrank` is monotone in the level. -/
theorem levelProj_monotone (L₁ L₂ : SPDPLevel) (hk : L₁.k ≤ L₂.k) (hd : L₁.d ≤ L₂.d)
    {A : Type*} [Fintype A] (M : A → (Fin a → Bool) → Bool) :
    pcrank (levelProj a L₁) M ≤ pcrank (levelProj a L₂) M := by
  refine pcrank_le_of_factor (levelProj a L₁) (levelProj a L₂)
    (fun feat p => feat (⟨p.1.val, le_trans p.1.property hk⟩, ⟨p.2.val, le_trans p.2.property hd⟩)) M ?_
  intro r
  funext p
  rfl

/-- **Low levels stay blind (proved).**  A high‑distance residual collapses to `pcrank ≤ 1` at every level whose
order + radius is below the distance. -/
theorem levelProj_lowLevel_collapse {A : Type*} [Fintype A] (L : SPDPLevel) (Δ : ℕ)
    (M : A → (Fin a → Bool) → Bool) (hM : MinSupportWeight M Δ) (hlt : L.k + L.d < Δ) :
    pcrank (levelProj a L) M ≤ 1 :=
  highDistance_spdp_collapse L.k L.d Δ M hM hlt

/-- The full‑radius projection (`d = a`) is injective: its order‑`0` coordinates recover the row at every point. -/
theorem spdp_full_radius_injective (k : ℕ) : Function.Injective (spdpProj a k a) := by
  intro r r' h
  funext v
  have hv : hw v ≤ a := hw_le v
  have hco := congrFun h (⟨⟨∅, by simp⟩, ⟨v, hv⟩⟩ : {S : Finset (Fin a) // S.card ≤ k} × LowWt a a)
  simp only [spdpProj] at hco
  rw [derivSet_empty, derivSet_empty] at hco
  exact hco

/-- **The top of the tower sees everything (proved): at radius `a`, `pcrank = crank`.**  Combined with
`levelProj_monotone` and `levelProj_lowLevel_collapse`, the rank turns on as the level rises past the distance. -/
theorem levelProj_full_radius_eq_crank {A : Type*} [Fintype A] (k : ℕ) (M : A → (Fin a → Bool) → Bool) :
    pcrank (levelProj a ⟨k, a⟩) M = crank M :=
  pcrank_eq_crank_of_injective (spdpProj a k a) M (spdp_full_radius_injective k)

/-- **Feature‑count tension (proved): the budget at level `L` is `2^{(#S≤L.k)·(#hw≤L.d)}`.**  At the Gödel level
`(log₂ n, log₂ n)` both factors are `~ n^{log n}`, so the budget is `2^{quasi‑poly}` — the honest danger on the
A1 side. -/
theorem levelProj_feature_bound {A : Type*} [Fintype A] (L : SPDPLevel) (M : A → (Fin a → Bool) → Bool) :
    pcrank (levelProj a L) M ≤ 2 ^ Fintype.card ({S : Finset (Fin a) // S.card ≤ L.k} × LowWt a L.d) := by
  have h := pcrank_le_card_range (levelProj a L) M
  rwa [show Fintype.card (({S : Finset (Fin a) // S.card ≤ L.k} × LowWt a L.d) → Bool)
        = 2 ^ Fintype.card ({S : Finset (Fin a) // S.card ≤ L.k} × LowWt a L.d) by
    simp [Fintype.card_bool]] at h

/-! ### The live bridge, named -/

/-- **(A1, named — not proved):** every poly‑time observer's Gödel‑level pcrank is polynomial. -/
def PolyTimeLowGodelSPDP (godelPcrank : ℕ → ℕ) (C : ℕ) : Prop :=
  ∀ n, godelPcrank n ≤ n ^ C

/-- **(A3, named):** the hard family's Gödel‑level pcrank is super‑polynomial. -/
def HardFamilyHighGodelSPDP (godelPcrank : ℕ → ℕ) : Prop :=
  ∀ C : ℕ, ∃ n, n ^ C < godelPcrank n

/-- **The conditional separation (proved).**  A polynomially‑bounded Gödel‑pcrank cannot equal a
super‑polynomial one.  So if A1 holds for poly observers and A3 holds for the hard family, the hard family's
Gödel‑pcrank is **not** any poly observer's — the hard family is not poly‑observable.  Both A1 and A3 are named
hypotheses; the irreducible content is proving A1 (the `ScalingSPDPBridge`). -/
theorem godelSPDP_no_shared_rank (poly hard : ℕ → ℕ) (C : ℕ)
    (hP : PolyTimeLowGodelSPDP poly C) (hH : HardFamilyHighGodelSPDP hard) :
    poly ≠ hard := by
  intro hEq
  subst hEq
  obtain ⟨n, hn⟩ := hH C
  have hle := hP n
  omega

end PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling

#print axioms PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling.levelProj_monotone
#print axioms PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling.levelProj_lowLevel_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling.levelProj_full_radius_eq_crank
#print axioms PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling.levelProj_feature_bound
#print axioms PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling.godelSPDP_no_shared_rank
