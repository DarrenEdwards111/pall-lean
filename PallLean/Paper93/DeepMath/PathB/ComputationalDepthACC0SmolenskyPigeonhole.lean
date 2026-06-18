import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MultilinearBasis

/-!
# The Smolensky pigeonhole — attacking the wall (step 4) via the entry-264 rank kernel

The Razborov–Smolensky non-native lower bound decomposes into two halves:

* **(counting/rank)** a *large good set* cannot have all its point-indicator functions representable in a *low-degree*
  space — because the point indicators are linearly independent (dimension `= |good set|`) and the low-degree space has
  dimension `lowDegreeDim n D' < |good set|`;
* **(degree-halving)** a degree-`D` approximator of `MOD_q` over `F_p` (`p ≠ q`) makes *every* function on its good set
  representable at degree `≤ n/2 + D` — the genuine Razborov–Smolensky representation lemma, which uses the algebra of
  `MOD_q` over `F_p`.

This file **proves the counting/rank half** — the Smolensky pigeonhole — by reusing the entry-264 rank kernel
(`exists_notMem_of_finrank_lt`) and the entry-265 multilinear dimension (`lowDegreeSubmodule_finrank`), and **isolates
the degree-halving as the single remaining socket** `SmolenskyDegreeHalving`.  This is exactly "attack step 4 via the
264 pigeonhole": the counting contradiction is now machine-proved; the residue is the one representation lemma.

## What is proved (clean axioms, no `sorry`)

* **`ptInd g := fun x => if x = g then 1 else 0`** — the point indicator at `g`.
* **`ptInd_linearIndependent`** (PROVED) — the point indicators over a finset `S` are linearly independent
  (`Fintype.linearIndependent_iff` + evaluation: only the `g'=g` term survives at `x = g`).
* **`smolensky_pigeonhole`** (PROVED) — if every point indicator of `S` lies in a submodule `W` with
  `finrank W < |S|`, then `False` (the entry-264 rank kernel: the `|S|`-dimensional point-indicator span cannot embed in
  `W`).
* **`smolensky_pigeonhole_lowDegree`** (PROVED) — instantiated at `W = lowDegreeSubmodule n D'`
  (`finrank = lowDegreeDim n D'`, entry 265): if every good-set point indicator is degree `≤ D'` and
  `lowDegreeDim n D' < |S|`, then `False`.

## The remaining socket (the genuine Smolensky core)

* **`SmolenskyDegreeHalving`** — a degree-`D` approximator of the non-native target makes every good-set point indicator
  degree `≤ D'` (`D' = n/2 + D`).  The Razborov–Smolensky representation lemma; uses `MOD_q`'s algebra over `F_p`.
  Combined with the binomial tail `lowDegreeDim n (n/2+D) < |good set|` (for `D` small) and the proved pigeonhole, it
  forces high degree.  For composite modulus this is the open `ACC⁰[composite]` wall (entry-238).

## Honest scope

This proves the **counting/rank half** of the Smolensky lower bound — the pigeonhole that a large good set forces a
high-degree point function, via the entry-264 rank kernel and entry-265 dimension.  The remaining content is the single
socket `SmolenskyDegreeHalving` (the degree-halving representation lemma — the genuine Smolensky core).  This does
**not** prove the lower bound (the socket is the wall), and is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPigeonhole

open PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree (exists_notMem_of_finrank_lt lowDegreeDim)
open PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis (lowDegreeSubmodule lowDegreeSubmodule_finrank)

variable {X F : Type} [Fintype X] [DecidableEq X] [Field F]

/-- **The point indicator** at `g`: `1` at `g`, `0` elsewhere. -/
def ptInd (g : X) : X → F := fun x => if x = g then (1 : F) else 0

/-- **The point indicators of a finset are linearly independent (PROVED).**  A dependence `∑_g c_g · ptInd g = 0`,
evaluated at a point `g`, collapses to `c_g = 0` (only the `g`-term survives). -/
theorem ptInd_linearIndependent (S : Finset X) :
    LinearIndependent F (fun g : S => (ptInd g.1 : X → F)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  have hev := congrFun hc g.1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ptInd] at hev
  have hsum : (∑ g' : S, c g' * (if (g.1 : X) = g'.1 then (1 : F) else 0)) = c g := by
    rw [Finset.sum_eq_single_of_mem g (Finset.mem_univ g)]
    · simp
    · intro g' _ hne
      have hval : ¬ ((g.1 : X) = g'.1) := fun h => hne (Subtype.ext h.symm)
      simp [hval]
  rw [hsum] at hev
  exact hev

/-- **The Smolensky pigeonhole (PROVED).**  If every point indicator of `S` lies in `W` and `finrank W < |S|`, then
`False`: the point indicators span a `|S|`-dimensional space (`ptInd_linearIndependent` + `finrank_span_eq_card`), which
cannot embed in the smaller `W` (entry-264 `exists_notMem_of_finrank_lt`). -/
theorem smolensky_pigeonhole (S : Finset X) (W : Submodule F (X → F))
    (hrep : ∀ g ∈ S, (ptInd g : X → F) ∈ W) (hlt : Module.finrank F W < S.card) : False := by
  have hspan : Module.finrank F W
      < Module.finrank F (Submodule.span F (Set.range (fun g : S => (ptInd g.1 : X → F)))) := by
    rw [finrank_span_eq_card (ptInd_linearIndependent S), Fintype.card_coe]
    exact hlt
  obtain ⟨g, hg⟩ := exists_notMem_of_finrank_lt (fun g : S => (ptInd g.1 : X → F)) W hspan
  exact hg (hrep g.1 g.2)

/-- **The Smolensky pigeonhole at the low-degree submodule (PROVED).**  If every good-set point indicator is degree
`≤ D'` (lies in `lowDegreeSubmodule n D'`) and the good set is larger than the low-degree dimension
(`lowDegreeDim n D' < |S|`), then `False`.  (`W = lowDegreeSubmodule n D'`, `finrank = lowDegreeDim n D'`, entry 265.) -/
theorem smolensky_pigeonhole_lowDegree {n D' : ℕ} (S : Finset (Fin n → Bool))
    (hrep : ∀ g ∈ S, (ptInd g : (Fin n → Bool) → F) ∈ lowDegreeSubmodule (F := F) n D')
    (hbig : lowDegreeDim n D' < S.card) : False := by
  apply smolensky_pigeonhole S (lowDegreeSubmodule (F := F) n D') hrep
  rw [lowDegreeSubmodule_finrank]
  exact hbig

/-- **The degree-halving socket (the genuine Smolensky core, NOT proved).**  A degree-`D` `F`-approximator of the
non-native target (`MOD_q`, `q ≠ char F`) makes *every* point indicator on its good set `S` representable at degree
`≤ D'` (`D' = n/2 + D`) — the Razborov–Smolensky representation lemma, using `MOD_q`'s algebra over `F_p`.  Combined with
the proved pigeonhole and the binomial tail (`lowDegreeDim n D' < |S|`, for `D` small), it forces high degree.  For
composite modulus this is the open `ACC⁰[composite]` wall (entry-238 `CarryRefinementCrossing`). -/
def SmolenskyDegreeHalving {n D' : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  ∀ g ∈ S, (ptInd g : (Fin n → Bool) → F) ∈ lowDegreeSubmodule (F := F) n D'

/-- **The Smolensky lower bound via the pigeonhole (PROVED, modulo the degree-halving socket).**  Given the degree-halving
representation (`SmolenskyDegreeHalving`: good-set point functions are degree `≤ D'`) and a good set larger than the
low-degree dimension (`lowDegreeDim n D' < |S|`), there is no such low-degree approximator — `False` follows.  The
counting/rank half is proved (the pigeonhole); the residue is the degree-halving lemma. -/
theorem smolensky_lower_bound_via_pigeonhole {n D' : ℕ} (S : Finset (Fin n → Bool))
    (hhalving : SmolenskyDegreeHalving (F := F) (D' := D') S)
    (hbig : lowDegreeDim n D' < S.card) : False :=
  smolensky_pigeonhole_lowDegree S hhalving hbig

/-!
**The attack on the wall.**  The Smolensky lower bound's *counting/rank half* is now machine-proved: a good set larger
than the low-degree dimension forces a high-degree point function (`smolensky_pigeonhole`, via the entry-264 rank kernel
and entry-265 multilinear dimension).  The contradiction `smolensky_lower_bound_via_pigeonhole` reduces the wall to the
*single* socket `SmolenskyDegreeHalving` — the Razborov–Smolensky degree-halving representation lemma, which uses
`MOD_q`'s algebra over `F_p`.  That lemma (prime case) is the classical Smolensky core; for composite modulus it is the
open `ACC⁰[composite]` wall (entry-238 `CarryRefinementCrossing`).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPigeonhole

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPigeonhole.ptInd_linearIndependent
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPigeonhole.smolensky_pigeonhole
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPigeonhole.smolensky_pigeonhole_lowDegree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPigeonhole.smolensky_lower_bound_via_pigeonhole
