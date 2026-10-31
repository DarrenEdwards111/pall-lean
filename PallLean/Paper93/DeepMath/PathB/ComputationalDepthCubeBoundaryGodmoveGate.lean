import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeBoundaryGodmoveFastSAT

/-!
# Instantiating the boundary family on a concrete `ACC⁰` gate: the junta regime

`…CubeBoundaryGodmoveFastSAT` built the interface `CubeBoundaryGodmove` and proved the route
`CubeBoundaryGodmove → FastSATModel → Williams`.  This file **instantiates the observer-boundary family on concrete
`ACC⁰` gates** — an `OR`/`AND`-of-subset gate and a `MOD_m`-of-subset gate — producing genuine `CubeBoundaryGodmove`
witnesses with real savings `2^{n − |S| − 1}`.

## What the compression honestly is — and where the wall is

The `CubeBoundaryGodmove` savings guarantee is `#visible + 1 ≤ n − budget`: the observer must **hide** coordinates, and
the speedup exponent *is* the number of hidden coordinates.  So the boundary compresses a gate exactly when the gate
**ignores** coordinates — a *junta*.  For a `k`-junta on a coordinate set `S` (`|S| = k`), the observer hides the
`n − k` irrelevant coordinates; SAT is preserved because their values never change the gate's output
(`junta_sat_iff`), and the count-cell table has the `2^k` visible configurations.  This gives budget `n − k − 1`,
i.e. a real `2^{n−k−1}` speedup — **provided `k + 1 ≤ n`** (the gate ignores at least one coordinate).

  `DependsOnly f S` — `f` is a junta on `S`.
  `cutOn S` / `projB` — the observer cut making exactly `S` visible (hiding the rest at `false`), and its projection.
  `junta_sat_iff` — **the compression (proved)**: for a junta on `S`, `∃x. f x` iff `∃x. f (project through the cut)`;
        fixing hidden coordinates loses no satisfying assignment.
  `juntaGodmove` — **the instantiation (proved)**: any junta `f` on `S` with `|S| + 1 ≤ n` yields a
        `CubeBoundaryGodmove` with budget `n − |S| − 1`.
  `orGate` / `modGate` + `…Godmove` / `…_gives_nframe_speedup` — concrete `AC⁰`/`ACC⁰[m]` gates (`OR`/`MOD_m` of a
        subset) carried through the interface into the N-Frame fast-SAT speedup slot the Williams meta-theorem consumes.
  `boundary_leaves_hidden` / `fullVisible_no_boundary` — **the wall (proved)**: *every* `CubeBoundaryGodmove` leaves at
        least one coordinate hidden (`#visible < n`); a gate that genuinely needs all `n` coordinates visible admits
        **no** boundary Godmove.  The savings is intrinsically a hidden-coordinate phenomenon.

## Honest scope

This is a *genuine* instantiation, but on the **low-junta regime** — gates that ignore coordinates.  It is honest
non-vacuity for the interface with real, growing savings, **not** progress on the hard case.  A composite gate depending
on all `n` inputs (e.g. `MOD_6` on all `n` bits — the C16 wall) is a *full-support* function: `#visible = n` is forced,
and `boundary_leaves_hidden` shows that admits no boundary Godmove.  Compressing such a gate needs the count-cell table
to be subexponential for a reason *other than* ignored coordinates (the genuine open algorithmic target — a real
`ACC⁰`-SAT algorithm), which this file does **not** provide and does not fake.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveGate

open PallLean.Paper93.DeepMath.PathB.NFrameFastSAT
open PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP (CubeBoundary visible)
open PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveFastSAT

variable {n : ℕ}

/-- `f` **depends only on** `S`: agreement on `S` forces equal output — `f` is a junta on `S`. -/
def DependsOnly (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

/-- The **observer cut** making exactly `S` visible: hide every coordinate outside `S` at `false`. -/
def cutOn (S : Finset (Fin n)) : CubeBoundary n :=
  fun i => if i ∈ S then none else some false

/-- The Boolean projection through a cut: read visible coordinates from `x`, hidden ones from the cut. -/
def projB (ρ : CubeBoundary n) (x : Fin n → Bool) : Fin n → Bool :=
  fun k => (ρ k).getD (x k)

/-- The cut `cutOn S` has visible set exactly `S`. -/
theorem visible_cutOn (S : Finset (Fin n)) : visible (cutOn S) = S := by
  ext i
  simp only [visible, cutOn, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h <;> simp [h]

/-- Through `cutOn S`, a visible coordinate reads its own value. -/
theorem projB_cutOn_mem (S : Finset (Fin n)) (x : Fin n → Bool) {i : Fin n} (hi : i ∈ S) :
    projB (cutOn S) x i = x i := by
  simp [projB, cutOn, hi]

/-- A junta is unchanged by projecting through its own cut (hidden coordinates are irrelevant). -/
theorem gate_projB_eq {f : (Fin n → Bool) → Bool} {S : Finset (Fin n)} (hf : DependsOnly f S)
    (x : Fin n → Bool) : f (projB (cutOn S) x) = f x :=
  hf _ _ (fun _ hi => projB_cutOn_mem S x hi)

/-- **The compression (proved)**: for a junta on `S`, SAT of the gate equals SAT of its projection through the cut —
fixing hidden coordinates loses no satisfying assignment. -/
theorem junta_sat_iff {f : (Fin n → Bool) → Bool} {S : Finset (Fin n)} (hf : DependsOnly f S) :
    (∃ x, f (projB (cutOn S) x) = true) ↔ (∃ x, f x = true) := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨projB (cutOn S) x, hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x, (gate_projB_eq hf x).trans hx⟩

/-- **The instantiation (proved)**: any junta `f` on `S` with `|S| + 1 ≤ n` yields a `CubeBoundaryGodmove` — the observer
`cutOn S` hides the `n − |S|` irrelevant coordinates, the count-cell table holds the `2^{|S|}` visible configurations,
and the budget is `n − |S| − 1`. -/
def juntaGodmove (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (hf : DependsOnly f S) (hS : S.card + 1 ≤ n) :
    CubeBoundaryGodmove n Unit (fun _ => decide (∃ x, f x = true)) where
  boundary := fun _ => cutOn S
  cells := fun _ => 2 ^ S.card
  decideSAT := fun _ => decide (∃ x, f (projB (cutOn S) x) = true)
  preserves_sat := fun _ => decide_eq_decide.mpr (junta_sat_iff hf)
  budget := n - S.card - 1
  budget_le := by omega
  compress := fun _ => le_of_eq (by rw [visible_cutOn])
  hides := fun _ => by rw [visible_cutOn]; omega

/-- **The wall (proved)**: every `CubeBoundaryGodmove` leaves at least one coordinate hidden — `#visible < n`.  The
savings is intrinsically a hidden-coordinate phenomenon. -/
theorem boundary_leaves_hidden {Circuit : Type} {satOf : Circuit → Bool}
    (G : CubeBoundaryGodmove n Circuit satOf) (C : Circuit) :
    (visible (G.boundary C)).card < n := by
  have h := G.hides C
  omega

/-- **The wall, contrapositive (proved)**: a gate that keeps *all* `n` coordinates visible (a full-support function,
e.g. `MOD_6` on all `n` bits) admits no `CubeBoundaryGodmove` — the boundary mechanism alone cannot compress it. -/
theorem fullVisible_no_boundary {Circuit : Type} {satOf : Circuit → Bool}
    (G : CubeBoundaryGodmove n Circuit satOf) (C : Circuit)
    (hfull : (visible (G.boundary C)).card = n) : False := by
  have := boundary_leaves_hidden G C
  omega

/-! ### Concrete `AC⁰` / `ACC⁰[m]` junta gates -/

/-- The `OR`-of-subset gate: true iff some coordinate in `S` is set.  A junta on `S` (an `AC⁰ ⊆ ACC⁰` gate). -/
def orGate (S : Finset (Fin n)) : (Fin n → Bool) → Bool :=
  fun x => decide (∃ i ∈ S, x i = true)

theorem orGate_dependsOnly (S : Finset (Fin n)) : DependsOnly (orGate S) S := by
  intro x y hxy
  simp only [orGate]
  rw [decide_eq_decide]
  constructor
  · rintro ⟨i, hiS, hxi⟩; exact ⟨i, hiS, by rw [← hxy i hiS]; exact hxi⟩
  · rintro ⟨i, hiS, hyi⟩; exact ⟨i, hiS, by rw [hxy i hiS]; exact hyi⟩

/-- The `MOD_m`-of-subset gate: true iff the number of set coordinates in `S` is `≡ 0 (mod m)`.  A junta on `S` — the
`ACC⁰[m]` signature gate. -/
def modGate (m : ℕ) (S : Finset (Fin n)) : (Fin n → Bool) → Bool :=
  fun x => decide ((S.filter (fun i => x i = true)).card % m = 0)

theorem modGate_dependsOnly (m : ℕ) (S : Finset (Fin n)) : DependsOnly (modGate m S) S := by
  intro x y hxy
  have hfilter : S.filter (fun i => x i = true) = S.filter (fun i => y i = true) :=
    Finset.filter_congr (fun i hi => by rw [hxy i hi])
  simp only [modGate, hfilter]

/-- The `OR`-of-subset gate carried through the boundary interface (for `|S| + 1 ≤ n`). -/
def orGateGodmove (S : Finset (Fin n)) (hS : S.card + 1 ≤ n) :
    CubeBoundaryGodmove n Unit (fun _ => decide (∃ x, orGate S x = true)) :=
  juntaGodmove (orGate S) S (orGate_dependsOnly S) hS

/-- The `MOD_m`-of-subset gate carried through the boundary interface (for `|S| + 1 ≤ n`). -/
def modGateGodmove (m : ℕ) (S : Finset (Fin n)) (hS : S.card + 1 ≤ n) :
    CubeBoundaryGodmove n Unit (fun _ => decide (∃ x, modGate m S x = true)) :=
  juntaGodmove (modGate m S) S (modGate_dependsOnly m S) hS

/-- The `MOD_m`-of-subset gate routes all the way to the N-Frame fast-SAT speedup slot the Williams meta-theorem
consumes — a concrete `ACC⁰[m]` gate inhabiting the boundary route. -/
theorem modGate_gives_nframe_speedup (m : ℕ) (S : Finset (Fin n)) (hS : S.card + 1 ≤ n) :
    NFrameFastSATSpeedup n Unit (fun _ => decide (∃ x, modGate m S x = true)) :=
  cubeBoundaryGodmove_speedup ⟨modGateGodmove m S hS⟩

/-! ### A concrete numeric witness: `MOD_3` on `{0,1,2} ⊆ Fin 8`, budget `4` (a `2^4` speedup) -/

/-- `MOD_3` reading coordinates `{0,1,2}` of `8` inputs: the observer hides the other `5`, giving budget `8−3−1 = 4`. -/
def mod3on8 : CubeBoundaryGodmove 8 Unit (fun _ => decide (∃ x, modGate 3 ({0, 1, 2} : Finset (Fin 8)) x = true)) :=
  modGateGodmove 3 ({0, 1, 2} : Finset (Fin 8)) (by decide)

/-- The concrete witness hides `5` coordinates: budget `= 4`, a real `2^4` speedup over brute force `2^8`. -/
theorem mod3on8_budget : mod3on8.budget = 4 := by decide

end PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveGate

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveGate.junta_sat_iff
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveGate.juntaGodmove
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveGate.boundary_leaves_hidden
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveGate.modGate_gives_nframe_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveGate.mod3on8_budget
