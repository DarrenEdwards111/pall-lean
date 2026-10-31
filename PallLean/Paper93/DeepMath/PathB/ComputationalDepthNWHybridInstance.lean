import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWHybridProbability

/-!
# Socket-2 (IKW): the NW hybrid instantiation

Rung 8 proved the abstract hybrid reduction (`Prob.hybrid_argument`): a distinguisher with advantage `≥ ε` between the
endpoint hybrids `H 0` and `H m` distinguishes some *consecutive* pair with advantage `≥ ε/m`.  That reduction was stated
for an arbitrary hybrid family `H`.  This file instantiates `H` as the **Nisan–Wigderson generator's coordinate-hybrids**,
over the concrete sample space of a seed together with an independent uniform bit-string.

  `NWSample q m` — the sample space: an NW seed `z ∈ {0,1}^{q²}` and an independent uniform string `r ∈ {0,1}^m` (one fresh
        bit per output coordinate).
  `nwOutput` / `nwUniform` — the generator's output string and the uniform string, as distributions on `NWSample q m`.
  `nwHybrid f poly j` — the `j`-th hybrid: coordinates `< j` are the generator's output, the rest are fresh uniform bits.
  `nwHybrid_zero` / `nwHybrid_card` — **PROVED, the endpoints**: `nwHybrid _ 0 = nwUniform` and `nwHybrid _ m = nwOutput`.
  `nwHybrid_agree_off` / `nwHybrid_succ_at` — **PROVED, the single-coordinate step**: `nwHybrid _ j` and `nwHybrid _ (j+1)`
        agree off coordinate `j`, and at coordinate `j` the former reads the fresh uniform bit while the latter reads the
        generator's bit `nwGen f z (poly j)` — the exact structure Yao's next-bit conversion consumes.
  `nw_hybrid_reduction` — **PROVED, the instantiated reduction**: a distinguisher separating the generator's output from
        uniform with advantage `≥ ε` separates some consecutive NW hybrid pair with advantage `≥ ε/m`.

So the abstract reduction is now anchored to the real generator: consecutive NW hybrids differ in exactly one coordinate,
whose value flips between a fresh uniform bit and the generator's bit at `poly j` — the coordinate a next-bit predictor
targets, where rung 7's `< 7·2^k` circuit for the *other* coordinates makes the predictor small.

## Honest scope — the hybrid family, not Yao's conversion or the collapse

This defines the NW coordinate-hybrids concretely and proves their endpoint and single-coordinate-difference structure,
then instantiates rung 8's reduction on them.  It does **not** carry out **Yao's next-bit conversion** (turning the
single-step distinguishing advantage into a predictor for `nwGen f z (poly j)` given the other coordinates), nor its
combination with rung 7's circuit and `f`'s average-case hardness to reach a contradiction, nor the IKW easy-witness
collapse.  The enumeration `poly` of the design polynomials is taken as given (injective in the intended instantiation; the
hybrid mechanics here are enumeration-agnostic).  Those remaining steps are the deep `NEXP`-strength content of socket 2,
not established here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NWDesign

open Polynomial PallLean.Paper93.DeepMath.PathB.Prob

variable {q : ℕ} [Fact q.Prime] {m : ℕ}

/-- The sample space: an NW seed `z ∈ {0,1}^{q²}` together with an independent uniform string `r ∈ {0,1}^m` (one fresh bit
per output coordinate). -/
abbrev NWSample (q m : ℕ) := (ZMod q × ZMod q → Bool) × (Fin m → Bool)

/-- The NW generator's output string, indexed by an enumeration `poly` of the design polynomials (reads the seed, ignores
the fresh bits). -/
def nwOutput (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X]) :
    NWSample q m → (Fin m → Bool) :=
  fun ω i => nwGen f ω.1 (poly i)

/-- The uniform string (reads the fresh bits, ignores the seed). -/
def nwUniform : NWSample q m → (Fin m → Bool) :=
  fun ω i => ω.2 i

/-- The `j`-th NW hybrid: the first `j` coordinates are the generator's output, the rest are fresh uniform bits. -/
def nwHybrid (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X]) (j : ℕ) :
    NWSample q m → (Fin m → Bool) :=
  fun ω i => if (i : ℕ) < j then nwGen f ω.1 (poly i) else ω.2 i

/-- **Left endpoint (proved)**: hybrid `0` is the uniform distribution — no coordinate uses the generator. -/
theorem nwHybrid_zero (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X]) :
    nwHybrid f poly 0 = nwUniform := by
  funext ω i
  simp [nwHybrid, nwUniform]

/-- **Right endpoint (proved)**: hybrid `m` is the full generator output — every coordinate uses the generator. -/
theorem nwHybrid_card (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X]) :
    nwHybrid f poly m = nwOutput f poly := by
  funext ω i
  simp only [nwHybrid, nwOutput]
  rw [if_pos i.isLt]

/-- **Single-coordinate step, agreement off `j` (proved)**: consecutive hybrids agree on every coordinate other than `j`. -/
theorem nwHybrid_agree_off (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X])
    (j : ℕ) (ω : NWSample q m) (i : Fin m) (hij : (i : ℕ) ≠ j) :
    nwHybrid f poly j ω i = nwHybrid f poly (j + 1) ω i := by
  simp only [nwHybrid]
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- **Single-coordinate step, the flip at `j` (proved)**: at coordinate `j`, hybrid `j` reads the fresh uniform bit while
hybrid `j+1` reads the generator's bit `nwGen f z (poly j)` — the one bit whose distribution changes. -/
theorem nwHybrid_succ_at (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X])
    (j : ℕ) (ω : NWSample q m) (hj : j < m) :
    nwHybrid f poly j ω ⟨j, hj⟩ = ω.2 ⟨j, hj⟩ ∧
      nwHybrid f poly (j + 1) ω ⟨j, hj⟩ = nwGen f ω.1 (poly ⟨j, hj⟩) := by
  refine ⟨?_, ?_⟩
  · simp only [nwHybrid]; rw [if_neg (by simp)]
  · simp only [nwHybrid]; rw [if_pos (by simp)]

/-- **The instantiated hybrid reduction (proved)**: if a distinguisher `D` separates the NW generator's output from the
uniform string with advantage `≥ ε`, then it separates some *consecutive* NW hybrid pair with advantage `≥ ε/m`. -/
theorem nw_hybrid_reduction (hm : 0 < m) (f : (ZMod q → Bool) → Bool)
    (poly : Fin m → (ZMod q)[X]) (D : (Fin m → Bool) → Bool) (ε : ℝ)
    (hε : ε ≤ |distinguish D (nwUniform (q := q) (m := m)) - distinguish D (nwOutput f poly)|) :
    ∃ i, i < m ∧ ε / m ≤
      |distinguish D (nwHybrid f poly i) - distinguish D (nwHybrid f poly (i + 1))| := by
  apply hybrid_argument hm D (nwHybrid f poly) ε
  rw [nwHybrid_zero, nwHybrid_card]
  exact hε

end PallLean.Paper93.DeepMath.PathB.NWDesign

#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwHybrid_zero
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwHybrid_card
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwHybrid_agree_off
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwHybrid_succ_at
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nw_hybrid_reduction
