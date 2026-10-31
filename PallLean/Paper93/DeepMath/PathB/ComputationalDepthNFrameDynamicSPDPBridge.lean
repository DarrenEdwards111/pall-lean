import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFinalReduction

/-!
# N-Frame: the dynamic SPDP boundary bridge — the dictionary

Track B.  This file adds **no new mathematics**: it is the formal dictionary tying the finished Track A
theorems to the dynamic-SPDP / boundary-geometry language of the N-Frame programme (Book 1).  Every
entry is a definition plus a restatement of an already-proved theorem.

The dictionary:

| dynamic SPDP / boundary geometry      | formal object                                    |
|----------------------------------------|--------------------------------------------------|
| hypercube move (edge)                  | `cubeEdge x i` — a single-bit update             |
| curvature witness (2-cell)             | `OddSquareWitness` — an odd-parity square        |
| local obstruction to flat factorization| `V1Witness` / `V0Witness` — the L-triples        |
| flat chart over a cut                  | `FlatChart f S` — a bipartite factorization      |
| boundary volume                        | `BoundaryVolume f = cbudget f`                   |
| boundary curvature                     | `BoundaryCurvature c = coneExcess c (root)`      |
| flat boundary                          | `FlatBoundary c` — curvature zero                |

The proved geometry:

  `boundary_volume_priced` — volume is bounded below by the flat floor **plus curvature**
        (the slot-multiplicity connectivity refinement).
  `flat_boundary_gives_chart` — a flat minimal SAT boundary yields a proper flat chart
        (root-shape reduction + top split + read-uniqueness + the constant-wire kill).
  `sat3_no_flat_chart` — SAT admits no proper flat chart (the discharged split hypothesis).
  `sat3_boundary_nonflat` — **SAT has non-flat boundary geometry**: every minimal circuit carries
        positive curvature.
  `sat3_boundary_volume_exceeds_flat_floor` — hence its boundary volume strictly exceeds the flat
        (tree/connectivity) floor: `2·N ≤ BoundaryVolume (sat3Family N)`.

## Honest scope

The conceptual reading is exactly HAL's: *SAT requires positive boundary curvature, so its boundary
volume exceeds the flat connectivity floor.*  What the dictionary does **not** contain — and what the
next mountains are — is a theory of **curvature accumulation** (local witnesses composing into
`Ω(m)`-scale curvature, then dimension growth), and the **observer-captures-P** bridge
(`PolyTime ⊆ BoundaryObserverPoly`).  A single unit of positive curvature is a linear-regime fact.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The dictionary: definitions -/

/-- A hypercube move: flip one coordinate. -/
def cubeEdge {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!(x i))

/-- Boundary volume: the observer's gate budget. -/
noncomputable def BoundaryVolume {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := cbudget f

/-- Boundary curvature of a concrete observer: its total excess fanout. -/
def BoundaryCurvature {n : ℕ} (c : List (CGate n)) : ℕ := coneExcess c (c.length - 1)

/-- A flat boundary: curvature zero — the read-once regime. -/
def FlatBoundary {n : ℕ} (c : List (CGate n)) : Prop := BoundaryCurvature c = 0

/-- A curvature witness: an odd-parity 2-cell of the hypercube. -/
def OddSquareWitness {n : ℕ} (f : (Fin n → Bool) → Bool) (s t : Fin n)
    (w : Fin n → Bool) : Prop :=
  xor (xor (f w) (f (cubeEdge w s)))
    (xor (f (cubeEdge w t)) (f (cubeEdge (cubeEdge w s) t))) = true

/-- A flat chart over the cut `S`: a bipartite factorization of `f`. -/
def FlatChart {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : Prop :=
  ∃ (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool),
    (∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) ∧
    (∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) ∧
    (∀ x, f x = op (g x) (h x))

/-! ### The dictionary: proved geometry -/

theorem boundaryVolume_eq_cbudget {n : ℕ} (f : (Fin n → Bool) → Bool) :
    BoundaryVolume f = cbudget f := rfl

theorem boundaryCurvature_eq_coneExcess {n : ℕ} (c : List (CGate n)) :
    BoundaryCurvature c = coneExcess c (c.length - 1) := rfl

/-- **VOLUME IS PRICED BY CURVATURE (proved)**: `2·K + curvature ≤ length + 1` for any circuit with `K`
essential variables — the flat floor plus every unit of curvature. -/
theorem boundary_volume_priced {n : ℕ} (f : (Fin n → Bool) → Bool) (V : Finset (Fin n))
    (hess : ∀ i ∈ V, ∃ x₁ x₀ : Fin n → Bool,
      (∀ b : Fin n, x₁ b ≠ x₀ b → b = i) ∧ f x₁ ≠ f x₀)
    (c : List (CGate n)) (hcomp : computes c f) :
    2 * V.card + BoundaryCurvature c ≤ c.length + 1 :=
  connectivity_fanout f V hess c hcomp

/-- **FLAT BOUNDARY ⇒ FLAT CHART (proved)**: a flat minimal SAT observer factorizes over a proper
cut. -/
theorem flat_boundary_gives_chart (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) (hflat : FlatBoundary c) :
    ∃ S : Finset (Fin N), FlatChart (sat3Family N) S ∧
      (∃ s₀ : Fin N, s₀ ∈ S) ∧ (∃ t₀ : Fin N, t₀ ∉ S) := by
  obtain ⟨op, g, h, S, hg, hh, hf, hs, ht⟩ :=
    sat3_split_frame_proper N hv hm3 hk c hcomp hmin hflat
  exact ⟨S, ⟨op, g, h, hg, hh, hf⟩, hs, ht⟩

/-- **NO PROPER FLAT CHART (proved)**: the discharged split hypothesis, in dictionary language. -/
theorem sat3_no_flat_chart (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hDN : sat3M N * sat3D N = N)
    (S : Finset (Fin N)) (hchart : FlatChart (sat3Family N) S)
    (hs : ∃ s₀ : Fin N, s₀ ∈ S) (ht : ∃ t₀ : Fin N, t₀ ∉ S) : False := by
  obtain ⟨op, g, h, hg, hh, hf⟩ := hchart
  exact sat3_no_bipartite_split_proper N hv hm3 hk hDN op g h S hg hh hf hs ht

/-- **SAT HAS NON-FLAT BOUNDARY GEOMETRY (proved)**: every minimal observer carries positive
curvature. -/
theorem sat3_boundary_nonflat (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hDN : sat3M N * sat3D N = N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) : ¬ FlatBoundary c := by
  intro hflat
  have h := sat3_coneExcess_pos N hv hm3 hk hDN c hcomp hmin
  rw [show coneExcess c (c.length - 1) = BoundaryCurvature c from rfl, hflat] at h
  omega

/-- **THE HEADLINE, IN DICTIONARY LANGUAGE (proved)**: SAT's boundary volume strictly exceeds the flat
connectivity floor — `2·N ≤ BoundaryVolume (sat3Family N)`. -/
theorem sat3_boundary_volume_exceeds_flat_floor (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hDN : sat3M N * sat3D N = N) :
    2 * N ≤ BoundaryVolume (sat3Family N) :=
  sat3_cbudget_ge_2N N hv hm3 hk hDN

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boundary_volume_priced
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_boundary_nonflat
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_boundary_volume_exceeds_flat_floor
