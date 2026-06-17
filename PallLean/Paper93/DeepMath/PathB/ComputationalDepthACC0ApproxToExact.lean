import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTDepthCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pFoundations

/-!
# RS approx→exact — the composite-`ACC⁰` barrier, honestly separated (structural fragment proved)

Entry 204 (`…ACC0BTRSConnection`) left **`SpanApproxToLowDegRep`** — that a `3/4`-agreement `F_p`-span approximant of an
`ACC⁰` circuit yields an *exact* Boolean `LowDegRep` — as a single named socket.  That socket bundles the genuinely
hard content of the whole Beigel–Tarui/Razborov–Smolensky route.  This file **honestly separates** that socket into a
genuinely-provable structural fragment and the precise **barrier-atom**, proving *only* the fragment and naming the
barrier loudly.

⚠️ **False-closure warning (this is the highest-risk target).**  The approximate-to-exact amplification for *composite*
modulus is exactly where Razborov–Smolensky **provably fails** — it is the `ACC⁰[m]` barrier itself, equivalent in
strength to the separation for composite `m`.  Nothing here closes it.  The barrier is a *loudly named socket*
(`ApproxToExactCount`); only the easy structural direction is proved.

## The honest factorisation

`SpanApproxToLowDegRep` factors as:

1. **(barrier, socket `ApproxToExactCount`)** the `3/4`-agreement weighted `F_p`-span approximant ⟹ an *exact*,
   *unit-coefficient* count representation.  This bundles **two** genuinely-hard steps: (a) **amplification** from
   `3/4`-agreement to exact (the composite-modulus barrier; works for `AC⁰[p]` prime, *fails* for `ACC⁰[m]` composite —
   cf. the majority route being exponential, entry 217), and (b) **weighted → unit-coefficient** conversion respecting
   the *injective* monomial family `LowDegRep` demands (a general weighted `F_p`-sum is not the unweighted count
   `saCount`; one cannot simply duplicate monomials, since the family must stay injective).

2. **(proved, `lowDegRep_of_exactUnitCount`)** an exact unit-coefficient count representation ⟹ `LowDegRep`.

## What is proved (clean axioms, no `sorry`)

* **`ExactUnitCount p D f`** — `f`'s `F_p` value is *exactly* the count (mod `p`) of an injective family of degree-`≤D`
  monomials: `∀ x, boolToZMod p (f x) = (saCount mono x : ZMod p)`.
* **`lowDegRep_of_exactUnitCount`** (PROVED) — `ExactUnitCount p D f → LowDegRep f D`, with the `SYM` gate
  `h k := decide ((k : ZMod p) = 1)` reading the count mod `p`.  The genuine *easy* direction of the BT conversion.
* **`ApproxToExactCount approxHyp p D f`** — the barrier socket: the approximant ⟹ `ExactUnitCount` (subsumes
  amplification + weighted→unit).  Stated, **not** proved; it is the composite-`ACC⁰` barrier.
* **`lowDegRep_via_amplification`** (PROVED glue) — `approxHyp → ApproxToExactCount approxHyp p D f → LowDegRep f D`:
  the honest factorisation, exhibiting the barrier as the *only* missing input.

## Honest scope

This proves that an **exact unit-coefficient count representation is a `LowDegRep`** (`lowDegRep_of_exactUnitCount`,
the easy structural direction) and exhibits the precise factorisation of entry-204's `SpanApproxToLowDegRep` through the
barrier.  What remains the named socket is **`ApproxToExactCount`** — the approximate→exact amplification together with
the weighted→unit-coefficient conversion.  This is **the composite-`ACC⁰[m]` barrier**: for prime-power modulus the
amplification is available (the polynomial method works), but for composite `m` it provably fails and is
separation-strength.  This file does **not** close it, and pushing the socket would be false closure.  The structural
span = weighted-count-of-`AND`s fact is the proved entry-207 `span_eval_weightedCount`.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExact

open PallLean.Paper93.DeepMath.PathB.ACC0BTDepthCollapse (LowDegRep)
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose (saCount)
open PallLean.Paper93.DeepMath.PathB.Layer3 (boolToZMod)

/-- **An exact unit-coefficient count representation.**  `f`'s `F_p` value is *exactly* (everywhere, not `3/4`) the
count mod `p` of an injective family of degree-`≤D` monomials: `∀ x, boolToZMod p (f x) = (saCount mono x : ZMod p)`.
This is the `SYM∘AND` form with unit-weight `AND` gates — the *target* the barrier must reach from the weighted
approximant. -/
def ExactUnitCount (p : ℕ) {n : ℕ} (D : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)),
    Function.Injective mono ∧ (∀ j, (mono j).card ≤ D) ∧
    ∀ x, boolToZMod p (f x) = (saCount mono x : ZMod p)

/-- **Exact unit-coefficient count ⟹ `LowDegRep` (PROVED).**  The genuine *easy* direction of the Beigel–Tarui
conversion: if `f`'s `F_p` value is exactly the count mod `p` of an injective degree-`≤D` monomial family, then `f` is a
symmetric function of that count — `LowDegRep f D` — with the `SYM` gate `h k := decide ((k : ZMod p) = 1)` decoding the
count mod `p` (`f x = true ↔ count ≡ 1`, `false ↔ count ≡ 0`; `0 ≠ 1` in the field `ZMod p`). -/
theorem lowDegRep_of_exactUnitCount (p : ℕ) [Fact p.Prime] {n D : ℕ}
    (f : (Fin n → Bool) → Bool) (h : ExactUnitCount p D f) :
    LowDegRep f D := by
  obtain ⟨m, mono, hinj, hdeg, hcount⟩ := h
  refine ⟨m, mono, fun k => decide ((k : ZMod p) = 1), hinj, hdeg, ?_⟩
  funext x
  have hx := hcount x
  by_cases hf : f x = true
  · rw [hf]
    simp only [boolToZMod, hf, if_true] at hx
    rw [eq_comm, decide_eq_true_iff]
    exact hx.symm
  · simp only [Bool.not_eq_true] at hf
    rw [hf]
    simp [boolToZMod, hf] at hx
    rw [eq_comm, decide_eq_false_iff_not, ← hx]
    exact zero_ne_one

/-- **The barrier socket — approximate → exact (and weighted → unit).**  The `3/4`-agreement weighted `F_p`-span
approximant (`approxHyp`) yields an *exact unit-coefficient* count representation.  This is the composite-`ACC⁰[m]`
barrier: amplifying `3/4` to exact + converting weighted coefficients to a unit-weight injective family.  Stated,
**not** proved — for composite modulus it provably fails. -/
def ApproxToExactCount (approxHyp : Prop) (p : ℕ) {n : ℕ} (D : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  approxHyp → ExactUnitCount p D f

/-- **The honest factorisation of `SpanApproxToLowDegRep` (PROVED glue).**  The RS span approximant (`approxHyp`,
supplied by the proved Razborov–Smolensky method, entry 204) plus the barrier socket `ApproxToExactCount` give
`LowDegRep f D`.  This exhibits **`ApproxToExactCount` as the *only* missing input** between the proved RS approximant
and the `LowDegRep` that the BT collapse (entry 203) consumes — i.e. the composite-`ACC⁰` barrier is the sole residual,
not a diffuse gap. -/
theorem lowDegRep_via_amplification (approxHyp : Prop) (p : ℕ) [Fact p.Prime] {n D : ℕ}
    (f : (Fin n → Bool) → Bool)
    (ha : approxHyp) (amp : ApproxToExactCount approxHyp p D f) :
    LowDegRep f D :=
  lowDegRep_of_exactUnitCount p f (amp ha)

end PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExact.lowDegRep_of_exactUnitCount
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExact.lowDegRep_via_amplification
