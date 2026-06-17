import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndFanIn

/-!
# The count-mod-`p` multiplicity collapse — the arithmetic heart of the span→`SYM∘AND` bridge (proved)

Entry 204 reduced the BT depth-collapse's `AccToLowDeg` socket to the residual **`SpanApproxToLowDegRep`** bridge: turn
an `F_p`-linear span approximant (a low-degree polynomial `∑_S c_S·e_S`) into an exact Boolean `SYM∘AND`.  That bridge
has two genuinely distinct pieces: the **multiplicity / count-mod-`p` expansion** (provable arithmetic) and the
**`3/4`→exact amplification** (the deep remaining step).  This file *proves the arithmetic heart* — the count-mod-`p`
expansion — and isolates the amplification as the residual.

The count-mod-`p` identity.  An `F_p`-combination `∑_S c_S·[S satisfied]` (`c_S ∈ ℕ` the multiplicities) is the value
of a **count of `AND`-copies**: replace each monomial `S` with `c_S` copies, index them by the sigma type
`Σ s, Fin (c s)`, and the count `saCount` of satisfied copies is exactly the weighted sum `∑_s c_s·[base s satisfied]`
(`saCount_sigma_expand`).  Reduced mod `p`, this is the `F_p` polynomial value (`saCount_sigma_cast`).  Hence the
function is a **symmetric** function of the `AND`-copies — a `SYM∘AND` of size `∑_s c_s` (`countModP_collapse`),
quasipolynomial when each `c_s ≤ p−1` and there are quasipolynomially many low-degree monomials
(`expand_card_le_mult`).

## What is proved (clean axioms, no `sorry`)

* **`saCount_sigma_expand`** — the weighted-count identity: `saCount` of the `Σ s, Fin (c s)` expansion equals
  `∑_s c_s·[base s satisfied]`.
* **`saCount_sigma_cast`** — the count-mod-`p` identity: that count, cast to `ZMod p`, is the `F_p` weighted value
  `∑_s (c_s : ZMod p)·[base s satisfied]` — i.e. the count mod `p` *is* the `F_p` polynomial value.
* **`countModP_collapse`** — the collapse: a count-mod-`p` decode `h ∘ saCount` of the `AND`-copy multiset is a
  `SYM∘AND` of size `∑_s c_s` and fan-in `≤ D` (no injectivity needed — multiplicity is allowed).
* **`expand_card_le_mult`** — the size bound: `∑_s c_s ≤ K·M` when each `c_s ≤ M` (with `M = p−1`, `K` the number of
  distinct monomials).
* **`ExactCountModPRep`** / **`bridge_via_countModP`** — the residual amplification socket and the assembly: an exact
  count-mod-`p` multiset representation of `f` (degree `≤ D`) yields a `SYM∘AND` form of `f` of fan-in `≤ D`.

## Honest scope

This proves the **multiplicity / count-mod-`p` arithmetic** of the span→`SYM∘AND` bridge — that an `F_p`-combination of
monomials, via `AND`-copy multiplicity, *is* a count-mod-`p` (hence symmetric) function, collapsing to a `SYM∘AND` of
size `∑ c_s` (`≤ (p−1)·#monomials`, quasipolynomial) — completely and from first principles.  What remains the named
socket, **`ExactCountModPRep`**, is that the circuit `f` actually *has* such an **exact** count-mod-`p` representation:
the `3/4`→exact amplification (combining several `RS` approximants) and the extraction of the explicit multiplicities
from the span coefficients.  This removes the count-mod-`p` content from entry 204's `SpanApproxToLowDegRep` bridge,
leaving only the amplification.  This proves the arithmetic half of the bridge, not the amplification.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CountModP

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose (saCount)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn (HasSymAndFormFanIn)

variable {n : ℕ}

/-- **The weighted-count identity (PROVED).**  Indexing `c_s` copies of each monomial `base s` by `Σ s, Fin (c s)`, the
count of satisfied `AND`-copies is the weighted sum `∑_s c_s·[base s satisfied]` — the value (over `ℕ`) of the
polynomial `∑_s c_s·e_{base s}`. -/
theorem saCount_sigma_expand {K : ℕ} (c : Fin K → ℕ) (base : Fin K → Finset (Fin n))
    (x : Fin n → Bool) :
    saCount (fun p : Σ s : Fin K, Fin (c s) => base p.1) x
      = ∑ s : Fin K, c s * (if monoAND (base s) x then 1 else 0) := by
  unfold saCount
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only []
  rw [Fin.sum_const (c s) (if monoAND (base s) x then (1 : ℕ) else 0), smul_eq_mul]

/-- **The count-mod-`p` identity (PROVED).**  The count of satisfied `AND`-copies, cast to `ZMod p`, is the `F_p`
weighted value `∑_s (c_s : ZMod p)·[base s satisfied]` — the count mod `p` *is* the `F_p` polynomial value, the BT
representation pivot. -/
theorem saCount_sigma_cast (p : ℕ) {K : ℕ} (c : Fin K → ℕ) (base : Fin K → Finset (Fin n))
    (x : Fin n → Bool) :
    ((saCount (fun q : Σ s : Fin K, Fin (c s) => base q.1) x : ℕ) : ZMod p)
      = ∑ s : Fin K, (c s : ZMod p) * (if monoAND (base s) x then 1 else 0) := by
  rw [saCount_sigma_expand]; push_cast; rfl

/-- **The count-mod-`p` collapse (PROVED).**  A count-mod-`p` decode `h ∘ saCount` of the `AND`-copy multiset
(monomials `base s` of degree `≤ D`, each with multiplicity `c s`) is a `SYM∘AND` of size `∑_s c_s` and fan-in `≤ D`.
No injectivity is needed — multiplicity is allowed (the sigma index `Σ s, Fin (c s)`). -/
theorem countModP_collapse {K : ℕ} (base : Fin K → Finset (Fin n)) (c : Fin K → ℕ) (h : ℕ → Bool)
    {D : ℕ} (hdeg : ∀ s, (base s).card ≤ D) :
    HasSymAndFormFanIn (fun x => h (saCount (fun q : Σ s : Fin K, Fin (c s) => base q.1) x))
      (∑ s : Fin K, c s) D := by
  refine ⟨Σ s : Fin K, Fin (c s), inferInstance, (fun q => base q.1), h, ?_, ?_, rfl⟩
  · rw [Fintype.card_sigma]; simp [Fintype.card_fin]
  · rintro ⟨s, _⟩; exact hdeg s

/-- **The multiplicity size bound (PROVED).**  `∑_s c_s ≤ K·M` when each multiplicity `c_s ≤ M`; with `M = p−1` and
`K ≤ (D+1)·n^D` low-degree monomials, the `SYM∘AND` size is `≤ (p−1)·(D+1)·n^D` — quasipolynomial. -/
theorem expand_card_le_mult {K : ℕ} (c : Fin K → ℕ) {M : ℕ} (hc : ∀ s, c s ≤ M) :
    ∑ s : Fin K, c s ≤ K * M := by
  calc ∑ s : Fin K, c s ≤ ∑ _s : Fin K, M := Finset.sum_le_sum (fun s _ => hc s)
    _ = K * M := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The residual amplification socket.**  `f` has an *exact* count-mod-`p` multiset representation of degree `≤ D`: a
family of `K` monomials of degree `≤ D` with multiplicities `c` and a decode `h` such that `f = h ∘ saCount` over the
`AND`-copy multiset.  Producing this from an `F_p`-span *approximant* (entry 204) is the `3/4`→exact amplification plus
the span-coefficient extraction.  Stated, not proved. -/
def ExactCountModPRep (f : (Fin n → Bool) → Bool) (D : ℕ) : Prop :=
  ∃ (K : ℕ) (base : Fin K → Finset (Fin n)) (c : Fin K → ℕ) (h : ℕ → Bool),
    (∀ s, (base s).card ≤ D) ∧
      f = fun x => h (saCount (fun q : Σ s : Fin K, Fin (c s) => base q.1) x)

/-- **The bridge via the count-mod-`p` collapse (PROVED).**  An exact count-mod-`p` representation of `f` (degree `≤ D`)
yields a `SYM∘AND` form of `f` of fan-in `≤ D` and size `∑_s c_s` — the count-mod-`p` arithmetic discharged, leaving
only the amplification socket `ExactCountModPRep`. -/
theorem bridge_via_countModP (f : (Fin n → Bool) → Bool) (D : ℕ) (hrep : ExactCountModPRep f D) :
    ∃ m, HasSymAndFormFanIn f m D := by
  obtain ⟨K, base, c, h, hdeg, hfe⟩ := hrep
  exact ⟨∑ s : Fin K, c s, hfe ▸ countModP_collapse base c h hdeg⟩

end PallLean.Paper93.DeepMath.PathB.ACC0CountModP

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountModP.saCount_sigma_cast
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountModP.countModP_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CountModP.bridge_via_countModP
