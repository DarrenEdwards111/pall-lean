import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameModpAndFlatten

/-!
# The composite middle-modulus case: no low-degree flattening exists (proved)

The prime-power case flattened a `MOD_p∘AND` gate (`char`-matching) into an exact degree-`(|F|−1)·D` monomial-`AND`
polynomial (`…ModpAndFlatten`).  For a **composite / coprime** middle modulus the fast-SAT bottom-`AND` reduction needs
the same low-degree flattening — and this file proves **it does not exist**.

A middle `MOD_q` gate with `q` coprime to `char` is not a function of the `char`-collapsed count (C14), so it can only be
arithmetised over an extension field via an order-`q` root of unity — which is `omegaFn`, and `omegaFn` has **high**
N-Frame complexity (`≥ ⌈n/2⌉`, C11).  Combined with "low degree ⟹ low N-Frame complexity" (C10):

  `composite_middle_no_lowdeg_flatten` — the coprime `MOD_q` gate is **not** the cube-function of *any* polynomial of
        total degree `< ⌈n/2⌉`.  No low-degree flattening exists.

So the fork is now proved on both sides, in the same measure:
* **prime-power** (`char`-matching) — `nframeComplexity_charModAndFn_le`: flattens, `NFrameComplexity ≤ (|F|−1)·D` (LOW);
* **composite / coprime** — `composite_middle_no_lowdeg_flatten`: `NFrameComplexity ≥ ⌈n/2⌉` (HIGH), no flattening below
        `⌈n/2⌉`.

`composite_flatten_fork` bundles the contrast.

## Honest scope — this is the barrier, proved, not crossed

This does **not** compile a composite-`MOD` circuit into `SYM∘AND` — it proves that the low-degree route *cannot*.  The
composite middle modulus is the genuinely open case (`MOD_6` / `ACC⁰[6]`); every technique in this repo — polynomial and
algorithmic — reaches exactly this obstruction: the coprime modulus is high-degree over every field, so no low-degree
monomial-`AND` flattening exists.  Crossing it needs a fundamentally different idea; not built (and not fakeable).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The composite middle modulus has no low-degree flattening (proved)**: a coprime `MOD_q` gate (`omegaFn`, order-`q`
root, `char ≠ q`) is not `boolFn p` for any polynomial `p` of total degree `< ⌈n/2⌉`.  Its N-Frame complexity is `≥ ⌈n/2⌉`
(C11), while any degree-`<⌈n/2⌉` flattening would have N-Frame complexity `< ⌈n/2⌉` (C10) — contradiction. -/
theorem composite_middle_no_lowdeg_flatten {q : ℕ} (ω : F) (hω : orderOf ω = q) (hq2 : 2 ≤ q)
    (p : MvPolynomial (Fin n) F) (hdeg : p.totalDegree < n - n / 2) :
    omegaFn ω (Finset.univ : Finset (Fin n)) ≠ boolFn p := by
  intro heq
  have h1 := nframeComplexity_omegaFn_univ_ge (n := n) ω hω hq2
  rw [heq] at h1
  have h2 := nframeComplexity_boolFn_le p
  omega

/-- **The fork, both sides in one measure (proved)**.
* Prime-power (`char`-matching): a `MOD_p∘AND` gate of fan-in `≤ D` *flattens* — `NFrameComplexity ≤ (|F|−1)·D`.
* Composite / coprime: the `MOD_q` gate has `NFrameComplexity ≥ ⌈n/2⌉`, so it does **not** flatten below `⌈n/2⌉`.
The two are irreconcilable exactly when `(|F|−1)·D < ⌈n/2⌉` — the low-degree regime the fast-SAT needs. -/
theorem composite_flatten_fork {m D q : ℕ} (S : Fin m → Finset (Fin n)) (hDs : ∀ j, (S j).card ≤ D)
    (ω : F) (hω : orderOf ω = q) (hq2 : 2 ≤ q) :
    NFrameComplexity F (charModAndFn S) ≤ (Fintype.card F - 1) * D
      ∧ n - n / 2 ≤ NFrameComplexity F (omegaFn ω (Finset.univ : Finset (Fin n))) :=
  ⟨nframeComplexity_charModAndFn_le S hDs, nframeComplexity_omegaFn_univ_ge ω hω hq2⟩

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.composite_middle_no_lowdeg_flatten
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.composite_flatten_fork
