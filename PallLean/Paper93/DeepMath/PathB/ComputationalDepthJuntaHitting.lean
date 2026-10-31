import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHittingSet

/-!
# An arity-growing restricted class with a small hitting set: `k`-juntas

`BoundedArityHitting` realized the poly-size hitting set only for **bounded** arity (size `(d+1)ⁿ`,
polynomial in `d` but exponential in `n`).  This file gives a genuinely **arity-growing** class — the
number of variables `n` is unbounded — that still admits a *small* hitting set: the class of
**`k`-juntas**, polynomials that depend on at most `k` of the `n` variables.

(A note on scope: the fully general "sparse polynomial" hitting set of Klivans–Spielman needs the
prime-isolation / Kronecker-substitution machinery — a much larger grind.  `k`-juntas are the clean,
classic restricted class that already exhibits the phenomenon and is fully provable from Schwartz–
Zippel, so that is what we formalize here.)

Fix an embedding `e : Fin k ↪ Fin n` selecting the `k` relevant coordinates, a base point `base` for
the irrelevant ones, and a side set `S`.  A `k`-junta along `e` is `rename e q` for a `k`-variable
polynomial `q`.

* **`juntaGrid`** — extend the `k`-variable grid `Sᵏ` to `Fⁿ` by filling non-junta coordinates with
  `base`.
* **`juntaGrid_hits` (proved)** — for any nonzero `q` with `deg q < #S`, the junta `rename e q` is
  non-vanishing at some point of `juntaGrid`.  (Schwartz–Zippel on `q`, extended along `e`; `eval`
  commutes with `rename` and the extension restricts to the witness on the junta coordinates.)
* **`juntaGrid_card` (proved)** — the junta grid has `≤ (#S)ᵏ` points — **independent of the ambient
  dimension `n`**, in stark contrast to the full `(#S)ⁿ` grid.
* **`juntaUnion_card` (proved)** — ranging `e` over a family `E` of embeddings, the union hits every
  `k`-junta whose relevant set is covered by `E`, with size `≤ #E · (#S)ᵏ = poly(n)` for fixed `k`
  (taking `E` = all `k`-subsets gives `\binom{n}{k}` copies, polynomial in `n`).

**Honest scope.**  This is a real, unconditional small hitting set for an arity-growing class: the
per-embedding grid size does not depend on `n` at all, and the union over `\binom{n}{k}` embeddings is
`poly(n)` for fixed `k`.  The one elementary step not formalized here is the *covering* — that every
degree-`d` `k`-junta equals `rename e q` for some `e ∈ E` (standard support analysis) — which links
`juntaGrid_hits` to the full unknown-support class.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.JuntaHitting

open PallLean.Paper93.DeepMath.PathB.SchwartzZippel

variable {F : Type*} [Field F] [DecidableEq F]

open scoped Classical in
/-- The **junta grid**: extend each point of the `k`-variable grid `Sᵏ` to `Fⁿ` by filling the
non-junta coordinates (those outside `range e`) with the fixed base value. -/
noncomputable def juntaGrid {k n : ℕ} (e : Fin k ↪ Fin n) (base : Fin n → F) (S : Finset F) :
    Finset (Fin n → F) :=
  (Fintype.piFinset (fun _ : Fin k => S)).image (fun x => Function.extend (⇑e) x base)

/-- **The junta grid hits every `k`-junta along `e` (proved).**  For a nonzero `k`-variable
polynomial `q` of total degree `< #S`, the `n`-variable junta `rename e q` — which depends only on
the `k` coordinates picked by `e` — is non-vanishing at some point of `juntaGrid e base S`. -/
theorem juntaGrid_hits {k n : ℕ} (e : Fin k ↪ Fin n) (base : Fin n → F) (S : Finset F)
    (q : MvPolynomial (Fin k) F) (hq : q ≠ 0) (hdeg : q.totalDegree < S.card) :
    ∃ f ∈ juntaGrid e base S, MvPolynomial.eval f (MvPolynomial.rename (⇑e) q) ≠ 0 := by
  obtain ⟨x, hx, hxne⟩ := sz_mv_exists_nonroot hq S hdeg
  refine ⟨Function.extend (⇑e) x base, ?_, ?_⟩
  · simp only [juntaGrid]
    exact Finset.mem_image_of_mem _ hx
  · rw [MvPolynomial.eval_rename, Function.extend_comp e.injective]
    exact hxne

/-- **The junta grid is small — its size is INDEPENDENT of the ambient dimension `n` (proved).**  It
has at most `(#S)ᵏ` points; for fixed junta-arity `k` this does not grow with the number of variables
`n`, unlike the full `(#S)ⁿ` grid. -/
theorem juntaGrid_card {k n : ℕ} (e : Fin k ↪ Fin n) (base : Fin n → F) (S : Finset F) :
    (juntaGrid e base S).card ≤ S.card ^ k := by
  classical
  refine le_trans Finset.card_image_le ?_
  simp [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The union over a family of embeddings is still small (proved).**  Ranging the relevant-set
embedding `e` over a family `E`, the union of junta grids has size `≤ #E · (#S)ᵏ`.  Taking `E` to be
all `k`-subsets gives `\binom{n}{k}` copies, so the hitting set for the full `k`-junta class is
`poly(n)` for fixed `k` — a small hitting set for an arity-growing class. -/
theorem juntaUnion_card {k n : ℕ} (E : Finset (Fin k ↪ Fin n)) (base : Fin n → F) (S : Finset F) :
    (E.biUnion (fun e => juntaGrid e base S)).card ≤ E.card * S.card ^ k := by
  classical
  calc (E.biUnion (fun e => juntaGrid e base S)).card
      ≤ ∑ e ∈ E, (juntaGrid e base S).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ E, S.card ^ k := Finset.sum_le_sum (fun e _ => juntaGrid_card e base S)
    _ = E.card * S.card ^ k := by rw [Finset.sum_const, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.JuntaHitting

#print axioms PallLean.Paper93.DeepMath.PathB.JuntaHitting.juntaGrid_hits
#print axioms PallLean.Paper93.DeepMath.PathB.JuntaHitting.juntaGrid_card
#print axioms PallLean.Paper93.DeepMath.PathB.JuntaHitting.juntaUnion_card
