import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingListInj

/-!
# Unconditional switching count (loose label), fully composed

**STATUS: REAL, UNCONDITIONAL (loose label).  TIGHT `(2w)^s` NEEDS THE FLATTENED REPLAY.**

With the canonical encoding now *proved* injective (`circuitPathList_inj`), the
whole switching machine composes into an **unconditional** count — no `hrec`
hypothesis, the injectivity is discharged:

  `|Bad| ≤ |{circuitPath ρ : ρ ∈ Bad}| · ((2^w)^m)^numTerms`.

This is the genuine switching cardinality bound for the canonical path encoding,
fully assembled from the proved pieces: the path construction, its injectivity
(`circuitPathList_inj`), the label membership (`circuitPathList_mem_labelSpace`),
and the label-space bound (`circuitLabelSpace_card_le`).

It is **loose** — the label factor is `((2^w)^m)^numTerms` (per-clause `2^w`,
multiplied over all clauses/terms), exponential in circuit size, so it does not
close the switching gate.  Tightening to `(2w)^s` requires the *flattened*
per-variable path (one root-leaf path of length `≤ s`, each step `≤ 2w`), whose
recovery needs the active-clause replay that removes the per-clause-count factor —
the genuine remaining hard construction, not a representation change.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Unconditional switching count (loose label).**  The canonical encoding
`ρ ↦ (circuitPath ρ ts a, circuitPathList ρ ts a)` is injective (`circuitPathList_inj`)
and its label lands in `circuitLabelSpace ts`, so `Bad` injects into
`(its path-restriction image) × circuitLabelSpace`, giving the count. -/
theorem circuit_switching_count (ts : List (Term n)) (a : Fin n → Bool) {w m : ℕ}
    (hw : ∀ T ∈ ts, ∀ C ∈ T.clauses, C.width ≤ w) (hm : ∀ T ∈ ts, T.clauses.length ≤ m)
    (Bad : Finset (Restriction n)) :
    Bad.card
      ≤ (Bad.image (fun ρ => circuitPath ρ ts a)).card * ((2 ^ w) ^ m) ^ ts.length := by
  classical
  have hsub : ∀ ρ ∈ Bad, (fun ρ => (circuitPath ρ ts a, circuitPathList ρ ts a)) ρ
      ∈ (Bad.image (fun ρ => circuitPath ρ ts a)) ×ˢ circuitLabelSpace ts := by
    intro ρ hρ
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hρ, circuitPathList_mem_labelSpace ts ρ a⟩
  have hinj : Set.InjOn (fun ρ => (circuitPath ρ ts a, circuitPathList ρ ts a)) ↑Bad := by
    intro ρ _ σ _ heq
    exact circuitPathList_inj ts a (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  calc Bad.card
      ≤ ((Bad.image (fun ρ => circuitPath ρ ts a)) ×ˢ circuitLabelSpace ts).card :=
        Finset.card_le_card_of_injOn _ hsub hinj
    _ = (Bad.image (fun ρ => circuitPath ρ ts a)).card * (circuitLabelSpace ts).card :=
        Finset.card_product _ _
    _ ≤ (Bad.image (fun ρ => circuitPath ρ ts a)).card * ((2 ^ w) ^ m) ^ ts.length :=
        mul_le_mul_left' (circuitLabelSpace_card_le ts w m hw hm) _

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.circuit_switching_count
