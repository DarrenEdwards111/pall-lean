import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingTokenCount

/-!
# Depth-3 collapse via both switching-count routes

The switching count now has two proven labeled forms (see `ComputationalDepthSwitchingTokenCount`):

* **Route A** — `canon_count_pathLenBad`: `|pathLenBad cs s| ≤ |Short| · (2w)^s` (delimiter-free,
  clean `(2w)^s`, needs nonempty blocks `hne`);
* **Route B** — `canonFlatLabel_switching_count`: `|Bad| ≤ |Short| · (w+1)^L` (tokenized,
  `hne`-free, label length `L = s + #blocks`).

This file performs the **collapse step** — count ⟹ good restriction — through *both* routes, and a
combiner that uses whichever bound is smaller.

* `exists_good_of_count` — generic pigeonhole: any bad set with `|Bad| ≤ M < |univ|` (the total
  restriction count `3^n`) misses some restriction.
* `depth3_collapse_markLabel` — Route A: under `|Short|·(2w)^s < 3^n`, a good restriction outside
  `pathLenBad cs s` exists.
* `depth3_collapse_flatLabel` — Route B: under `|Short|·(w+1)^L < 3^n`, a good restriction outside
  `Bad` exists, **with no `hne`**.
* `depth3_collapse_both` — the combiner: with both bounds in hand, `min` of the two parameter
  products below `3^n` suffices.

A good restriction `ρ` has small canonical path length, hence (via the depth↔`s` tie and
`SearchDischarge.canonicalDT_ldderiv`) the restricted DNF collapses to a short, width-bounded `LDeriv`
resolution refutation — the depth-3 collapse conclusion.  Composing with the Tseitin width *lower*
bound (`LDeriv.tseitin_size_width`) is the contradiction the lower-bound argument turns on; that
final composition is left to the application and not asserted here.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Generic pigeonhole collapse.**  If the bad set is bounded by `M`, and `M` is below the total
restriction count, then some restriction is good (not bad). -/
theorem exists_good_of_count {Bad : Finset (Restriction n)} {M : ℕ}
    (hcount : Bad.card ≤ M) (hlt : M < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ρ ∉ Bad := by
  have hBad : Bad.card < (Finset.univ : Finset (Restriction n)).card := lt_of_le_of_lt hcount hlt
  by_contra h
  push_neg at h
  exact absurd (Finset.card_le_card (fun ρ _ => h ρ)) (not_le.mpr hBad)

/-- **Route A collapse (delimiter-free `(2w)^s`).**  Under the parameter inequality, a good
restriction outside the path-length bad set exists. -/
theorem depth3_collapse_markLabel {w s : ℕ} [NeZero w] {cs : List (Clause n)}
    {Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hne : ∀ ρ ∈ pathLenBad cs s, ∀ b ∈ canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))), b ≠ [])
    (hmem : ∀ ρ ∈ pathLenBad cs s, complete ρ (encLits ρ cs) ∈ Short)
    (hlt : Short.card * (2 * w) ^ s < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ρ ∉ pathLenBad cs s :=
  exists_good_of_count (canon_count_pathLenBad hcs hwidth hne hmem) hlt

/-- **Route B collapse (tokenized `(w+1)^L`, `hne`-free).**  Under the parameter inequality, a good
restriction outside the bad set exists, with no nonempty-block hypothesis. -/
theorem depth3_collapse_flatLabel {w L : ℕ} [NeZero w] {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hlen : ∀ ρ ∈ Bad, (canonFlatLabel w ρ cs).length = L)
    (hmem : ∀ ρ ∈ Bad, complete ρ (encLits ρ cs) ∈ Short)
    (hlt : Short.card * (w + 1) ^ L < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ρ ∉ Bad :=
  exists_good_of_count (canonFlatLabel_switching_count hcs hwidth hlen hmem) hlt

/-- **The combiner — use whichever route is tighter.**  Given both route bounds on the same bad
set, the smaller one below `3^n` yields a good restriction. -/
theorem depth3_collapse_both {Bad : Finset (Restriction n)} {M_A M_B : ℕ}
    (hA : Bad.card ≤ M_A) (hB : Bad.card ≤ M_B)
    (hlt : min M_A M_B < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ρ ∉ Bad :=
  exists_good_of_count (le_min hA hB) hlt

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.depth3_collapse_markLabel
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.depth3_collapse_flatLabel
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.depth3_collapse_both
