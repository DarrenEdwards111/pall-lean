import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCircuitPath

/-!
# Switching-count assembly (switching lemma, step 4)

**STATUS: REAL.  THE COUNTING BOUND ASSEMBLED; SEMANTIC "BADNESS" STILL ABSTRACT.**

Wires the canonical encoding pipeline (clause → term → circuit) into the
counting/injection scaffold to get the switching-lemma cardinality bound

  `|Bad| ≤ |Short| · ((2^w)^m)^numTerms`

for **any** set `Bad` of restrictions whose canonical encoding lands in `Short`
(width `w`, `m` clauses per term).  `Bad` is kept abstract here — the only
hypothesis is that fixing each bad `ρ` along its circuit selector lands in
`Short`.  Specialising `Bad` to "the canonical path is long / the circuit is
undecided with large residual" (and choosing `Short`, `w`, `m`) is the later
semantic step; this brick is the pure combinatorial count.

The one connective beyond pure wiring: `card_bad_le_of_label_bound` counts via the
*union* of selected coordinates (`circuitSel`), while the proved label bound is on
the *ordered* path space.  `circuitSel_eq` factors the union through the path
(`circuitSel ρ = unionLabel (circuitPathList ρ)`), so the union image is bounded by
the path-label space.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The union of all coordinates appearing in a nested path label. -/
def unionLabel : List (List (Finset (Fin n))) → Finset (Fin n)
  | [] => ∅
  | l :: ls => l.foldr (· ∪ ·) ∅ ∪ unionLabel ls

/-- `termSel` is the union of the term path label. -/
theorem termSel_eq :
    ∀ (cs : List (Clause n)) (ρ : Restriction n) (a : Fin n → Bool),
      termSel ρ cs a = (termPathList ρ cs a).foldr (· ∪ ·) ∅ := by
  intro cs
  induction cs with
  | nil => intro ρ a; simp [termSel, termPathList]
  | cons C cs ih =>
    intro ρ a
    simp only [termSel, termPathList, List.foldr_cons]
    rw [ih (fixOn ρ (canonicalSel ρ C) a) a]

/-- `circuitSel` is the union of the circuit path label. -/
theorem circuitSel_eq :
    ∀ (ts : List (Term n)) (ρ : Restriction n) (a : Fin n → Bool),
      circuitSel ρ ts a = unionLabel (circuitPathList ρ ts a) := by
  intro ts
  induction ts with
  | nil => intro ρ a; simp [circuitSel, circuitPathList, unionLabel]
  | cons T ts ih =>
    intro ρ a
    simp only [circuitSel, circuitPathList, unionLabel]
    rw [termSel_eq T.clauses ρ a, ih (termPath ρ T.clauses a) a]

/-- The union-set image of `Bad` is bounded by the path-label space. -/
theorem image_circuitSel_card_le (ts : List (Term n)) (a : Fin n → Bool)
    {Bad : Finset (Restriction n)} {w m : ℕ}
    (hw : ∀ T ∈ ts, ∀ C ∈ T.clauses, C.width ≤ w) (hm : ∀ T ∈ ts, T.clauses.length ≤ m) :
    (Bad.image (fun ρ => circuitSel ρ ts a)).card ≤ ((2 ^ w) ^ m) ^ ts.length := by
  have hsub : Bad.image (fun ρ => circuitSel ρ ts a)
      ⊆ (circuitLabelSpace ts).image unionLabel := by
    intro s hs
    obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.mp hs
    rw [circuitSel_eq]
    exact Finset.mem_image.mpr ⟨circuitPathList ρ ts a, circuitPathList_mem_labelSpace ts ρ a, rfl⟩
  calc (Bad.image (fun ρ => circuitSel ρ ts a)).card
      ≤ ((circuitLabelSpace ts).image unionLabel).card := Finset.card_le_card hsub
    _ ≤ (circuitLabelSpace ts).card := Finset.card_image_le
    _ ≤ ((2 ^ w) ^ m) ^ ts.length := circuitLabelSpace_card_le ts w m hw hm

/-- **Switching-count assembly.**  For any `Bad` whose canonical circuit encoding
lands in `Short`, the number of bad restrictions is at most
`|Short| · ((2^w)^m)^numTerms` — the switching-lemma cardinality bound.  `Bad`,
`Short`, the fixing values `D`, and the path values `a` are all abstract; only the
width `w` and clauses-per-term `m` bounds on the circuit are used. -/
theorem circuit_bad_card_le (ts : List (Term n)) (a : Fin n → Bool)
    (D : Restriction n → (Fin n → Bool)) {Bad Short : Finset (Restriction n)} {w m : ℕ}
    (hw : ∀ T ∈ ts, ∀ C ∈ T.clauses, C.width ≤ w) (hm : ∀ T ∈ ts, T.clauses.length ≤ m)
    (hmem : ∀ ρ ∈ Bad, fixOn ρ (circuitSel ρ ts a) (D ρ) ∈ Short) :
    Bad.card ≤ Short.card * ((2 ^ w) ^ m) ^ ts.length :=
  card_bad_le_of_label_bound (fun ρ => circuitSel ρ ts a) D Short
    (fun ρ _ => circuitSel_subset_freeVars ts ρ a) hmem
    (image_circuitSel_card_le ts a hw hm)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.circuitSel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.circuit_bad_card_le
