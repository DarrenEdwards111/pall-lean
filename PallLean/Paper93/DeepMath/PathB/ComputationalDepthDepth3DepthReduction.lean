import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeSwap

/-!
# Block-DT model, foundation 14: one full depth-reduction step `d → d-1` (branch only)

The DT↔CNF/DNF swap (`dnf_cnf_swap`) re-expresses each *shallow* bottom gate as a bounded-width CNF (or
DNF).  The second half of the switching-lemma depth reduction is the **associativity collapse**: an
unbounded-fan-in `AND` of CNFs is itself a single CNF (`AND`-of-`AND`s flattens), and dually `OR` of
DNFs is a single DNF.  Composing the two: a gate layer of shallow decision trees feeding one top
connective merges into that connective, removing one alternation level — `depth d → d-1`.

* `bigAnd_eq_cnf` / `bigAndCNF_width` — `AND` of shallow DTs (each depth `≤ t`) is a width-`≤ t` CNF
  (clauses = `flatMap toCNF`); the top `AND` absorbs the gate `AND`s.
* `bigOr_eq_dnf` / `bigOrDNF_width` — dually, `OR` of shallow DTs is a width-`≤ t` DNF.
* `depth_reduction_step` — the packaged step: a one-level layer of depth-`≤ t` gates collapses into a
  single width-`≤ t` CNF (under `AND`) and DNF (under `OR`), the eval preserved.

Clean, no `sorry`, no `native_decide`.  AC⁰/depth-3; not P≠NP-strength (this is AC⁰ depth-reduction
machinery, which tops out at AC⁰).
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace DTree

variable {n : ℕ}

/-! ### `AND` of shallow decision trees collapses to one CNF -/

/-- **`AND`-of-DTs is a CNF.**  An unbounded-fan-in `AND` of decision trees accepts `x` iff the
concatenated rejecting-path CNF (`flatMap toCNF`) is satisfied — the top `AND` absorbs each gate's `AND`
of clauses. -/
theorem bigAnd_eq_cnf (ts : List (DTree n)) (x : Fin n → Bool) :
    (∀ t ∈ ts, t.eval x = true) ↔ cnfSat x (ts.flatMap toCNF) := by
  simp only [cnfSat, List.mem_flatMap]
  constructor
  · intro h c ⟨t, ht, hc⟩
    exact (eval_eq_cnf t x).mp (h t ht) c hc
  · intro h t ht
    refine (eval_eq_cnf t x).mpr ?_
    intro c hc
    exact h c ⟨t, ht, hc⟩

/-- **Width bound for the merged CNF.**  If every gate has depth `≤ d`, every clause of the merged CNF
has width `≤ d`. -/
theorem bigAndCNF_width (ts : List (DTree n)) (d : ℕ) (hd : ∀ t ∈ ts, t.depth ≤ d) :
    ∀ c ∈ ts.flatMap toCNF, c.length ≤ d := by
  intro c hc
  rw [List.mem_flatMap] at hc
  obtain ⟨t, ht, hct⟩ := hc
  exact le_trans (toCNF_width t c hct) (hd t ht)

/-! ### `OR` of shallow decision trees collapses to one DNF -/

/-- **`OR`-of-DTs is a DNF.**  An unbounded-fan-in `OR` of decision trees accepts `x` iff the
concatenated accepting-path DNF (`flatMap toDNF`) is satisfied. -/
theorem bigOr_eq_dnf (ts : List (DTree n)) (x : Fin n → Bool) :
    (∃ t ∈ ts, t.eval x = true) ↔ dnfSat x (ts.flatMap toDNF) := by
  simp only [dnfSat, List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hev⟩
    obtain ⟨s, hs, hsat⟩ := (eval_eq_dnf t x).mp hev
    exact ⟨s, ⟨t, ht, hs⟩, hsat⟩
  · rintro ⟨s, ⟨t, ht, hs⟩, hsat⟩
    exact ⟨t, ht, (eval_eq_dnf t x).mpr ⟨s, hs, hsat⟩⟩

/-- **Width bound for the merged DNF.** -/
theorem bigOrDNF_width (ts : List (DTree n)) (d : ℕ) (hd : ∀ t ∈ ts, t.depth ≤ d) :
    ∀ s ∈ ts.flatMap toDNF, s.length ≤ d := by
  intro s hs
  rw [List.mem_flatMap] at hs
  obtain ⟨t, ht, hst⟩ := hs
  exact le_trans (toDNF_width t s hst) (hd t ht)

/-- **One depth-reduction step `d → d-1`.**  A single layer of decision-tree gates, each of depth
`≤ d`, feeding one top connective collapses into a *single* bounded-width normal form, eval preserved:
under `AND` it becomes a width-`≤ d` CNF, under `OR` a width-`≤ d` DNF.  The gate layer is absorbed
into the top connective — one alternation level removed. -/
theorem depth_reduction_step (ts : List (DTree n)) (d : ℕ) (hd : ∀ t ∈ ts, t.depth ≤ d)
    (x : Fin n → Bool) :
    ((∀ t ∈ ts, t.eval x = true) ↔ cnfSat x (ts.flatMap toCNF))
      ∧ ((∃ t ∈ ts, t.eval x = true) ↔ dnfSat x (ts.flatMap toDNF))
      ∧ (∀ c ∈ ts.flatMap toCNF, c.length ≤ d)
      ∧ (∀ s ∈ ts.flatMap toDNF, s.length ≤ d) :=
  ⟨bigAnd_eq_cnf ts x, bigOr_eq_dnf ts x, bigAndCNF_width ts d hd, bigOrDNF_width ts d hd⟩

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.bigAnd_eq_cnf
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.bigOr_eq_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.depth_reduction_step
