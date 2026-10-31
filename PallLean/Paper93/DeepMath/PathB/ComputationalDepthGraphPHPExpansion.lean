import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPHPProofSpaceForcing

/-!
# BSW graph-PHP: the three combinatorial cores of the flip lemma (proved)

`ComputationalDepthPHPWidthLink.lean` reduced `phpWidthLink` to the **flip lemma** (minimal implying
pigeon-set ⇒ each pigeon a clause variable).  This file proves the **three combinatorial cores** of that
flip for *bounded-degree expander graph-PHP* — the genuine Ben-Sasson–Wigderson ingredients — leaving only
the matching-measure construction (the "exactly-`S`" semantics) as the residual.

## The three proved cores

1. **`pigeonhole_unplaced`** — *unsatisfiability*.  If `n < m`, any injective placement of pigeons into holes
   leaves a pigeon unplaced.  (`Fintype.card_le_of_injective` ⇒ `m ≤ n`, contradiction.)  This is the
   `hunsat` ingredient.
2. **`php_flip_mem_clause`** — *the flip mechanism*.  If extending an assignment at one variable `v` to
   `true` newly satisfies the clause `C` (satisfied after, not before), then `(v, true) ∈ C`.  This is the
   logical core of the flip: a single-variable repair that newly satisfies `C` pins a `C`-variable.
3. **`free_hole_of_unique_neighbor`** — *the expansion ingredient*.  If `h` is a **unique neighbour** of `p`
   relative to `S` (`h ∈ nbr p` but `h ∉ nbr q` for every other `q ∈ S`) and a matching `M` places only
   pigeons of `S\{p}`, then `h` is **free** under `M`.  This is where bipartite boundary expansion enters: a
   set with `≥ c·|S|` unique-neighbour holes gives every relevant pigeon a private free hole.

## How they assemble (and the residual)

The flip lemma is: minimal `S` ⇒ a counterexample matching `M` of `S\{p}` falsifies `C` with `p` unplaced
(core 1 forces `p` unplaced: a placed `p` would satisfy `S`, hence `C`); a unique-neighbour hole `h` of `p`
is free under `M` (core 3); extending `M` by `p ↦ h` satisfies `S`, hence `C`, changing only `(p,h)` — so
`(p,h) ∈ C` (core 2).  Distinct pigeons give distinct variables (`php_pigeons_subset_width`, previous file),
so `width ≥ |S|`.

**The residual (named, not faked).**  Cores 1–3 are proved.  Wiring them needs the *matching-based measure*:
the implication `S ⊨ C` quantified over matchings whose domain is **exactly** `S` (so the counterexample
places only `S\{p}`, making core 3 apply), and its subadditivity under resolution.  That "exactly-`S`"
measure is the genuine BSW measure construction — *different* from the generic `SemanticMeasure` (over all
assignments) — and is the remaining work.  So graph-PHP's flip is reduced to the matching-measure
construction, with its three combinatorial hearts proved here.
-/

namespace PallLean.Paper93.DeepMath.PathB.PHPProofSpace

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-- **Core 1 — pigeonhole unsatisfiability (proved).**  If `n < m`, any injective placement of the `m`
pigeons into `n` holes (`place p = some h`, injective on placed pigeons) leaves some pigeon unplaced. -/
theorem pigeonhole_unplaced {m n : ℕ} (hmn : n < m) (place : Fin m → Option (Fin n))
    (hinj : ∀ p q (h : Fin n), place p = some h → place q = some h → p = q) :
    ∃ p, place p = none := by
  by_contra hall
  push_neg at hall
  -- every pigeon placed: build an injection Fin m ↪ Fin n
  let f : Fin m → Fin n := fun p => (place p).get (Option.isSome_iff_ne_none.mpr (hall p))
  have hf : Function.Injective f := by
    intro p q hpq
    have hp : place p = some (f p) := (Option.some_get _).symm
    have hq : place q = some (f q) := (Option.some_get _).symm
    rw [hpq] at hp
    exact hinj p q (f q) hp hq
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at this
  omega

/-- **Core 2 — the flip mechanism (proved).**  If extending `a` at variable `v` to `true` newly satisfies
`C` (satisfied after the update, not before), then the positive literal `(v, true)` is in `C`.  A
single-variable repair that newly satisfies `C` pins a `C`-variable. -/
theorem php_flip_mem_clause {m n : ℕ} (a : Fin m × Fin n → Bool) (v : Fin m × Fin n)
    (C : ResolutionClause (PHPLit m n))
    (hsat : SemanticMeasure.clauseSat phpSat (Function.update a v true) C)
    (hno : ¬ SemanticMeasure.clauseSat phpSat a C) :
    ((v, true) : PHPLit m n) ∈ C := by
  obtain ⟨l, hlC, hl⟩ := hsat
  simp only [phpSat] at hl
  by_cases hv : l.1 = v
  · have hl2 : l.2 = true := by rw [hv, Function.update_self] at hl; exact hl.symm
    have : l = ((v, true) : PHPLit m n) := Prod.ext hv hl2
    rwa [this] at hlC
  · rw [Function.update_of_ne hv] at hl
    exact absurd ⟨l, hlC, hl⟩ hno

/-- **Core 3 — free hole from unique neighbour (the expansion ingredient, proved).**  If `h` is a unique
neighbour of `p` relative to `S` (`h ∈ nbr p`, and `h ∉ nbr q` for every other `q ∈ S`), and the matching
`M` places only pigeons of `S \ {p}` into their neighbourhoods, then no pigeon is placed in `h`: `h` is free
under `M`. -/
theorem free_hole_of_unique_neighbor {m n : ℕ} (nbr : Fin m → Finset (Fin n))
    (S : Finset (Fin m)) (p : Fin m) (h : Fin n)
    (huniq : ∀ q ∈ S, q ≠ p → h ∉ nbr q)
    (M : Fin m → Option (Fin n))
    (hrange : ∀ q (h' : Fin n), M q = some h' → h' ∈ nbr q)
    (honly : ∀ q (h' : Fin n), M q = some h' → q ∈ S ∧ q ≠ p) :
    ∀ q, M q ≠ some h := by
  intro q hq
  obtain ⟨hqS, hqp⟩ := honly q h hq
  exact huniq q hqS hqp (hrange q h hq)

end PallLean.Paper93.DeepMath.PathB.PHPProofSpace

#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.pigeonhole_unplaced
#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.php_flip_mem_clause
#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.free_hole_of_unique_neighbor
