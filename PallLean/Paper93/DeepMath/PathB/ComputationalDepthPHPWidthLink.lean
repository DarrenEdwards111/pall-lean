import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPHPProofSpaceForcing

/-!
# Discharging `phpWidthLink` down to the BSW flip lemma (the injection + assembly, proved)

`ComputationalDepthPHPProofSpaceForcing.lean` left `phpWidthLink` (bipartite expansion ⇒ width) as a named
hypothesis.  This file **proves `phpWidthLink`** — as `php_width_ge_of_medium` — **modulo the per-pigeon flip
lemma**, which is the genuine irreducible Haken / Ben-Sasson–Wigderson combinatorial core.  Everything around
it is proved here.

## What is proved

* `php_pigeons_subset_width` — **the injection (the clean PHP-specific core).**  If, for every pigeon `p` in a
  set `S`, the clause `C` mentions some variable `(p, h)`, then `|S| ≤ width C`.  This is *cleaner* than
  Tseitin's boundary injection: PHP variables are pigeon-indexed `(p, h)`, so distinct pigeons map to distinct
  clause variables immediately — `S ⊆ C.image (pigeon-of-literal)`.
* `php_width_ge_of_medium` — **`phpWidthLink` proved from the flip lemma.**  A clause of medium semantic
  measure (`t ≤ μ < 2t`) has width `≥ t`: the minimal implying pigeon-set `S` has `|S| = μ ∈ [t, 2t)`, the
  flip lemma gives each pigeon of `S` a clause variable, and the injection bounds `width ≥ |S| ≥ t`.  The
  minimality/measure assembly reuses `SemanticMeasure.exists_implies_measure` / `measure_le_of_implies`.

## The remaining input (named, not faked) — the BSW flip lemma

`flip` (the hypothesis of `php_width_ge_of_medium`):

> for a *minimal* implying pigeon-set `S` of `C`, every pigeon `p ∈ S` has `C` mentioning a variable `(p, h)`.

This is Haken's core: by minimality there is an assignment satisfying `S \ {p}`'s pigeon-axioms but not `C`;
in it `p` is unplaced; placing `p` in a free incident hole `h` (which exists by the bipartite expansion of the
PHP graph) repairs `S` and so satisfies `C`, and the only change is at `(p, h)`, so `C` mentions it.  The
*free-hole-exists* step is exactly the bipartite-expansion content — a real theorem, **named here, not
proved** (the complete-bipartite case is Haken's bottleneck argument; the bounded-degree case is BSW
graph-PHP).

## Honest status

`phpWidthLink` is now a **theorem given the flip lemma** — the injection and the measure assembly are proved
and reused.  The only remaining input is the per-pigeon flip (free hole ⇐ expansion), the genuine Haken/BSW
combinatorial core, isolated and labelled.  So `phpWidthLink` is reduced from a monolithic hypothesis to its
one irreducible expansion ingredient.
-/

namespace PallLean.Paper93.DeepMath.PathB.PHPProofSpace

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-- **The injection (proved, the clean PHP core).**  If every pigeon `p ∈ S` has the clause `C` mention a
variable `(p, h)`, then `|S| ≤ width C` — distinct pigeons give distinct clause variables. -/
theorem php_pigeons_subset_width {m n : ℕ} (S : Finset (Fin m)) (C : ResolutionClause (PHPLit m n))
    (hmem : ∀ p ∈ S, ∃ h : Fin n, ∃ b : Bool, (((p, h), b) : PHPLit m n) ∈ C) :
    S.card ≤ ResolutionClause.width C := by
  classical
  have hsub : S ⊆ C.image (fun l : PHPLit m n => l.1.1) := by
    intro p hp
    obtain ⟨h, b, hin⟩ := hmem p hp
    exact Finset.mem_image.mpr ⟨((p, h), b), hin, rfl⟩
  calc S.card ≤ (C.image (fun l : PHPLit m n => l.1.1)).card := Finset.card_le_card hsub
    _ ≤ C.card := Finset.card_image_le
    _ = ResolutionClause.width C := rfl

/-- **`phpWidthLink` proved, modulo the flip lemma.**  Given the BSW flip lemma `flip` (a minimal implying
pigeon-set's every pigeon appears as a variable of `C`), a clause of medium semantic measure (`t ≤ μ < 2t`)
has width `≥ t`.  The minimality and measure bookkeeping are proved here; only `flip` (the expansion/free-hole
core) is assumed. -/
theorem php_width_ge_of_medium {m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (phpConstr : ι → (Fin m × Fin n → Bool) → Prop)
    (pigeonOf : ι → Fin m)
    (hunsat : ∀ a : Fin m × Fin n → Bool, ∃ i, ¬ phpConstr i a)
    (flip : ∀ {C : ResolutionClause (PHPLit m n)} {S : Finset ι},
        SemanticMeasure.Implies phpSat phpConstr S C →
        (∀ i ∈ S, ¬ SemanticMeasure.Implies phpSat phpConstr (S.erase i) C) →
        ∀ i ∈ S, ∃ h : Fin n, ∃ b : Bool, (((pigeonOf i, h), b) : PHPLit m n) ∈ C)
    {t : ℕ} {C : ResolutionClause (PHPLit m n)}
    (hpigInj : Function.Injective pigeonOf)
    (hlo : t ≤ SemanticMeasure.measure phpSat phpConstr C)
    (hhi : SemanticMeasure.measure phpSat phpConstr C < 2 * t) :
    t ≤ ResolutionClause.width C := by
  classical
  obtain ⟨S, hSimp, hScard⟩ := SemanticMeasure.exists_implies_measure phpSat phpConstr hunsat C
  have htS : t ≤ S.card := by rw [hScard]; exact hlo
  have hmin : ∀ i ∈ S, ¬ SemanticMeasure.Implies phpSat phpConstr (S.erase i) C := by
    intro i hi himp
    have hle := SemanticMeasure.measure_le_of_implies phpSat phpConstr himp
    rw [Finset.card_erase_of_mem hi, hScard] at hle
    omega
  have hmem := flip hSimp hmin
  -- inject the pigeons `pigeonOf '' S` into `C`'s variables
  have hsub : S.image pigeonOf ⊆ C.image (fun l : PHPLit m n => l.1.1) := by
    intro p hp
    obtain ⟨i, hiS, hip⟩ := Finset.mem_image.mp hp
    obtain ⟨h, b, hin⟩ := hmem i hiS
    exact Finset.mem_image.mpr ⟨((pigeonOf i, h), b), hin, by rw [hip]⟩
  have hcard : S.card ≤ ResolutionClause.width C := by
    calc S.card = (S.image pigeonOf).card := (Finset.card_image_of_injective S hpigInj).symm
      _ ≤ (C.image (fun l : PHPLit m n => l.1.1)).card := Finset.card_le_card hsub
      _ ≤ C.card := Finset.card_image_le
      _ = ResolutionClause.width C := rfl
  exact le_trans htS hcard

end PallLean.Paper93.DeepMath.PathB.PHPProofSpace

#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.php_pigeons_subset_width
#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.php_width_ge_of_medium
