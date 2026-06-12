import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionSpace
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionSemanticMeasure

/-!
# A new forcing family: PHP (pigeonhole) proof-space, via the generic band engine

The least-action move (`SCOPE_NFRAME_OBSERVER_LAGRANGIAN.md`, route 3): a **new forcing family** in the
proof-space regime where the machinery already works.  The Tseitin total-space lower bound (`Option C`) was
*one* instantiation of a **generic** engine — `Blackboard.totalSpace_ge_of_medium_wide` is generic over
`(μ, subadditivity, axiom-bound, width-link)`.  This file extracts that engine and instantiates it for **PHP**.

## The generic proof-space forcing engine (PROVED, reused)

* `every_refutation_totalSpace_ge` — for *any* constraint family with a subadditive measure `μ`, axiom
  measure `≤ a < t`, a width link (`medium μ ⇒ wide`), and a root bound (`μ(⊥) ≥ t`), **every** blackboard
  refutation has total space `≥ W`.  One line from the band theorem.
* `proofSpaceMin`, `proofSpaceMin_ge_of_band` — the `min` total space over *all* refutations is `≥ W`: the
  proof-space forcing family (decompositions = refutations).

## The PHP instance

* The **subadditivity is proved** for PHP via the generic `SemanticMeasure.measure_resolvent_le` (with the
  literal-consistency `php_hcons`, proved).
* The **PHP-specific combinatorial inputs are explicit named hypotheses** (the demotion pattern — the classic
  Haken / bipartite-expansion content, real theorems, **not** faked here):
  * `hunsat` — PHP is globally unsatisfiable (`m > n` pigeons in holes);
  * `phpWidthLink` — bipartite expansion ⇒ width (a medium constraint set implies only wide clauses);
  * `phpRoot` — the root bound `μ(⊥) ≥ t`.
* `php_proofSpace_min_ge` — from these, **every PHP refutation has total space `≥ W`, so the `min` is `≥ W`**.

## Honest status

The **abstraction's reach is proved**: the same band engine that gives Tseitin proof-space gives PHP
proof-space, with subadditivity and the `min` packaging *proved* and reused.  The PHP-specific expansion
lower bound (Haken) is **named, not proved** — discharging `phpWidthLink`/`phpRoot`/`hunsat` is the genuine
PHP combinatorial work (its own real theorem).  So this is a *new forcing-family instance modulo the classic
PHP expansion bound* — the honest least-action increment, with the hard input isolated and labelled.
-/

namespace PallLean.Paper93.DeepMath.PathB.PHPProofSpace

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-! ## The generic proof-space forcing engine (proved, reused) -/

variable {Lit : Type*} [DecidableEq Lit] {compl : Lit → Lit} {Axiom : ResolutionClause Lit → Prop}

/-- **Generic: every refutation is forced `≥ W`.**  From a subadditive measure with axiom bound `a < t`, a
width link, and a root bound, every blackboard refutation has total space `≥ W`.  (One line from
`Blackboard.totalSpace_ge_of_medium_wide`.) -/
theorem every_refutation_totalSpace_ge {a t W : ℕ}
    (μ : ResolutionClause Lit → ℕ)
    (hsub : ∀ {C D : ResolutionClause Lit} (p : Lit),
        μ (ResolutionClause.resolvent compl C D p) ≤ μ C + μ D)
    (hax : ∀ {C : ResolutionClause Lit}, Axiom C → μ C ≤ a)
    (ht : a < t)
    (hwide : ∀ {C : ResolutionClause Lit}, t ≤ μ C → μ C < 2 * t →
        W ≤ ResolutionClause.width C)
    (hroot : t ≤ μ (∅ : ResolutionClause Lit))
    {M : Configuration Lit} (Ref : Blackboard compl Axiom M)
    (hbot : (∅ : ResolutionClause Lit) ∈ M) :
    W ≤ Blackboard.totalSpace Ref :=
  Blackboard.totalSpace_ge_of_medium_wide μ hsub hax ht hwide Ref ⟨∅, hbot, hroot⟩

/-- The set of total-space values of blackboard refutations of `Axiom`. -/
def refutationSpaces (compl : Lit → Lit) (Axiom : ResolutionClause Lit → Prop) : Set ℕ :=
  { b | ∃ (M : Configuration Lit) (Ref : Blackboard compl Axiom M),
      (∅ : ResolutionClause Lit) ∈ M ∧ b = Blackboard.totalSpace Ref }

/-- **The proof-space forcing family `min`.**  The least total space over all refutations. -/
noncomputable def proofSpaceMin (compl : Lit → Lit) (Axiom : ResolutionClause Lit → Prop) : ℕ :=
  sInf (refutationSpaces compl Axiom)

/-- **Generic: the `min` is forced `≥ W`.**  The proof-space forcing family has threshold `W`. -/
theorem proofSpaceMin_ge_of_band {a t W : ℕ}
    (μ : ResolutionClause Lit → ℕ)
    (hsub : ∀ {C D : ResolutionClause Lit} (p : Lit),
        μ (ResolutionClause.resolvent compl C D p) ≤ μ C + μ D)
    (hax : ∀ {C : ResolutionClause Lit}, Axiom C → μ C ≤ a)
    (ht : a < t)
    (hwide : ∀ {C : ResolutionClause Lit}, t ≤ μ C → μ C < 2 * t →
        W ≤ ResolutionClause.width C)
    (hroot : t ≤ μ (∅ : ResolutionClause Lit))
    (hne : (refutationSpaces compl Axiom).Nonempty) :
    W ≤ proofSpaceMin compl Axiom := by
  obtain ⟨M, Ref, hbot, heq⟩ := Nat.sInf_mem hne
  rw [proofSpaceMin, heq]
  exact every_refutation_totalSpace_ge μ hsub hax ht hwide hroot Ref hbot

/-! ## The PHP instance -/

/-- A PHP literal: `((pigeon, hole), b)` asserts `x_{p,h} = b`. -/
abbrev PHPLit (m n : ℕ) := (Fin m × Fin n) × Bool

/-- Complement of a PHP literal. -/
def phpCompl {m n : ℕ} (l : PHPLit m n) : PHPLit m n := (l.1, !l.2)

/-- Satisfaction: `a` satisfies `(v, b)` iff `a v = b`. -/
def phpSat {m n : ℕ} (a : Fin m × Fin n → Bool) (l : PHPLit m n) : Prop := a l.1 = l.2

/-- **Literal-consistency (proved).**  A PHP literal and its complement are never both satisfied. -/
theorem php_hcons {m n : ℕ} (a : Fin m × Fin n → Bool) (l : PHPLit m n) :
    phpSat a l → ¬ phpSat a (phpCompl l) := by
  simp only [phpSat, phpCompl]
  intro h
  rw [h]
  exact fun hc => by cases hl : l.2 <;> rw [hl] at hc <;> simp at hc

/-- **PHP proof-space forcing (the new instance).**  Given the PHP constraint family `phpConstr` and the
classic PHP combinatorial inputs as explicit hypotheses — `hunsat` (PHP unsatisfiable), `haxiom` (each axiom
implied by `≤ a` constraints), `phpWidthLink` (bipartite expansion ⇒ width), `phpRoot` (root bound) — **every
PHP refutation has total space `≥ W`, so the proof-space `min` is `≥ W`.**  Subadditivity and the `min`
packaging are *proved* (generic engine); only the PHP-specific expansion content is named. -/
theorem php_proofSpace_min_ge {m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (phpConstr : ι → (Fin m × Fin n → Bool) → Prop)
    (Axiom : ResolutionClause (PHPLit m n) → Prop)
    (hunsat : ∀ a : Fin m × Fin n → Bool, ∃ i, ¬ phpConstr i a)
    {a t W : ℕ}
    (haxiom : ∀ C, Axiom C →
      ∃ S : Finset ι, S.card ≤ a ∧ SemanticMeasure.Implies phpSat phpConstr S C)
    (ht : a < t)
    (phpWidthLink : ∀ {C : ResolutionClause (PHPLit m n)},
      t ≤ SemanticMeasure.measure phpSat phpConstr C →
      SemanticMeasure.measure phpSat phpConstr C < 2 * t →
      W ≤ ResolutionClause.width C)
    (phpRoot : t ≤ SemanticMeasure.measure phpSat phpConstr (∅ : ResolutionClause (PHPLit m n)))
    (hne : (refutationSpaces phpCompl Axiom).Nonempty) :
    W ≤ proofSpaceMin phpCompl Axiom :=
  proofSpaceMin_ge_of_band
    (SemanticMeasure.measure phpSat phpConstr)
    (fun {C D} p => SemanticMeasure.measure_resolvent_le phpSat phpConstr phpCompl php_hcons hunsat C D p)
    (fun {C} hC => by
      obtain ⟨S, hScard, hSimp⟩ := haxiom C hC
      exact le_trans (SemanticMeasure.measure_le_of_implies phpSat phpConstr hSimp) hScard)
    ht phpWidthLink phpRoot hne

end PallLean.Paper93.DeepMath.PathB.PHPProofSpace

#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.proofSpaceMin_ge_of_band
#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.php_proofSpace_min_ge
