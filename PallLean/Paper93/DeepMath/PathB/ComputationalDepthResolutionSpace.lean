import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionMediumClause

/-!
# Blackboard (configuration) resolution and a total-space band theorem

**STATUS: A REAL, RESTRICTED THEOREM — the proof-space companion of the BSW width bound.**

The width lower bound (`proofWidth_ge_of_medium_wide`) lives on the *tree* model.  This file builds the
standard **blackboard / configuration** proof-space model (Esteban–Torán) and proves the abstract
**total-space** analogue of the BSW band argument — run, this time, *directly on the configuration
sequence* rather than the derivation tree.

A `Blackboard` derivation is a sequence of memory configurations (finite sets of clauses) built by

* `start`    — empty memory,
* `download` — add an axiom,
* `infer`    — add the resolvent of two clauses currently in memory,
* `erase`    — drop a clause.

The **total space** is the largest configuration ever held, measured in literal occurrences
(`configSize M = ∑_{C ∈ M} width C`).  This is the faithful "observer boundary in the proof-space model":
the number of literal-slots a deterministic observer reconstructing the refutation must hold simultaneously.

## The key idea (why no Atserias–Dalmau detour is needed)

Take the abstract BSW measure `μ` (subadditive on resolvents, `≤ a` on axioms, `a < t`).  Consider the
*first* configuration whose maximal clause-measure reaches `t`.  It cannot be a download (axioms have
`μ ≤ a < t`) nor an erasure (those only shrink), so it is an **inference** adding a resolvent `R`.  Its two
parents were on the *previous* board, where every clause had `μ < t`; hence `μ R ≤ μ C + μ D < 2t`, while
`μ R ≥ t`.  So `R` is a clause of **medium** measure sitting on the board — and the width link forces
`width R ≥ W`.  Since `R` is in that configuration, the configuration's total space is `≥ W`.

This is the genuine total-space lower bound by expansion (the Ben-Sasson–Galesi / Esteban–Torán route),
proved with **no** locking lemma and **no** space-width inequality assumed — only the already-proved
`measure_resolvent_le` and the medium→wide link.

**Honest scope.**  This is *total space* (literal occurrences), the easy-to-relate proof-space measure; it
is a genuine super-logarithmic lower bound *for the resolution proof-space observer* (a restricted model),
not the general machine-decomposition observer (which stays open, `= CookLevinFrontierHyp`).
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

variable {Lit : Type*} [DecidableEq Lit]

/-- A blackboard configuration: the finite set of clauses currently in memory. -/
abbrev Configuration (Lit : Type*) [DecidableEq Lit] := Finset (ResolutionClause Lit)

/-- **Total space of a configuration**: the number of literal occurrences held in memory,
`∑_{C ∈ M} width C`. -/
def configSize (M : Configuration Lit) : ℕ := ∑ C ∈ M, ResolutionClause.width C

/-- A single clause's width is at most the configuration's total space. -/
theorem width_le_configSize {M : Configuration Lit} {C : ResolutionClause Lit} (hC : C ∈ M) :
    ResolutionClause.width C ≤ configSize M :=
  Finset.single_le_sum (f := ResolutionClause.width) (fun _ _ => Nat.zero_le _) hC

/-- **Blackboard (configuration-style) resolution derivations** — the standard proof-space model. -/
inductive Blackboard (compl : Lit → Lit) (Axiom : ResolutionClause Lit → Prop) :
    Configuration Lit → Type _ where
  | start : Blackboard compl Axiom ∅
  | download {M : Configuration Lit} {C : ResolutionClause Lit} :
      Blackboard compl Axiom M → Axiom C → Blackboard compl Axiom (insert C M)
  | infer {M : Configuration Lit} {C D : ResolutionClause Lit} (p : Lit) :
      Blackboard compl Axiom M → C ∈ M → D ∈ M →
      Blackboard compl Axiom (insert (ResolutionClause.resolvent compl C D p) M)
  | erase {M : Configuration Lit} (C : ResolutionClause Lit) :
      Blackboard compl Axiom M → Blackboard compl Axiom (M.erase C)

namespace Blackboard

variable {compl : Lit → Lit} {Axiom : ResolutionClause Lit → Prop}

/-- **Total space** of a blackboard derivation: the largest configuration ever held (in literal
occurrences) over the whole construction history. -/
def totalSpace : {M : Configuration Lit} → Blackboard compl Axiom M → ℕ
  | _, .start => 0
  | _, .download (M := M) (C := C) b _ => max (configSize (insert C M)) (totalSpace b)
  | _, .infer (M := M) (C := C) (D := D) p b _ _ =>
      max (configSize (insert (ResolutionClause.resolvent compl C D p) M)) (totalSpace b)
  | _, .erase (M := M) C b => max (configSize (M.erase C)) (totalSpace b)

@[simp] theorem totalSpace_start :
    totalSpace (Blackboard.start (compl := compl) (Axiom := Axiom)) = 0 := rfl

@[simp] theorem totalSpace_download {M : Configuration Lit} {C : ResolutionClause Lit}
    (b : Blackboard compl Axiom M) (h : Axiom C) :
    totalSpace (Blackboard.download b h) = max (configSize (insert C M)) (totalSpace b) := rfl

@[simp] theorem totalSpace_infer {M : Configuration Lit} {C D : ResolutionClause Lit} (p : Lit)
    (b : Blackboard compl Axiom M) (hC : C ∈ M) (hD : D ∈ M) :
    totalSpace (Blackboard.infer p b hC hD)
      = max (configSize (insert (ResolutionClause.resolvent compl C D p) M)) (totalSpace b) := rfl

@[simp] theorem totalSpace_erase {M : Configuration Lit} (C : ResolutionClause Lit)
    (b : Blackboard compl Axiom M) :
    totalSpace (Blackboard.erase C b) = max (configSize (M.erase C)) (totalSpace b) := rfl

/-- The current configuration's total space is at most the derivation's total space. -/
theorem configSize_le_totalSpace {M : Configuration Lit} (D : Blackboard compl Axiom M) :
    configSize M ≤ totalSpace D := by
  cases D with
  | start => simp [configSize]
  | download b h => rw [totalSpace_download]; exact le_max_left _ _
  | infer p b hC hD => rw [totalSpace_infer]; exact le_max_left _ _
  | erase C b => rw [totalSpace_erase]; exact le_max_left _ _

/-- **Abstract total-space band theorem (proved).**  For a measure `μ` subadditive under resolution, with
axiom measure `≤ a < t` and a *medium→wide* link (`t ≤ μ C < 2t ⇒ width C ≥ W`): any blackboard derivation
whose final memory already holds a clause of measure `≥ t` has total space `≥ W`.

The proof runs the BSW band argument on the configuration sequence: the first time the board carries a
clause of measure `≥ t`, that clause is a freshly inferred resolvent of two `< t`-measure parents, hence of
medium measure `[t, 2t)`, hence wide; being in memory, it forces the total space up. -/
theorem totalSpace_ge_of_medium_wide
    {a t W : ℕ}
    (μ : ResolutionClause Lit → ℕ)
    (hsub : ∀ {C D : ResolutionClause Lit} (p : Lit),
        μ (ResolutionClause.resolvent compl C D p) ≤ μ C + μ D)
    (hax : ∀ {C : ResolutionClause Lit}, Axiom C → μ C ≤ a)
    (ht : a < t)
    (hwide : ∀ {C : ResolutionClause Lit}, t ≤ μ C → μ C < 2 * t →
        W ≤ ResolutionClause.width C)
    {M : Configuration Lit} (D : Blackboard compl Axiom M) :
    (∃ C ∈ M, t ≤ μ C) → W ≤ totalSpace D := by
  induction D with
  | start =>
      intro hmed
      obtain ⟨C, hC, _⟩ := hmed
      simp at hC
  | @download M C b hC ih =>
      intro hmed
      simp only [totalSpace_download]
      obtain ⟨E, hE, htE⟩ := hmed
      rw [Finset.mem_insert] at hE
      rcases hE with hE | hE
      · subst hE
        exact absurd htE (by have := hax hC; omega)
      · exact le_trans (ih ⟨E, hE, htE⟩) (le_max_right _ _)
  | @infer M C D p b hCM hDM ih =>
      intro hmed
      simp only [totalSpace_infer]
      obtain ⟨E, hE, htE⟩ := hmed
      by_cases hprev : ∃ F ∈ M, t ≤ μ F
      · exact le_trans (ih hprev) (le_max_right _ _)
      · push_neg at hprev
        rw [Finset.mem_insert] at hE
        rcases hE with hE | hE
        · -- the witness is the freshly inferred resolvent: medium, hence wide
          have hμC : μ C < t := hprev C hCM
          have hμD : μ D < t := hprev D hDM
          have hRlo : t ≤ μ (ResolutionClause.resolvent compl C D p) := hE ▸ htE
          have hRhi : μ (ResolutionClause.resolvent compl C D p) < 2 * t :=
            lt_of_le_of_lt (hsub p) (by omega)
          have hWwidth : W ≤ ResolutionClause.width (ResolutionClause.resolvent compl C D p) :=
            hwide hRlo hRhi
          have hRmem : ResolutionClause.resolvent compl C D p
              ∈ insert (ResolutionClause.resolvent compl C D p) M := Finset.mem_insert_self _ _
          calc W ≤ ResolutionClause.width (ResolutionClause.resolvent compl C D p) := hWwidth
            _ ≤ configSize (insert (ResolutionClause.resolvent compl C D p) M) :=
                width_le_configSize hRmem
            _ ≤ max (configSize (insert (ResolutionClause.resolvent compl C D p) M))
                  (totalSpace b) := le_max_left _ _
        · exact absurd htE (by have := hprev E hE; omega)
  | @erase M C b ih =>
      intro hmed
      simp only [totalSpace_erase]
      obtain ⟨E, hE, htE⟩ := hmed
      exact le_trans (ih ⟨E, Finset.mem_of_mem_erase hE, htE⟩) (le_max_right _ _)

end Blackboard

/-! ## Kernel-only axiom trace -/

#print axioms Blackboard.totalSpace_ge_of_medium_wide
#print axioms Blackboard.configSize_le_totalSpace

end PallLean.Paper93.DeepMath.PathB
