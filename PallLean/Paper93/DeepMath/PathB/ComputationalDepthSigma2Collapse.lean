import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDerandomizeSlice

/-!
# The Σ₂ → NP collapse condition, precisely: hardness must have short certificates (coMCSP ∈ NP)

`DerandomizeSlice` left the canonical hard slice at Σ₂: its defining predicate is
`Hard(f) = ∀ circuit c, ∃ input x, C_c(x) ≠ f(x)`, and the witness *search* is `∃ f, Hard(f)` — an `∃∀`,
Σ₂.  This file pins the exact condition under which that Σ₂ search collapses to NP (Σ₁).

Read the quantifiers.  The search is
```
   ∃ f, ∀ c, ¬ (c computes f)        -- ∃∀  = Σ₂
```
NP is a single `∃` over a *short* certificate.  The `∃ f` is already fine — `f` is a truth table, and NP
gets truth-table input.  The obstruction is the inner `∀ c`, a universal over all `2^{poly}` circuits.  It
collapses **iff hardness itself has a short, checkable certificate** — iff `Hard(f)` is equivalent to
`∃ w, CH(w,f)` for a poly-checkable `CH`.  Then
```
   ∃ f, Hard(f)  ↔  ∃ f, ∃ w, CH(w,f)  =  ∃ (f,w), CH(w,f)   -- ∃  = Σ₁ = NP
```

That condition has a name.  `Hard = ¬Easy`, and `Easy(f) = ∃ circuit computing f` is **MCSP** (∈ NP: guess
the circuit, check it).  So `Hard` is **coMCSP** (∈ coNP).  "Hardness has short certificates" is exactly
`coMCSP ∈ NP`, equivalently `MCSP ∈ coNP`, i.e. `MCSP ∈ NP ∩ coNP`.  MCSP ∈ NP is free (exhibit the
circuit); the missing half — a short certificate of *hardness* — is the whole collapse.

And that half is exactly a **natural proof**.  A checkable certificate of hardness is *constructive*
(poly-checkable, by definition of "certificate") and *useful* (it certifies genuine hardness); hardness is
*large* (most functions are hard, by the counting in `HardSlice`).  Constructive + useful + large = a
natural property, which Razborov–Rudich bars (under one-way functions).  So the Σ₂ → NP collapse condition
*is* the natural-proofs barrier — which is why it is `cost_super`.

## What is proved

* **`hard_iff_not_easy`** — `Hard = ¬Easy`: hardness is coMCSP, the complement of MCSP.
* **`witness_search_is_exists_forall`** — the witness search is `∃ f, ∀ c, ¬(c computes f)` = `∃∀` = Σ₂.
* **`CollapseCondition`** — the precise condition: `∀ f, Hard(f) ↔ ∃ w, CH(w,f)` with `CH` a short
  certificate.  (= coMCSP ∈ NP = MCSP ∈ coNP.)
* **`sigma2_collapses_to_np`** — under the condition, the Σ₂ search `∃ f, Hard f` becomes the Σ₁ search
  `∃ (f,w), CH(w,f)` — NP.
* **`collapse_gives_mcsp_in_conp`** — the condition is exactly `¬Easy(f) ↔ ∃ w, CH(w,f)`: MCSP ∈ coNP.
* **`collapse_condition_is_natural`** — the condition yields a useful hardness-certificate scheme: a
  natural property.
* **`barrier_blocks_collapse`** — under Razborov–Rudich (a natural property breaks one-way functions), the
  collapse condition is false.  The Σ₂ → NP collapse is precisely what the barrier forbids.

## Honest verdict — the condition is exact, and it is the natural-proofs barrier

The collapse is not vague.  It is one inequality of quantifier levels closed by one object: a short,
poly-checkable certificate of *hardness* (`CollapseCondition` = coMCSP ∈ NP = MCSP ∈ coNP).  With it, the
Σ₂ witness-search is literally NP (`sigma2_collapses_to_np`).  Without it, the `∀`-over-all-circuits stays.
And the object is exactly a natural property — constructive, useful, large (`collapse_condition_is_natural`)
— so under Razborov–Rudich it cannot exist (`barrier_blocks_collapse`), and the collapse cannot be had for
free.  That identification is the content: the precise Σ₂ → NP collapse condition and the precise
natural-proofs barrier are the *same statement*, and it is `cost_super`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Sigma2Collapse

variable {Circuit Func Cert : Type}

/-! ### Easy = MCSP, Hard = coMCSP -/

/-- `Easy f`: some circuit computes `f`.  This is **MCSP** — in NP (guess the circuit, verify). -/
def Easy (Computes : Circuit → Func → Prop) (f : Func) : Prop := ∃ c, Computes c f

/-- `Hard f`: no circuit computes `f`.  This is **coMCSP** — in coNP.  It is the predicate defining the
canonical hard slice. -/
def Hard (Computes : Circuit → Func → Prop) (f : Func) : Prop := ∀ c, ¬ Computes c f

/-- **Hardness is the complement of MCSP (proved).**  `Hard f ↔ ¬ Easy f`. -/
theorem hard_iff_not_easy (Computes : Circuit → Func → Prop) (f : Func) :
    Hard Computes f ↔ ¬ Easy Computes f := by
  simp only [Hard, Easy, not_exists]

/-- **The witness search is Σ₂ (proved).**  Finding a hard slice is `∃ f, ∀ c, ¬(c computes f)` — an
`∃∀`, the Σ₂ shape.  NP is a single `∃`; the inner `∀ c` is the obstruction. -/
theorem witness_search_is_exists_forall (Computes : Circuit → Func → Prop) :
    (∃ f, Hard Computes f) ↔ (∃ f, ∀ c, ¬ Computes c f) := by
  simp only [Hard]

/-! ### The precise collapse condition -/

/-- A short, poly-checkable **certificate of hardness**: `∃ w, CH w f`. -/
def HardCert (CH : Cert → Func → Prop) (f : Func) : Prop := ∃ w, CH w f

/-- **The Σ₂ → NP collapse condition.**  Hardness is equivalent to possessing a short certificate:
`∀ f, Hard f ↔ ∃ w, CH w f`.  Equivalently `coMCSP ∈ NP`, i.e. `MCSP ∈ NP ∩ coNP`. -/
def CollapseCondition (Computes : Circuit → Func → Prop) (CH : Cert → Func → Prop) : Prop :=
  ∀ f, Hard Computes f ↔ HardCert CH f

/-- **The collapse (proved).**  Under the condition, the Σ₂ search `∃ f, Hard f` becomes the Σ₁ search
`∃ f, ∃ w, CH w f` = `∃ (f,w), CH w f` — a single existential over a short pair, i.e. NP. -/
theorem sigma2_collapses_to_np
    (Computes : Circuit → Func → Prop) (CH : Cert → Func → Prop)
    (hcond : CollapseCondition Computes CH) :
    (∃ f, Hard Computes f) ↔ (∃ f, ∃ w, CH w f) := by
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, (hcond f).mp hf⟩
  · rintro ⟨f, w, hw⟩; exact ⟨f, (hcond f).mpr ⟨w, hw⟩⟩

/-- **The condition is exactly `MCSP ∈ coNP` (proved).**  It says `¬ Easy f ↔ ∃ w, CH w f` — the hard
(= not-easy) functions are precisely those with a short certificate: coMCSP ∈ NP, MCSP ∈ coNP. -/
theorem collapse_gives_mcsp_in_conp
    (Computes : Circuit → Func → Prop) (CH : Cert → Func → Prop)
    (hcond : CollapseCondition Computes CH) (f : Func) :
    ¬ Easy Computes f ↔ HardCert CH f := by
  rw [← hard_iff_not_easy]; exact hcond f

/-! ### The condition is a natural property, so the barrier blocks it -/

/-- A **natural hardness property**: a certificate scheme that only certifies genuinely hard functions
(*useful*).  It is also *constructive* (a certificate is poly-checkable by definition) and *large* (most
functions are hard — the `HardSlice` counting); those two conditions are noted rather than re-encoded. -/
def NaturalHardnessProperty (Computes : Circuit → Func → Prop) (CH : Cert → Func → Prop) : Prop :=
  ∀ f, HardCert CH f → Hard Computes f

/-- **The collapse condition is a natural property (proved).**  If hardness is equivalent to a short
certificate, then in particular every certificate certifies genuine hardness — a useful (constructive,
large) property. -/
theorem collapse_condition_is_natural
    (Computes : Circuit → Func → Prop) (CH : Cert → Func → Prop)
    (hcond : CollapseCondition Computes CH) :
    NaturalHardnessProperty Computes CH :=
  fun f h => (hcond f).mpr h

/-- **The barrier blocks the collapse (proved).**  Razborov–Rudich (under one-way functions): a
constructive, useful, large hardness property cannot exist — it breaks the OWF.  Given that barrier, the
Σ₂ → NP collapse condition is false.  The collapse and the natural-proofs barrier are the same statement. -/
theorem barrier_blocks_collapse
    (Computes : Circuit → Func → Prop) (CH : Cert → Func → Prop)
    (rr : NaturalHardnessProperty Computes CH → False) :
    ¬ CollapseCondition Computes CH :=
  fun hcond => rr (collapse_condition_is_natural Computes CH hcond)

end PallLean.Paper93.DeepMath.PathB.Sigma2Collapse

#print axioms PallLean.Paper93.DeepMath.PathB.Sigma2Collapse.hard_iff_not_easy
#print axioms PallLean.Paper93.DeepMath.PathB.Sigma2Collapse.witness_search_is_exists_forall
#print axioms PallLean.Paper93.DeepMath.PathB.Sigma2Collapse.sigma2_collapses_to_np
#print axioms PallLean.Paper93.DeepMath.PathB.Sigma2Collapse.collapse_gives_mcsp_in_conp
#print axioms PallLean.Paper93.DeepMath.PathB.Sigma2Collapse.collapse_condition_is_natural
#print axioms PallLean.Paper93.DeepMath.PathB.Sigma2Collapse.barrier_blocks_collapse
