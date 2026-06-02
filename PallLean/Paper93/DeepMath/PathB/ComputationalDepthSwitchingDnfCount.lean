import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingTermWalk
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel

/-!
# The `(2w)^s` DNF switching count (on the closed decoder)

**STATUS: REAL.  THE TIGHT COUNT MODULO THE LABEL-DETERMINES-LITLIST HYPOTHESIS.**

With the DNF decoder closed (`termWalk_decode_blocks`, `termWalk_inj`), the `(2w)^s` count
follows from a generic encoding-count scaffold plus the lone label-engineering hypothesis
`hlabdet` — that the compact `PathLabel w s` (together with the completion `σ*`) determines
the path-literal list.  `card_pathLabels` already gives the `(2w)^s` cardinality.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **The common count scaffold (shared by both routes).**  If an encoding `E` lands in
`Short`, every label lies in a label-space `Lspace` of cardinality `≤ ℓ`, and `(E ρ, lab ρ)`
determines `ρ`, then `|Bad| ≤ |Short| · ℓ`.  *Both* the tight `PathLabel` route (this file,
`Lspace = univ`, `ℓ = (2w)^s`) and Codex's structural route (`Lspace = circuitLabelSpace`,
`ℓ = ((2^w)^m)^numTerms`) are instances — the routes meet here, at one scaffold. -/
theorem card_bad_le_finset_label {L : Type*} [DecidableEq L]
    (E : Restriction n → Restriction n) (lab : Restriction n → L) (Lspace : Finset L)
    {Bad Short : Finset (Restriction n)} {ℓ : ℕ}
    (hLspace : Lspace.card ≤ ℓ) (hmem : ∀ ρ ∈ Bad, E ρ ∈ Short)
    (hlab : ∀ ρ ∈ Bad, lab ρ ∈ Lspace)
    (hrec : ∀ ρ ∈ Bad, ∀ σ ∈ Bad, E ρ = E σ → lab ρ = lab σ → ρ = σ) :
    Bad.card ≤ Short.card * ℓ := by
  classical
  calc Bad.card
      ≤ (Short ×ˢ Lspace).card :=
        Finset.card_le_card_of_injOn (fun ρ => (E ρ, lab ρ))
          (fun ρ hρ => Finset.mem_product.mpr ⟨hmem ρ hρ, hlab ρ hρ⟩)
          (fun ρ hρ σ hσ heq => hrec ρ (Finset.mem_coe.mp hρ) σ (Finset.mem_coe.mp hσ)
            (congrArg Prod.fst heq) (congrArg Prod.snd heq))
    _ = Short.card * Lspace.card := Finset.card_product _ _
    _ ≤ Short.card * ℓ := Nat.mul_le_mul_left _ hLspace

/-- **Generic finite-label count scaffold.**  If an encoding `E` lands in `Short`, the pair
`(E ρ, lab ρ)` determines `ρ`, and the label type `β` has `≤ ℓ` elements, then
`|Bad| ≤ |Short| · ℓ`.  Decouples the count from any particular label type. -/
theorem card_bad_le_label_card {β : Type*} [Fintype β] [DecidableEq β]
    (E : Restriction n → Restriction n) (lab : Restriction n → β)
    {Bad Short : Finset (Restriction n)} {ℓ : ℕ} (hℓ : Fintype.card β ≤ ℓ)
    (hmem : ∀ ρ ∈ Bad, E ρ ∈ Short)
    (hrec : ∀ ρ ∈ Bad, ∀ σ ∈ Bad, E ρ = E σ → lab ρ = lab σ → ρ = σ) :
    Bad.card ≤ Short.card * ℓ := by
  classical
  calc Bad.card
      ≤ (Short ×ˢ (Finset.univ : Finset β)).card :=
        Finset.card_le_card_of_injOn (fun ρ => (E ρ, lab ρ))
          (fun ρ hρ => Finset.mem_product.mpr ⟨hmem ρ hρ, Finset.mem_univ _⟩)
          (fun ρ hρ σ hσ heq => hrec ρ (Finset.mem_coe.mp hρ) σ (Finset.mem_coe.mp hσ)
            (congrArg Prod.fst heq) (congrArg Prod.snd heq))
    _ = Short.card * Fintype.card β := by rw [Finset.card_product, Finset.card_univ]
    _ ≤ Short.card * ℓ := Nat.mul_le_mul_left _ hℓ

/-- **Generic encoding-count scaffold.**  If an encoding `E` lands in `Short` and the pair
`(E ρ, lab ρ)` determines `ρ`, then `|Bad| ≤ |Short| · (2w)^s`. -/
theorem card_bad_le_encoding {w s : ℕ} (E : Restriction n → Restriction n)
    (lab : Restriction n → PathLabel w s) {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, E ρ ∈ Short)
    (hrec : ∀ ρ ∈ Bad, ∀ σ ∈ Bad, E ρ = E σ → lab ρ = lab σ → ρ = σ) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  classical
  have hcard : (Finset.univ : Finset (PathLabel w s)).card = (2 * w) ^ s := by
    rw [Finset.card_univ]; exact card_pathLabels w s
  have hsub : ∀ ρ ∈ Bad, (fun ρ => (E ρ, lab ρ)) ρ
      ∈ Short ×ˢ (Finset.univ : Finset (PathLabel w s)) :=
    fun ρ hρ => Finset.mem_product.mpr ⟨hmem ρ hρ, Finset.mem_univ _⟩
  have hinj : Set.InjOn (fun ρ => (E ρ, lab ρ)) ↑Bad :=
    fun ρ hρ σ hσ heq => hrec ρ (Finset.mem_coe.mp hρ) σ (Finset.mem_coe.mp hσ)
      (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  calc Bad.card
      ≤ (Short ×ˢ (Finset.univ : Finset (PathLabel w s))).card :=
        Finset.card_le_card_of_injOn _ hsub hinj
    _ = Short.card * (2 * w) ^ s := by rw [Finset.card_product, hcard]

/-- **The `(2w)^s` DNF switching count.**  Given, for every bad `ρ`: its completion decodes
back to `ρ` (`hdecode`, = `termWalk_decode_blocks`), its completion lands in `Short`
(`hmem`), and the compact label `lab` together with the completion determines the
path-literal list (`hlabdet` — the lone label-engineering obligation), then

  `|Bad| ≤ |Short| · (2w)^s`.

The decoder side (`termWalk_inj`) discharges the injectivity; `hlabdet` is the only
remaining input (the per-step `Fin w`-index encoding of the blocks). -/
theorem dnf_switching_bound {w s : ℕ} {cs : List (Clause n)}
    {litList : Restriction n → List (Rung4Literal n)} {k : ℕ}
    {lab : Restriction n → PathLabel w s} {Bad Short : Finset (Restriction n)}
    (hdecode : ∀ ρ ∈ Bad, freeOn (complete ρ (litList ρ))
        (termWalkVars (complete ρ (litList ρ)) (termBlock (litList ρ)) cs k) = ρ)
    (hmem : ∀ ρ ∈ Bad, complete ρ (litList ρ) ∈ Short)
    (hlabdet : ∀ ρ ∈ Bad, ∀ σ ∈ Bad,
        complete ρ (litList ρ) = complete σ (litList σ) → lab ρ = lab σ → litList ρ = litList σ) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  refine card_bad_le_encoding (fun ρ => complete ρ (litList ρ)) lab hmem ?_
  intro ρ hρ σ hσ hE hlab
  exact termWalk_inj (hdecode ρ hρ) (hdecode σ hσ) hE (hlabdet ρ hρ σ hσ hE hlab)

/-- **The `(2w)^s` count, var-set form.**  Same as `dnf_switching_bound`, but the label
need only determine the path-variable *set* (not the ordered list) — the weaker, and
correct, obligation, since the decoder depends on `litList` only through that set. -/
theorem dnf_switching_bound' {w s : ℕ} {cs : List (Clause n)}
    {litList : Restriction n → List (Rung4Literal n)} {k : ℕ}
    {lab : Restriction n → PathLabel w s} {Bad Short : Finset (Restriction n)}
    (hdecode : ∀ ρ ∈ Bad, freeOn (complete ρ (litList ρ))
        (termWalkVars (complete ρ (litList ρ)) (termBlock (litList ρ)) cs k) = ρ)
    (hmem : ∀ ρ ∈ Bad, complete ρ (litList ρ) ∈ Short)
    (hlabdet : ∀ ρ ∈ Bad, ∀ σ ∈ Bad,
        complete ρ (litList ρ) = complete σ (litList σ) → lab ρ = lab σ →
        ((litList ρ).map litVar).toFinset = ((litList σ).map litVar).toFinset) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  refine card_bad_le_encoding (fun ρ => complete ρ (litList ρ)) lab hmem ?_
  intro ρ hρ σ hσ hE hlab
  exact termWalk_inj' (hdecode ρ hρ) (hdecode σ hσ) hE (hlabdet ρ hρ σ hσ hE hlab)

/-- **THE ENCODER INTERFACE.**  This is the precise target an encoder (e.g. Codex's
`circuitPath`) must hit for the tight `(2w)^s` switching count.  Provide:

* a finite label type `β` with `Fintype.card β ≤ (2w)^s` (`hcard`);
* a label `lab : Restriction → β` and a per-`ρ` path-literal list `litList`;
* `hdecode` — the sound decoder recovers `ρ` from the completion (`termWalk_decode_blocks`,
  i.e. the canonical path's processed terms with distinct-variable blocks);
* `hmem` — the completion lands in `Short`;
* `hlabdet` — the label (with the completion) determines the path-variable set
  (discharged at the flat-label level by `termWalk_flat_det` + `ungroupBlocks_inj`).

Then `|Bad| ≤ |Short| · (2w)^s`.  The entire decoder side is discharged inside; only the
four hypotheses — all about the *encoder/canonical path* — remain, and they are exactly
what Codex's `circuitPath`/`circuitLabelSpace` produce (his "term" = AND-of-clauses; a
single-`Clause` term adapter or his packed label with `card β ≤ (2w)^s` plugs in here). -/
theorem dnf_switching_interface {β : Type*} [Fintype β] [DecidableEq β] {w s : ℕ}
    {cs : List (Clause n)} {litList : Restriction n → List (Rung4Literal n)} {k : ℕ}
    {lab : Restriction n → β} {Bad Short : Finset (Restriction n)}
    (hcard : Fintype.card β ≤ (2 * w) ^ s)
    (hdecode : ∀ ρ ∈ Bad, freeOn (complete ρ (litList ρ))
        (termWalkVars (complete ρ (litList ρ)) (termBlock (litList ρ)) cs k) = ρ)
    (hmem : ∀ ρ ∈ Bad, complete ρ (litList ρ) ∈ Short)
    (hlabdet : ∀ ρ ∈ Bad, ∀ σ ∈ Bad,
        complete ρ (litList ρ) = complete σ (litList σ) → lab ρ = lab σ →
        ((litList ρ).map litVar).toFinset = ((litList σ).map litVar).toFinset) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  refine card_bad_le_label_card (fun ρ => complete ρ (litList ρ)) lab hcard hmem ?_
  intro ρ hρ σ hσ hE hlab
  exact termWalk_inj' (hdecode ρ hρ) (hdecode σ hσ) hE (hlabdet ρ hρ σ hσ hE hlab)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.dnf_switching_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.dnf_switching_interface
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_bad_le_finset_label
