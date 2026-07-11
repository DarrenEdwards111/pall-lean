import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameAC0pUnionBound

/-!
# The approximator, and assembling `ErrAdditive` from per-gate local errors (RS repair, step 2)

`NFrameAC0pUnionBound` supplied `AC0pCircuit p` and the union-bound composition lemma
(`ErrAdditive A B ⟹ errCard A C ≤ gateCount C · B`).  This file builds the **approximator** it consumes and
**assembles `ErrAdditive`** from per-gate local-error bounds.

`approx loc x C` is a recursive Boolean approximator: it computes each gate's operation via a *local
approximation* `loc gate : List Bool → Bool` of that gate's children's approximate values (NOT / inputs / consts
are exact).  Because `loc` receives the gate itself, each gate may carry its own seed (weights).

The key structural result is the **gate-level union bound** (`errCard_gate_le`): a gate's error set is contained
in the union of its children's error sets together with its **local error set**

```text
  { x  |  loc gate (true children values at x)  ≠  gateOp (true children values at x) }.
```

Hence (`approx_ErrAdditive`) if every gate's local error is `≤ B`, then `ErrAdditive (approxA loc) B` holds, and
(`approx_errCard_le`) the union-bound lemma gives `errCard (approxA loc) C ≤ gateCount C · B`.

## What is still open (honest)

This assembles `ErrAdditive` **from** per-gate local-error bounds; it does not **discharge** them.  Bounding a
gate's local error by `B ≤ ⌈p^{-t}·2^n⌉` requires the *input-level* Razborov–Smolensky averaging: for each input
`x` the amplified form errs (over the gate's random seed) with probability `≤ p^{-t}`, so a good seed has local
error `≤ 2^n·p^{-t}` per gate.  That is a per-gate averaging over seeds — related to but not identical to
`NFrameFpAmplify.or_amplified_error_bound` (which counts *value-vectors*, not inputs) — and is the remaining
piece.  Until it is proved, the `hAnd/hOr/hMod` hypotheses of `approx_ErrAdditive` are inputs, not theorems.

## Honest scope

The approximator and the gate-level union bound assembling `ErrAdditive` from per-gate local errors.  No
per-gate error bound is proved (so no circuit approximation stands on its own), no ACC⁰ lower bound.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameAC0pApproximator

open PallLean.Paper93.DeepMath.PathB.NFrameAC0pUnionBound
open PallLean.Paper93.DeepMath.PathB.NFrameAC0pUnionBound.AC0pCircuit

/-! ## The approximator -/

/-- The recursive Boolean approximator.  Each AND/OR/MOD gate is computed by a local approximation
`loc gate : List Bool → Bool` of its children's approximate values; NOT/inputs/consts are exact.  `loc` receives
the gate itself, so each gate may carry its own seed. -/
def approx {p n : Nat} (loc : AC0pCircuit p n → List Bool → Bool) (x : Fin n → Bool) :
    AC0pCircuit p n → Bool
  | .input i => x i
  | .const b => b
  | .not c => !(approx loc x c)
  | .and l => loc (.and l) (l.map (approx loc x))
  | .or l => loc (.or l) (l.map (approx loc x))
  | .mod l => loc (.mod l) (l.map (approx loc x))

/-- The approximator packaged for the union-bound interface. -/
def approxA {p n : Nat} (loc : AC0pCircuit p n → List Bool → Bool) :
    AC0pCircuit p n → (Fin n → Bool) → Bool :=
  fun C x => approx loc x C

/-! ## The gate-level union bound -/

/-- A gate's error set is covered by the union of its children's error sets: `#{x | ∃ child errs} ≤ Σ child
error counts`. -/
theorem card_exists_le {p n : Nat} (loc : AC0pCircuit p n → List Bool → Bool)
    (l : List (AC0pCircuit p n)) :
    (Finset.univ.filter (fun x => ∃ c ∈ l, approxA loc c x ≠ eval x c)).card
      ≤ (l.map (errCard (approxA loc))).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hsub : (Finset.univ.filter (fun x => ∃ c ∈ a :: t, approxA loc c x ≠ eval x c))
        ⊆ (Finset.univ.filter (fun x => approxA loc a x ≠ eval x a))
          ∪ (Finset.univ.filter (fun x => ∃ c ∈ t, approxA loc c x ≠ eval x c)) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, Finset.mem_union] at hx ⊢
      obtain ⟨c, hc, herr⟩ := hx
      rcases hc with rfl | hc
      · exact Or.inl herr
      · exact Or.inr ⟨c, hc, herr⟩
    calc (Finset.univ.filter (fun x => ∃ c ∈ a :: t, approxA loc c x ≠ eval x c)).card
        ≤ ((Finset.univ.filter (fun x => approxA loc a x ≠ eval x a))
            ∪ (Finset.univ.filter (fun x => ∃ c ∈ t, approxA loc c x ≠ eval x c))).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter (fun x => approxA loc a x ≠ eval x a)).card
            + (Finset.univ.filter (fun x => ∃ c ∈ t, approxA loc c x ≠ eval x c)).card :=
          Finset.card_union_le _ _
      _ ≤ errCard (approxA loc) a + (t.map (errCard (approxA loc))).sum := Nat.add_le_add le_rfl ih
      _ = ((a :: t).map (errCard (approxA loc))).sum := by simp [errCard]

/-- **The gate-level union bound.**  For a gate `C = gate l` whose approximation is `loc C (children values)` and
whose semantics is `top (children values)`, the gate's error is bounded by the children's errors plus the local
error set `{x | loc C (true values) ≠ top (true values)}`. -/
theorem errCard_gate_le {p n : Nat} (loc : AC0pCircuit p n → List Bool → Bool)
    (C : AC0pCircuit p n) (l : List (AC0pCircuit p n)) (top : List Bool → Bool)
    (hA : ∀ x, approxA loc C x = loc C (l.map (fun c => approxA loc c x)))
    (hE : ∀ x, eval x C = top (l.map (fun c => eval x c))) :
    errCard (approxA loc) C ≤ (l.map (errCard (approxA loc))).sum
      + (Finset.univ.filter
          (fun x => loc C (l.map (fun c => eval x c)) ≠ top (l.map (fun c => eval x c)))).card := by
  have hsub : (Finset.univ.filter (fun x => approxA loc C x ≠ eval x C))
      ⊆ (Finset.univ.filter (fun x => ∃ c ∈ l, approxA loc c x ≠ eval x c))
        ∪ (Finset.univ.filter
            (fun x => loc C (l.map (fun c => eval x c)) ≠ top (l.map (fun c => eval x c)))) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    by_cases hall : ∀ c ∈ l, approxA loc c x = eval x c
    · refine Or.inr ?_
      rw [hA x, hE x] at hx
      have hmap : l.map (fun c => approxA loc c x) = l.map (fun c => eval x c) :=
        List.map_congr_left hall
      rwa [hmap] at hx
    · push_neg at hall
      obtain ⟨c, hc, hne⟩ := hall
      exact Or.inl ⟨c, hc, hne⟩
  calc errCard (approxA loc) C
      ≤ ((Finset.univ.filter (fun x => ∃ c ∈ l, approxA loc c x ≠ eval x c))
          ∪ (Finset.univ.filter
              (fun x => loc C (l.map (fun c => eval x c)) ≠ top (l.map (fun c => eval x c))))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun x => ∃ c ∈ l, approxA loc c x ≠ eval x c)).card
          + (Finset.univ.filter
              (fun x => loc C (l.map (fun c => eval x c)) ≠ top (l.map (fun c => eval x c)))).card :=
        Finset.card_union_le _ _
    _ ≤ (l.map (errCard (approxA loc))).sum
          + (Finset.univ.filter
              (fun x => loc C (l.map (fun c => eval x c)) ≠ top (l.map (fun c => eval x c)))).card :=
        Nat.add_le_add (card_exists_le loc l) le_rfl

/-! ## Assembling `ErrAdditive` -/

/-- The local error count of an AND / OR / MOD gate under `loc`, against the true gate operation. -/
def localErr {p n : Nat} (loc : AC0pCircuit p n → List Bool → Bool) (C : AC0pCircuit p n)
    (top : List Bool → Bool) (l : List (AC0pCircuit p n)) : Nat :=
  (Finset.univ.filter
    (fun x => loc C (l.map (fun c => eval x c)) ≠ top (l.map (fun c => eval x c)))).card

/-- **Assembling `ErrAdditive`.**  If every AND, OR and MOD gate has local error `≤ B` under `loc`, then the
approximator `approxA loc` satisfies the per-gate additive error bound `ErrAdditive (approxA loc) B`. -/
theorem approx_ErrAdditive {p n : Nat} (loc : AC0pCircuit p n → List Bool → Bool) (B : Nat)
    (hAnd : ∀ l, localErr loc (.and l) (fun v => v.all id) l ≤ B)
    (hOr : ∀ l, localErr loc (.or l) (fun v => v.any id) l ≤ B)
    (hMod : ∀ l, localErr loc (.mod l) (fun v => decide ((v.filter id).length % p = 0)) l ≤ B) :
    ErrAdditive (approxA loc) B := by
  refine ⟨fun i => ?_, fun b => ?_, fun c => ?_, fun l => ?_, fun l => ?_, fun l => ?_⟩
  · -- input: exact, error 0
    have h0 : errCard (approxA loc) (AC0pCircuit.input i) = 0 := by
      simp only [errCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _; simp [approxA, approx, eval]
    omega
  · have h0 : errCard (approxA loc) (AC0pCircuit.const b) = 0 := by
      simp only [errCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _; simp [approxA, approx, eval]
    omega
  · -- not: exact, error = child error
    have heq : errCard (approxA loc) (AC0pCircuit.not c) = errCard (approxA loc) c := by
      simp only [errCard]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro x _
      simp only [approxA, approx, eval]
      cases approx loc x c <;> cases eval x c <;> decide
    omega
  · calc errCard (approxA loc) (AC0pCircuit.and l)
        ≤ (l.map (errCard (approxA loc))).sum + localErr loc (.and l) (fun v => v.all id) l :=
          errCard_gate_le loc (.and l) l (fun v => v.all id)
            (fun x => by simp [approxA, approx]) (fun x => by simp [eval])
      _ ≤ (l.map (errCard (approxA loc))).sum + B := Nat.add_le_add le_rfl (hAnd l)
  · calc errCard (approxA loc) (AC0pCircuit.or l)
        ≤ (l.map (errCard (approxA loc))).sum + localErr loc (.or l) (fun v => v.any id) l :=
          errCard_gate_le loc (.or l) l (fun v => v.any id)
            (fun x => by simp [approxA, approx]) (fun x => by simp [eval])
      _ ≤ (l.map (errCard (approxA loc))).sum + B := Nat.add_le_add le_rfl (hOr l)
  · calc errCard (approxA loc) (AC0pCircuit.mod l)
        ≤ (l.map (errCard (approxA loc))).sum
            + localErr loc (.mod l) (fun v => decide ((v.filter id).length % p = 0)) l :=
          errCard_gate_le loc (.mod l) l (fun v => decide ((v.filter id).length % p = 0))
            (fun x => by simp [approxA, approx]) (fun x => by simp [eval])
      _ ≤ (l.map (errCard (approxA loc))).sum + B := Nat.add_le_add le_rfl (hMod l)

/-- **The circuit error bound (given per-gate local bounds).**  If every gate's local error is `≤ B`, the
approximator errs on at most `gateCount C · B` inputs — the RS union bound, assembled from the gate-level
composition. -/
theorem approx_errCard_le {p n : Nat} (loc : AC0pCircuit p n → List Bool → Bool) (B : Nat)
    (hAnd : ∀ l, localErr loc (.and l) (fun v => v.all id) l ≤ B)
    (hOr : ∀ l, localErr loc (.or l) (fun v => v.any id) l ≤ B)
    (hMod : ∀ l, localErr loc (.mod l) (fun v => decide ((v.filter id).length % p = 0)) l ≤ B)
    (C : AC0pCircuit p n) :
    errCard (approxA loc) C ≤ gateCount C * B :=
  errCard_le_gateCount_mul (approxA loc) B (approx_ErrAdditive loc B hAnd hOr hMod) C

end PallLean.Paper93.DeepMath.PathB.NFrameAC0pApproximator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pApproximator.errCard_gate_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pApproximator.approx_ErrAdditive
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pApproximator.approx_errCard_le
