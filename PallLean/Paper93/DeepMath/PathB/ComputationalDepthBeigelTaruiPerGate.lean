import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiBase

/-!
# Beigel–Tarui, rung 7: per-gate substitution and the error union bound

The Razborov–Smolensky degree reduction (rungs 2–5) gives, per gate, a *low-degree* approximator that errs on a small
set.  This file proves the **composition of those per-gate approximators**: substituting an approximator at every gate,
the whole circuit is correct on any input that avoids **every** gate's error set, so the circuit's error set is
contained in the **union** of the per-gate error sets — hence its size is at most the *sum* of the per-gate error sizes
(the union bound over gates).

  `subforms` — the list of all subformulas (gates) of a formula.
  `approx_correct` — **PROVED**: if at every gate the approximator maps correct inputs to the correct output whenever the
        input avoids that gate's bad set, then on any input avoiding *all* gates' bad sets the whole approximation is
        exactly correct.
  `error_subset` — **PROVED**: the set of inputs where the approximation errs is contained in the union of the per-gate
        bad sets.
  `error_card_le` — **PROVED, the union bound**: the number of inputs where the approximation errs is at most the sum,
        over gates, of the per-gate error-set sizes.

Combined with rung 6's degree composition (each approximator of degree `≤ D` → whole circuit degree `≤ D^depth`), this
is the per-gate substitution: a degree-`D^depth` polynomial for the whole circuit whose total error is at most
`(#gates) · (per-gate error)`.

## Honest scope

This is the **error union bound** for per-gate substitution — the composition of approximators' *correctness* — stated
abstractly over any per-gate approximator and its bad set.  Instantiating it with Razborov–Smolensky: the bad set of
each gate is the inputs on which that gate's low-degree approximator (rungs 2–5) errs, of density `≤ 2^{-t}`, so the
whole circuit's error density is `≤ (#gates) · 2^{-t}`; with rung 6's degree bound the circuit polynomial has degree
`(t(p-1))^depth = polylog`.  Discharging that instantiation (matching each gate's bad set to the RS subset-choice error
and choosing `t` so `#gates · 2^{-t} < 1` for the union-bound existence) and folding the resulting low-degree polynomial
into one `SYM∘AND` with `m` quasipolynomial are the remaining Beigel–Tarui content.  This file supplies the per-gate
composition skeleton — degree (rung 6) and error (here) — that the RS instantiation plugs into.  Nothing here is the
Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

variable {n : ℕ}

open scoped Classical

/-- All subformulas (gates) of a formula, including itself. -/
def subforms : BForm n → List (BForm n)
  | .var i => [.var i]
  | .bnot a => (.bnot a) :: subforms a
  | .band a b => (.band a b) :: (subforms a ++ subforms b)
  | .bor a b => (.bor a b) :: (subforms a ++ subforms b)

/-- **Per-gate substitution correctness (proved)**: if at every gate the approximator `aeval` maps correct sub-values to
the correct gate output whenever the input avoids that gate's bad set, then on any input avoiding *all* gates' bad sets,
`aeval f` equals the exact value `f.eval`. -/
theorem approx_correct
    (aeval : BForm n → (Fin n → Bool) → Bool)
    (bad : BForm n → Finset (Fin n → Bool))
    (hvar : ∀ i x, aeval (.var i) x = (BForm.var i).eval x)
    (hnot : ∀ a x, x ∉ bad (.bnot a) → aeval a x = a.eval x → aeval (.bnot a) x = (BForm.bnot a).eval x)
    (hand : ∀ a b x, x ∉ bad (.band a b) → aeval a x = a.eval x → aeval b x = b.eval x →
      aeval (.band a b) x = (BForm.band a b).eval x)
    (hor : ∀ a b x, x ∉ bad (.bor a b) → aeval a x = a.eval x → aeval b x = b.eval x →
      aeval (.bor a b) x = (BForm.bor a b).eval x)
    (x : Fin n → Bool) :
    ∀ f : BForm n, (∀ g ∈ subforms f, x ∉ bad g) → aeval f x = f.eval x := by
  intro f
  induction f with
  | var i => intro _; exact hvar i x
  | bnot a ih =>
      intro hok
      exact hnot a x (hok _ (List.mem_cons_self ..))
        (ih (fun g hg => hok g (List.mem_cons_of_mem _ hg)))
  | band a b iha ihb =>
      intro hok
      exact hand a b x (hok _ (List.mem_cons_self ..))
        (iha (fun g hg => hok g (List.mem_cons_of_mem _ (List.mem_append_left _ hg))))
        (ihb (fun g hg => hok g (List.mem_cons_of_mem _ (List.mem_append_right _ hg))))
  | bor a b iha ihb =>
      intro hok
      exact hor a b x (hok _ (List.mem_cons_self ..))
        (iha (fun g hg => hok g (List.mem_cons_of_mem _ (List.mem_append_left _ hg))))
        (ihb (fun g hg => hok g (List.mem_cons_of_mem _ (List.mem_append_right _ hg))))

variable (aeval : BForm n → (Fin n → Bool) → Bool) (bad : BForm n → Finset (Fin n → Bool))
    (hvar : ∀ i x, aeval (.var i) x = (BForm.var i).eval x)
    (hnot : ∀ a x, x ∉ bad (.bnot a) → aeval a x = a.eval x → aeval (.bnot a) x = (BForm.bnot a).eval x)
    (hand : ∀ a b x, x ∉ bad (.band a b) → aeval a x = a.eval x → aeval b x = b.eval x →
      aeval (.band a b) x = (BForm.band a b).eval x)
    (hor : ∀ a b x, x ∉ bad (.bor a b) → aeval a x = a.eval x → aeval b x = b.eval x →
      aeval (.bor a b) x = (BForm.bor a b).eval x)

include hvar hnot hand hor

/-- **Error ⊆ union of gate errors (proved)**: every input on which the approximation differs from the exact value lies
in some gate's bad set. -/
theorem error_subset (f : BForm n) :
    Finset.univ.filter (fun x => aeval f x ≠ f.eval x)
      ⊆ (subforms f).toFinset.biUnion bad := by
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [Finset.mem_biUnion]
  by_contra hc
  push_neg at hc
  exact hx.2 (approx_correct aeval bad hvar hnot hand hor x f
    (fun g hg => hc g (List.mem_toFinset.mpr hg)))

/-- **The error union bound (proved)**: the number of inputs on which the approximation errs is at most the sum, over
gates, of the per-gate error-set sizes. -/
theorem error_card_le (f : BForm n) :
    (Finset.univ.filter (fun x => aeval f x ≠ f.eval x)).card
      ≤ ∑ g ∈ (subforms f).toFinset, (bad g).card :=
  le_trans (Finset.card_le_card (error_subset aeval bad hvar hnot hand hor f))
    Finset.card_biUnion_le

end PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.approx_correct
#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.error_card_le
