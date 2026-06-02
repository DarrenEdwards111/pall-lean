import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonLabel

/-!
# Bridge: the canonical `(2w)^s` switching count → the depth-3 collapse pipeline

**STATUS: REAL.  COUNT ⟹ A SIMULTANEOUSLY-GOOD RESTRICTION EXISTS (pigeonhole + union bound).**

The depth-3 collapse gate (`Depth3CollapseModel.collapse`) needs: a restriction under which the
refuting circuit collapses to a short list-derivation refutation.  The canonical switching count
`canonMarkLabel_switching_count` is the *quantitative* ingredient — it bounds the **bad**
restrictions (those that fail to collapse a bottom gate) by `|Short| · (2w)^s`.

This file builds the honest links of the count → collapse chain that are pure counting:
* `exists_good_restriction` — pigeonhole: count `< 3^n` ⟹ a non-bad restriction exists;
* `exists_good_restriction_canon` — the same, consuming `canonMarkLabel_switching_count`;
* `exists_good_restriction_forall` — **union bound**: a single restriction good for *all*
  bottom gates at once (`#gates · |Short|·(2w)^s < 3^n`);
* `card_restriction` — `#restrictions = 3^n`, pinning the parameter inequality's RHS.

The strict inequalities are the **parameter-algebra** obligation (random-restriction /
binomial-ratio estimate), stated here as hypotheses, to be discharged by the choice of
restriction parameters.

What remains open (genuinely new collapse-side machinery, not faked here):
* discharging the parameter inequality from a concrete random-restriction model;
* the **assembly**: a good restriction collapses the circuit to a short `LDeriv` refutation
  (the object-matching step — switching's `termSat` AND-clauses vs the ΣΠΣ bottom OR-clauses).

So this is the honest interface seam: the canonical count is consumed to produce a
simultaneously-good restriction; the collapse-assembly remains the open gate.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Pigeonhole: a good restriction exists.**  If the bad set is bounded by `|Short| · (2w)^s`
and that is strictly less than the total number of restrictions, some restriction is not bad. -/
theorem exists_good_restriction {w s : ℕ} {Bad Short : Finset (Restriction n)}
    (hcount : Bad.card ≤ Short.card * (2 * w) ^ s)
    (hlt : Short.card * (2 * w) ^ s < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ρ ∉ Bad := by
  have hBad : Bad.card < (Finset.univ : Finset (Restriction n)).card := lt_of_le_of_lt hcount hlt
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Restriction n)) ⊆ Bad := fun ρ _ => h ρ
  exact absurd (Finset.card_le_card hsub) (not_le.mpr hBad)

/-- **Count ⟹ good restriction, via the canonical switching count.**  Discharges the bad-set
bound from `canonMarkLabel_switching_count` and applies the pigeonhole: under the parameter
condition `|Short| · (2w)^s < 3^n` (the total restriction count), a non-bad restriction exists.
This is the first link consuming the canonical `(2w)^s` count in the collapse pipeline. -/
theorem exists_good_restriction_canon {w s : ℕ} [NeZero w] {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hne : ∀ ρ ∈ Bad, ∀ b ∈ canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))), b ≠ [])
    (hlen : ∀ ρ ∈ Bad, (ungroupBlocks (canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))))).length = s)
    (hmem : ∀ ρ ∈ Bad, complete ρ (encLits ρ cs) ∈ Short)
    (hlt : Short.card * (2 * w) ^ s < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ρ ∉ Bad :=
  exists_good_restriction (canonMarkLabel_switching_count hcs hwidth hne hlen hmem) hlt

/-- **Union bound: one good restriction for all gates.**  Given a finite family of bad sets
(one per bottom gate), each bounded by `B`, if `#gates · B < #restrictions` then some single
restriction is good for *every* gate.  Composing with `canonMarkLabel_switching_count`
(`B = |Short| · (2w)^s` per gate) this supplies the simultaneously-good restriction the collapse
argument needs — link (b) of the count → collapse chain. -/
theorem exists_good_restriction_forall {ι : Type*} (gates : Finset ι)
    (Bad : ι → Finset (Restriction n)) (B : ℕ)
    (hcount : ∀ i ∈ gates, (Bad i).card ≤ B)
    (hlt : gates.card * B < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ∀ i ∈ gates, ρ ∉ Bad i := by
  have hunion : (gates.biUnion Bad).card ≤ gates.card * B :=
    calc (gates.biUnion Bad).card
        ≤ ∑ i ∈ gates, (Bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ gates, B := Finset.sum_le_sum hcount
      _ = gates.card * B := by rw [Finset.sum_const, smul_eq_mul]
  have hbu : (gates.biUnion Bad).card < (Finset.univ : Finset (Restriction n)).card :=
    lt_of_le_of_lt hunion hlt
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Restriction n)) ⊆ gates.biUnion Bad := by
    intro ρ _
    obtain ⟨i, hi, hρ⟩ := h ρ
    exact Finset.mem_biUnion.mpr ⟨i, hi, hρ⟩
  exact absurd (Finset.card_le_card hsub) (not_le.mpr hbu)

/-- The total number of restrictions is `3^n` (each coordinate is unset / 0 / 1).  Pins the
right-hand side of the parameter-algebra inequality `|Short| · (2w)^s < 3^n`. -/
theorem card_restriction (n : ℕ) :
    (Finset.univ : Finset (Restriction n)).card = 3 ^ n := by
  rw [Finset.card_univ]
  simp [Restriction, Fintype.card_fun, Fintype.card_option, Fintype.card_bool]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_good_restriction_canon
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_good_restriction_forall
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_restriction
