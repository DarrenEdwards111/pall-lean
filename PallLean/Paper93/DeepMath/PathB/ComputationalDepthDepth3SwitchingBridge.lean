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

Correctly parameterized against a restriction **family** `F` (not all `3^n`):
* `exists_good_restriction_in` / `_forall_in` — `|Bad| < |F|` (resp. `#gates·B < |F|`) ⟹ a good
  restriction *in `F`* exists.

The **binomial star-count** that backs the family/short cardinalities (model backing):
* `card_freeVars_eq` — `#{ρ : freeVars ρ = S} = 2^(n-|S|)`;
* `card_stars_eq` — `#{ρ : stars ρ = m} = C(n,m)·2^(n-m)`, so `|F| = |{stars=K}| = C(n,K)·2^(n-K)`
  and (since completions drop `s` stars, `stars_complete_encLits`) `|Short| ≤ C(n,K-s)·2^(n-K+s)`.
  The parameter inequality `|Short|·(2w)^s < |F|` then reduces to the switching ratio
  `[C(n,K-s)/C(n,K)]·(4w)^s < 1`.

What remains open (genuinely new collapse-side machinery, not faked here):
* the binomial-ratio inequality `[C(n,K-s)/C(n,K)]·(4w)^s < 1` for a chosen `(K,s,w)` regime;
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

/-! ### Correctly parameterized: relative to a restriction family `F`

The right comparison is not against *all* `3^n` restrictions but against the **restriction
family** `F` the random restriction draws from (e.g. `{ρ : stars ρ = K}`, the `p`-restriction
support).  The bad set lives inside `F`; a good restriction exists once `|Bad| < |F|`. -/

/-- **Family-relative pigeonhole.**  If the bad restrictions lie in the family `F` and number
fewer than `F`, a good restriction exists *in `F`*. -/
theorem exists_good_restriction_in {Bad F : Finset (Restriction n)}
    (hsub : Bad ⊆ F) (hlt : Bad.card < F.card) :
    ∃ ρ ∈ F, ρ ∉ Bad := by
  have hne : (F \ Bad).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub]; omega
  obtain ⟨ρ, hρ⟩ := hne
  rw [Finset.mem_sdiff] at hρ
  exact ⟨ρ, hρ.1, hρ.2⟩

/-- **Family-relative union bound.**  If each gate's bad set lies in `F` and is bounded by `B`,
and `#gates · B < |F|`, then some restriction in `F` is good for *every* gate.  This is the
correctly parameterized existence: against the restriction-family size `|F|`, with
`B = |Short| · (2w)^s` from the canonical count. -/
theorem exists_good_restriction_forall_in {ι : Type*} (gates : Finset ι) (F : Finset (Restriction n))
    (Bad : ι → Finset (Restriction n)) (B : ℕ)
    (hsub : ∀ i ∈ gates, Bad i ⊆ F)
    (hcount : ∀ i ∈ gates, (Bad i).card ≤ B)
    (hlt : gates.card * B < F.card) :
    ∃ ρ ∈ F, ∀ i ∈ gates, ρ ∉ Bad i := by
  have hbusub : gates.biUnion Bad ⊆ F := Finset.biUnion_subset.mpr hsub
  have hunion : (gates.biUnion Bad).card ≤ gates.card * B :=
    calc (gates.biUnion Bad).card
        ≤ ∑ i ∈ gates, (Bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ gates, B := Finset.sum_le_sum hcount
      _ = gates.card * B := by rw [Finset.sum_const, smul_eq_mul]
  obtain ⟨ρ, hρF, hρ⟩ := exists_good_restriction_in hbusub (lt_of_le_of_lt hunion hlt)
  exact ⟨ρ, hρF, fun i hi hmem => hρ (Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩)⟩

/-- The total number of restrictions is `3^n` (each coordinate is unset / 0 / 1).  Pins the
right-hand side of the parameter-algebra inequality `|Short| · (2w)^s < 3^n`. -/
theorem card_restriction (n : ℕ) :
    (Finset.univ : Finset (Restriction n)).card = 3 ^ n := by
  rw [Finset.card_univ]
  simp [Restriction, Fintype.card_fun, Fintype.card_option, Fintype.card_bool]

/-! ### The binomial-ratio inequality (the switching parameter condition) -/

/-- One descending step of the binomial ratio.  In the sparse regime `4w·K ≤ n−K`, dropping the
chosen count by one costs at least a factor `4w`: `C(n, K−s−1) · 4w ≤ C(n, K−s)`.  Via the
recurrence `C(n,k+1)·(k+1) = C(n,k)·(n−k)` and cancellation. -/
theorem choose_step_bound {n K w : ℕ} (hKn : K ≤ n) (hcond : 4 * w * K ≤ n - K) {s : ℕ}
    (hs : s + 1 ≤ K) : Nat.choose n (K - (s + 1)) * (4 * w) ≤ Nat.choose n (K - s) := by
  have hpos : 0 < K - s := by omega
  have hks1 : K - (s + 1) = K - s - 1 := by omega
  -- recurrence at k = K - s - 1:  C(n, K-s) * (K-s) = C(n, K-s-1) * (n - K + s + 1)
  have hrec : Nat.choose n (K - s) * (K - s)
      = Nat.choose n (K - s - 1) * (n - (K - s - 1)) := by
    have := Nat.choose_succ_right_eq n (K - s - 1)
    rwa [Nat.sub_add_cancel hpos] at this
  -- the parameter condition, localized:  4w·(K-s) ≤ n - (K-s-1)
  have hloc : 4 * w * (K - s) ≤ n - (K - s - 1) := by
    have h1 : 4 * w * (K - s) ≤ 4 * w * K := Nat.mul_le_mul_left _ (by omega)
    omega
  -- multiply through and cancel (K - s)
  have hmul : Nat.choose n (K - (s + 1)) * (4 * w) * (K - s) ≤ Nat.choose n (K - s) * (K - s) := by
    rw [hrec, hks1]
    calc Nat.choose n (K - s - 1) * (4 * w) * (K - s)
        = Nat.choose n (K - s - 1) * (4 * w * (K - s)) := by ring
      _ ≤ Nat.choose n (K - s - 1) * (n - (K - s - 1)) := Nat.mul_le_mul_left _ hloc
  exact Nat.le_of_mul_le_mul_right hmul hpos

/-- **The binomial-ratio inequality.**  In the sparse regime `4w·K ≤ n−K`, dropping `s` from the
chosen count costs at least `(4w)^s`:  `C(n, K−s) · (4w)^s ≤ C(n, K)`.  This is the switching
parameter condition: with `|F| = C(n,K)·2^(n−K)` and `|Short| ≤ C(n,K−s)·2^(n−K+s)`, it gives
`|Short|·(2w)^s ≤ |F|` (since `2^s·(2w)^s = (4w)^s`). -/
theorem choose_descend_bound {n K w : ℕ} (hKn : K ≤ n) (hcond : 4 * w * K ≤ n - K) :
    ∀ s, s ≤ K → Nat.choose n (K - s) * (4 * w) ^ s ≤ Nat.choose n K := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hs
    calc Nat.choose n (K - (s + 1)) * (4 * w) ^ (s + 1)
        = Nat.choose n (K - (s + 1)) * (4 * w) * (4 * w) ^ s := by ring
      _ ≤ Nat.choose n (K - s) * (4 * w) ^ s :=
          Nat.mul_le_mul_right _ (choose_step_bound hKn hcond hs)
      _ ≤ Nat.choose n K := ih (by omega)

/-- **The parameter-algebra inequality (cardinality form).**  Combining the binomial ratio with
the family/short cardinalities: in the sparse regime `4w·K ≤ n−K`,

  `C(n,K−s)·2^(n−K+s) · (2w)^s  ≤  C(n,K)·2^(n−K)`,

i.e. `|Short-bound| · (2w)^s ≤ |F|` (with `F = {stars=K}`, `Short ⊆ {stars=K−s}`).  This is the
parameter inequality the good-restriction existence needs, now *model-backed* by the binomial
star-count rather than assumed. -/
theorem param_ineq {n K w : ℕ} (hKn : K ≤ n) (hcond : 4 * w * K ≤ n - K) {s : ℕ} (hs : s ≤ K) :
    Nat.choose n (K - s) * 2 ^ (n - K + s) * (2 * w) ^ s ≤ Nat.choose n K * 2 ^ (n - K) := by
  have h4w : (4 * w) ^ s = 2 ^ s * (2 * w) ^ s := by rw [← mul_pow]; congr 1; ring
  have hrw : Nat.choose n (K - s) * 2 ^ (n - K + s) * (2 * w) ^ s
      = (Nat.choose n (K - s) * (4 * w) ^ s) * 2 ^ (n - K) := by
    rw [pow_add, h4w]; ring
  rw [hrw]
  exact Nat.mul_le_mul_right _ (choose_descend_bound hKn hcond s hs)

/-! ### The binomial star-count (model backing for `|F|` and `|Short|`) -/

/-- **Fiber count.**  The restrictions with a *given* free-variable set `S` are exactly the
functions assigning a Boolean to each coordinate outside `S` (and `none` inside `S`), so there
are `2^(n - |S|)` of them. -/
theorem card_freeVars_eq (S : Finset (Fin n)) :
    (Finset.univ.filter (fun ρ : Restriction n => freeVars ρ = S)).card = 2 ^ (n - S.card) := by
  have hpi : (Finset.univ.filter (fun ρ : Restriction n => freeVars ρ = S))
      = Fintype.piFinset (fun i =>
          if i ∈ S then ({none} : Finset (Option Bool)) else {some true, some false}) := by
    ext ρ
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro hfv i
      by_cases hi : i ∈ S
      · have hnone : ρ i = none := mem_freeVars.mp (by rw [hfv]; exact hi)
        simp [hi, hnone]
      · have hne : ρ i ≠ none := fun hc => hi (hfv ▸ mem_freeVars.mpr hc)
        simp only [hi, if_false, Finset.mem_insert, Finset.mem_singleton]
        cases hρ : ρ i with
        | none => exact absurd hρ hne
        | some b => cases b <;> simp
    · intro h
      ext i
      rw [mem_freeVars]
      by_cases hi : i ∈ S
      · have := h i; simp only [hi, if_true, Finset.mem_singleton] at this
        simp [hi, this]
      · have := h i
        simp only [hi, if_false, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h1 | h1 <;> simp [hi, h1]
  rw [hpi, Fintype.card_piFinset]
  have hval : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (if i ∈ S then ({none} : Finset (Option Bool)) else {some true, some false}).card
        = if i ∈ S then (1 : ℕ) else 2 := by
    intro i _; by_cases hi : i ∈ S <;> simp [hi]
  rw [Finset.prod_congr rfl hval, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const]
  congr 1
  have : (Finset.univ.filter (fun x : Fin n => ¬ x ∈ S)) = Finset.univ \ S := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]

/-- **The binomial star-count.**  The number of restrictions with exactly `m` free variables is
`C(n,m) · 2^(n-m)`: choose the `m` free coordinates (`C(n,m)`), assign each of the other `n-m` a
Boolean (`2^(n-m)`).  This is the cardinality of the restriction family `{ρ : stars ρ = m}` — the
quantity that backs `|F|` (and, at `m-s`, the `|Short|` bound) in the parameter algebra. -/
theorem card_stars_eq (m : ℕ) :
    (Finset.univ.filter (fun ρ : Restriction n => stars ρ = m)).card = n.choose m * 2 ^ (n - m) := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ρ : Restriction n => freeVars ρ) (t := Finset.univ.powersetCard m)
    (fun ρ hρ => by
      simp only [Finset.mem_coe, Finset.mem_filter] at hρ
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hρ.2⟩)]
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ((Finset.univ.filter (fun ρ : Restriction n => stars ρ = m)).filter
        (fun ρ => freeVars ρ = S)).card = 2 ^ (n - m) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have heq : (Finset.univ.filter (fun ρ : Restriction n => stars ρ = m)).filter
        (fun ρ => freeVars ρ = S) = Finset.univ.filter (fun ρ => freeVars ρ = S) := by
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨by rw [show stars ρ = (freeVars ρ).card from rfl, h]; exact hS.2, h⟩⟩
    rw [heq, card_freeVars_eq, hS.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Parameter inequality in concrete form.**  The simultaneously-good restriction exists once
`#gates · |Short| · (2w)^s < 3^n` — the explicit numeric obligation against the total restriction
count `3^n` (`card_restriction`).  This is the precise parameter-algebra target the random-
restriction parameters must meet. -/
theorem exists_good_restriction_forall_pow {ι : Type*} (gates : Finset ι)
    (Bad : ι → Finset (Restriction n)) (B : ℕ)
    (hcount : ∀ i ∈ gates, (Bad i).card ≤ B)
    (hlt : gates.card * B < 3 ^ n) :
    ∃ ρ : Restriction n, ∀ i ∈ gates, ρ ∉ Bad i := by
  rw [← card_restriction n] at hlt
  exact exists_good_restriction_forall gates Bad B hcount hlt

/-- Single-gate concrete form: `|Short| · (2w)^s < 3^n ⟹ a good restriction exists`. -/
theorem exists_good_restriction_pow {w s : ℕ} {Bad Short : Finset (Restriction n)}
    (hcount : Bad.card ≤ Short.card * (2 * w) ^ s)
    (hlt : Short.card * (2 * w) ^ s < 3 ^ n) :
    ∃ ρ : Restriction n, ρ ∉ Bad := by
  rw [← card_restriction n] at hlt
  exact exists_good_restriction hcount hlt

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_good_restriction_canon
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_good_restriction_forall
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_good_restriction_in
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_good_restriction_forall_in
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.choose_descend_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.param_ineq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_freeVars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_stars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_restriction
