import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4SwitchingCore

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

open Rung4DNFTerm

/-- The variable a `Rung4Literal` queries. -/
def rvar {n : ℕ} : Rung4Literal n → Fin n
  | .pos i => i
  | .neg i => i

/-- **Surviving literals are free.**  Every literal in a non-falsified restricted term lies on a
variable left *free* by the restriction (`restrictLits` keeps exactly the `none` literals).  So
the residual width is carried entirely by the free coordinates — the structural fact behind
"few stars ⟹ small residual width". -/
theorem restrictLits_all_free {n : ℕ} (ρ : Fin n → Option Bool) :
    ∀ (lits out : List (Rung4Literal n)), restrictLits ρ lits = some out →
      ∀ ℓ ∈ out, ρ (rvar ℓ) = none := by
  intro lits
  induction lits with
  | nil => intro out h ℓ hℓ; simp [restrictLits] at h; subst out; simp at hℓ
  | cons lit rest ih =>
    intro out h ℓ hℓ
    cases lit with
    | pos i =>
      cases hρ : ρ i with
      | none =>
        cases hrest : restrictLits ρ rest with
        | none => simp [restrictLits, hρ, hrest] at h
        | some rest' =>
          simp [restrictLits, hρ, hrest] at h
          subst out
          rcases List.mem_cons.mp hℓ with rfl | hℓ'
          · simpa [rvar] using hρ
          · exact ih rest' hrest ℓ hℓ'
      | some b =>
        cases b
        · simp [restrictLits, hρ] at h
        · simp [restrictLits, hρ] at h; exact ih out h ℓ hℓ
    | neg i =>
      cases hρ : ρ i with
      | none =>
        cases hrest : restrictLits ρ rest with
        | none => simp [restrictLits, hρ, hrest] at h
        | some rest' =>
          simp [restrictLits, hρ, hrest] at h
          subst out
          rcases List.mem_cons.mp hℓ with rfl | hℓ'
          · simpa [rvar] using hρ
          · exact ih rest' hrest ℓ hℓ'
      | some b =>
        cases b
        · simp [restrictLits, hρ] at h; exact ih out h ℓ hℓ
        · simp [restrictLits, hρ] at h

/-! ### Gate 2 (length bound): a depth-`d` decision tree has `≤ 2^d` leaves

The DT→`LDeriv` *construction* (a shallow decision tree for the restricted refuting circuit
yields a resolution refutation of the Tseitin axioms — one clause per leaf, resolved up the
tree) is the remaining open proof-complexity content.  Its refutation *length* is the number of
leaves, which is `≤ 2^depth` — the bound below, giving `collapseLen ≈ 2^depth`. -/

namespace BoolDecisionTree

/-- The number of leaves of a decision tree (the refutation length the DT→resolution map
produces). -/
def leaves {n : ℕ} : BoolDecisionTree n → ℕ
  | leaf _ => 1
  | query _ low high => low.leaves + high.leaves

/-- **A depth-`d` decision tree has at most `2^d` leaves.**  So the resolution refutation gate 2
extracts has length `≤ 2^depth`. -/
theorem leaves_le_two_pow_depth {n : ℕ} (T : BoolDecisionTree n) : T.leaves ≤ 2 ^ T.depth := by
  induction T with
  | leaf b => simp [leaves, depth]
  | query i low high ihl ihh =>
    calc low.leaves + high.leaves
        ≤ 2 ^ low.depth + 2 ^ high.depth := Nat.add_le_add ihl ihh
      _ ≤ 2 ^ (max low.depth high.depth) + 2 ^ (max low.depth high.depth) :=
          Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
            (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      _ = 2 ^ (max low.depth high.depth + 1) := by rw [pow_succ]; ring

end BoolDecisionTree

/-! ### The depth-`=`-path-length decision tree (the depth-based DT-collapse)

A decision tree that queries a given variable list in order has depth exactly the list length,
and it *computes* any Boolean function depending only on those variables.  Applied to the
canonical path variables and the restricted DNF, this is the DT-collapse the depth-based gate 1
needs: a **short path ⟹ a short decision tree computing the DNF** — with depth equal to the path
length (not `Rung4`'s `toDecisionTree`, whose depth is bounded by `totalWidth`).  The one
remaining input is that the DNF depends only on the path variables (`DependsOn`), which is the
switching conclusion. -/

/-- `F` depends only on the variables in `vars`. -/
def DependsOn {n : ℕ} (F : (Fin n → Bool) → Bool) (vars : List (Fin n)) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i ∈ vars, x i = y i) → F x = F y

/-- The decision tree querying `vars` in order; each leaf outputs `F` on the path-determined
assignment. -/
def pathTree {n : ℕ} : List (Fin n) → ((Fin n → Bool) → Bool) → BoolDecisionTree n
  | [], F => BoolDecisionTree.leaf (F (fun _ => false))
  | i :: rest, F => BoolDecisionTree.query i
      (pathTree rest (fun x => F (Function.update x i false)))
      (pathTree rest (fun x => F (Function.update x i true)))

/-- **Depth `=` path length.**  The query tree over `vars` has depth exactly `vars.length`. -/
theorem pathTree_depth {n : ℕ} (vars : List (Fin n)) (F : (Fin n → Bool) → Bool) :
    (pathTree vars F).depth = vars.length := by
  induction vars generalizing F with
  | nil => rfl
  | cons i rest ih => simp only [pathTree, BoolDecisionTree.depth, ih, List.length_cons, max_self]

/-- **The query tree computes any function depending only on the queried variables.** -/
theorem pathTree_eval {n : ℕ} (vars : List (Fin n)) (F : (Fin n → Bool) → Bool)
    (hdep : DependsOn F vars) (x : Fin n → Bool) : (pathTree vars F).eval x = F x := by
  induction vars generalizing F with
  | nil =>
    simp only [pathTree, BoolDecisionTree.eval]
    exact hdep _ x (by simp)
  | cons i rest ih =>
    have hdepF : ∀ b : Bool, DependsOn (fun y => F (Function.update y i b)) rest := by
      intro b a c hac
      refine hdep _ _ (fun k hk => ?_)
      by_cases hki : k = i
      · subst hki; simp [Function.update_self]
      · simp only [Function.update_of_ne hki]
        exact hac k ((List.mem_cons.mp hk).resolve_left hki)
    simp only [pathTree, BoolDecisionTree.eval]
    cases hxi : x i with
    | true =>
      simp only [hxi, if_true]
      rw [ih _ (hdepF true),
        show Function.update x i true = x from by rw [← hxi]; exact Function.update_eq_self i x]
    | false =>
      simp only [hxi, Bool.false_eq_true, if_false]
      rw [ih _ (hdepF false),
        show Function.update x i false = x from by rw [← hxi]; exact Function.update_eq_self i x]

/-- **The depth-based DT-collapse.**  If a Boolean function `F` depends only on the path
variables `vars` and the path is short (`vars.length ≤ budget`), then `F` is computed by a
decision tree of depth `≤ budget` — namely `pathTree vars F`, whose depth is *exactly* the path
length.  This is the short-path ⟹ short-DT collapse with depth `=` path length (not `Rung4`'s
`totalWidth` bound).  Applied to the restricted DNF (`F`), the path variables, and the switching
conclusion (`DependsOn F vars`), it discharges the DT-collapse the depth-based gate 1 needs. -/
theorem short_path_yields_short_dt {n : ℕ} {vars : List (Fin n)} {F : (Fin n → Bool) → Bool}
    {budget : ℕ} (hlen : vars.length ≤ budget) (hdep : DependsOn F vars) :
    ∃ T : BoolDecisionTree n, T.depth ≤ budget ∧ ∀ x : Fin n → Bool, T.eval x = F x :=
  ⟨pathTree vars F, by rw [pathTree_depth]; exact hlen, fun x => pathTree_eval vars F hdep x⟩

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

/-- Strict descending step: in the *strict* sparse regime `4w·K < n−K`,
`C(n, K−s−1) · 4w < C(n, K−s)`. -/
theorem choose_step_lt {n K w : ℕ} (hKn : K ≤ n) (hcond : 4 * w * K < n - K) {s : ℕ}
    (hs : s + 1 ≤ K) : Nat.choose n (K - (s + 1)) * (4 * w) < Nat.choose n (K - s) := by
  have hpos : 0 < K - s := by omega
  have hks1 : K - (s + 1) = K - s - 1 := by omega
  have hrec : Nat.choose n (K - s) * (K - s)
      = Nat.choose n (K - s - 1) * (n - (K - s - 1)) := by
    have := Nat.choose_succ_right_eq n (K - s - 1)
    rwa [Nat.sub_add_cancel hpos] at this
  have hcpos : 0 < Nat.choose n (K - s - 1) := Nat.choose_pos (by omega)
  have hloc : 4 * w * (K - s) < n - (K - s - 1) := by
    have h1 : 4 * w * (K - s) ≤ 4 * w * K := Nat.mul_le_mul_left _ (by omega)
    omega
  have hmul : Nat.choose n (K - (s + 1)) * (4 * w) * (K - s) < Nat.choose n (K - s) * (K - s) := by
    rw [hrec, hks1]
    calc Nat.choose n (K - s - 1) * (4 * w) * (K - s)
        = Nat.choose n (K - s - 1) * (4 * w * (K - s)) := by ring
      _ < Nat.choose n (K - s - 1) * (n - (K - s - 1)) := Nat.mul_lt_mul_of_pos_left hloc hcpos
  exact lt_of_mul_lt_mul_right hmul (Nat.zero_le _)

/-- **Strict binomial-ratio inequality.**  In the strict regime `4w·K < n−K` with `1 ≤ s ≤ K`,
`C(n, K−s) · (4w)^s < C(n, K)` — the strict bound the pigeonhole needs. -/
theorem choose_descend_lt {n K w : ℕ} (hKn : K ≤ n) (hcond : 4 * w * K < n - K) :
    ∀ s, 1 ≤ s → s ≤ K → Nat.choose n (K - s) * (4 * w) ^ s < Nat.choose n K := by
  intro s
  induction s with
  | zero => intro h _; omega
  | succ s ih =>
    intro _ hs
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · subst hs0
      simpa using choose_step_lt hKn hcond hs
    · calc Nat.choose n (K - (s + 1)) * (4 * w) ^ (s + 1)
          = Nat.choose n (K - (s + 1)) * (4 * w) * (4 * w) ^ s := by ring
        _ ≤ Nat.choose n (K - s) * (4 * w) ^ s :=
            Nat.mul_le_mul_right _ (choose_step_bound hKn (le_of_lt hcond) hs)
        _ < Nat.choose n K := ih hs0 (by omega)

/-- **Strict parameter inequality.**  `|Short-bound| · (2w)^s < |F|` in the strict regime — the
form the family-relative pigeonhole consumes. -/
theorem param_ineq_lt {n K w : ℕ} (hKn : K ≤ n) (hcond : 4 * w * K < n - K) {s : ℕ}
    (hs1 : 1 ≤ s) (hs : s ≤ K) :
    Nat.choose n (K - s) * 2 ^ (n - K + s) * (2 * w) ^ s < Nat.choose n K * 2 ^ (n - K) := by
  have h4w : (4 * w) ^ s = 2 ^ s * (2 * w) ^ s := by rw [← mul_pow]; congr 1; ring
  have hrw : Nat.choose n (K - s) * 2 ^ (n - K + s) * (2 * w) ^ s
      = (Nat.choose n (K - s) * (4 * w) ^ s) * 2 ^ (n - K) := by
    rw [pow_add, h4w]; ring
  rw [hrw]
  exact Nat.mul_lt_mul_of_lt_of_le (choose_descend_lt hKn hcond s hs1 hs) (le_refl _)
    (by positivity)

/-! ### Assembly link: good restriction ⟹ a short decision tree (on real DT machinery) -/

/-- **Good restriction ⟹ short decision tree.**  Composing the count's good-restriction
existence with the deterministic switching substrate
(`Rung4DNF.exists_restrictedDecisionTree_of_residualWidth_le`): if a good restriction (one not
in `Bad`) leaves the DNF with residual total width `≤ depthBudget`, then there is a good `ρ`
and a decision tree of depth `≤ depthBudget` computing the DNF on `ρ`'s subcube.

This is a genuine link of the **assembly**, built on the real `BoolDecisionTree` machinery — not
faked.  The one named gate `hresid` (good restriction ⟹ small residual width) is the honest
remaining switching-lemma structural content connecting the canonical path length (which the
`(2w)^s` count bounds) to the residual DNF width. -/
theorem good_restriction_yields_short_dt {depthBudget : ℕ} (D : Rung4DNF n)
    {Bad : Finset (Restriction n)}
    (hgood : ∃ ρ : Restriction n, ρ ∉ Bad)
    (hresid : ∀ ρ : Restriction n, ρ ∉ Bad → (D.restrict ρ).totalWidth ≤ depthBudget) :
    ∃ ρ : Restriction n, ∃ T : BoolDecisionTree n,
      T.depth ≤ depthBudget ∧
      ∀ x : Fin n → Bool, Rung4Restriction.Extends ρ x → T.eval x = D.eval x := by
  obtain ⟨ρ, hρ⟩ := hgood
  obtain ⟨T, hTd, hTe⟩ := D.exists_restrictedDecisionTree_of_residualWidth_le ρ (hresid ρ hρ)
  exact ⟨ρ, T, hTd, hTe⟩

/-- The **width-bad set**: restrictions leaving the residual DNF with width above budget.  This
is exactly the set the `(2w)^s` count must control; the genuine switching content is that the
canonical path is long (so `ρ` is counted) precisely when the residual width is large. -/
def widthBad (D : Rung4DNF n) (depthBudget : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter (fun ρ => depthBudget < (D.restrict ρ).totalWidth)

/-- **Gate 1 (definitional core).**  A restriction *outside* the width-bad set leaves residual
width `≤ depthBudget`.  This is the `hresid` good-restriction ⟹ small-residual-width gate, with
the bad set taken to be exactly the width-bad set — so the remaining obligation is purely that
the switching count bounds `widthBad`. -/
theorem residual_width_le_of_not_widthBad {D : Rung4DNF n} {depthBudget : ℕ} {ρ : Restriction n}
    (hρ : ρ ∉ widthBad D depthBudget) : (D.restrict ρ).totalWidth ≤ depthBudget := by
  simp only [widthBad, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hρ
  exact hρ

/-- **Gate 1 ⟹ short decision tree.**  A restriction outside the width-bad set yields a depth-
`≤ depthBudget` decision tree computing the DNF on its subcube.  Combined with the count's
good-restriction existence (`exists_good_restriction*` applied to `Bad = widthBad`), this closes
the count → DT-collapse arc; the one remaining obligation is `|widthBad| < |F|` (the count bound
on the width-bad set). -/
theorem widthBad_yields_short_dt {D : Rung4DNF n} {depthBudget : ℕ}
    (hgood : ∃ ρ : Restriction n, ρ ∉ widthBad D depthBudget) :
    ∃ ρ : Restriction n, ∃ T : BoolDecisionTree n,
      T.depth ≤ depthBudget ∧
      ∀ x : Fin n → Bool, Rung4Restriction.Extends ρ x → T.eval x = D.eval x :=
  good_restriction_yields_short_dt D hgood (fun _ hρ => residual_width_le_of_not_widthBad hρ)

/-! ### Depth-based bad set (the CORRECT reformulation the count actually bounds) -/

/-- **The path-length bad set.**  Restrictions whose *canonical path* (flat label) has length
exactly `s` — equivalently, whose canonical decision tree fixes `s` variables.  This is the bad
set the `(2w)^s` count *actually* bounds: it is precisely the `hlen` slice of
`canonMarkLabel_switching_count`, not the `totalWidth`-bad set. -/
def pathLenBad (cs : List (Clause n)) (s : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter (fun ρ => (ungroupBlocks (canonPosBlocks (encLits ρ cs) ∅
    (cs.filter (termSat (complete ρ (encLits ρ cs)))))).length = s)

/-- **The count bounds the path-length bad set.**  For the *correct* (path-length) bad set,
`hlen` holds by definition (filter membership), so `canonMarkLabel_switching_count` bounds it:
`|pathLenBad cs s| ≤ |Short| · (2w)^s`.  This is the honest depth-based gate 1 — the count
controls exactly the restrictions whose canonical path has length `s`. -/
theorem canon_count_pathLenBad {w s : ℕ} [NeZero w] {cs : List (Clause n)}
    {Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hne : ∀ ρ ∈ pathLenBad cs s, ∀ b ∈ canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))), b ≠ [])
    (hmem : ∀ ρ ∈ pathLenBad cs s, complete ρ (encLits ρ cs) ∈ Short) :
    (pathLenBad cs s).card ≤ Short.card * (2 * w) ^ s := by
  refine canonMarkLabel_switching_count hcs hwidth hne ?_ hmem
  intro ρ hρ
  simp only [pathLenBad, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
  exact hρ

/-- The canonical path length (flat-label length) of `ρ`. -/
def canonLabelLen (ρ : Restriction n) (cs : List (Clause n)) : ℕ :=
  (ungroupBlocks (canonPosBlocks (encLits ρ cs) ∅
    (cs.filter (termSat (complete ρ (encLits ρ cs)))))).length

/-- **The geometric sum: the long-path bad set is bounded by the sum of the per-`s` counts.**
`{ρ : path length > budget}` is the disjoint union of `pathLenBad cs s` over `s > budget`, so by
the per-`s` count `canon_count_pathLenBad`,

  `|{ρ : canonLabelLen ρ cs > budget}|  ≤  ∑_{budget < s ≤ maxLen} |Short s| · (2w)^s`.

This is the standard switching-lemma summation over decision-tree depths.  `maxLen` is any upper
bound on the path length (e.g. `n`); the sum is finite because path lengths are bounded. -/
theorem pathLenBadGt_card_le {w : ℕ} [NeZero w] {cs : List (Clause n)}
    {Short : ℕ → Finset (Restriction n)} {budget maxLen : ℕ}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hmax : ∀ ρ : Restriction n, canonLabelLen ρ cs ≤ maxLen)
    (hne : ∀ s : ℕ, ∀ ρ ∈ pathLenBad cs s, ∀ b ∈ canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))), b ≠ [])
    (hmem : ∀ s : ℕ, ∀ ρ ∈ pathLenBad cs s, complete ρ (encLits ρ cs) ∈ Short s) :
    (Finset.univ.filter (fun ρ : Restriction n => budget < canonLabelLen ρ cs)).card
      ≤ ∑ s ∈ (Finset.range (maxLen + 1)).filter (fun s => budget < s),
          (Short s).card * (2 * w) ^ s := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ρ : Restriction n => canonLabelLen ρ cs)
    (t := (Finset.range (maxLen + 1)).filter (fun s => budget < s))
    (fun ρ hρ => by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range] at hρ ⊢
      exact ⟨Nat.lt_succ_of_le (hmax ρ), hρ⟩)]
  refine Finset.sum_le_sum (fun s hs => ?_)
  simp only [Finset.mem_filter, Finset.mem_range] at hs
  have heq : (Finset.univ.filter (fun ρ : Restriction n => budget < canonLabelLen ρ cs)).filter
      (fun ρ => canonLabelLen ρ cs = s) = pathLenBad cs s := by
    ext ρ
    simp only [pathLenBad, canonLabelLen, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  rw [heq]
  exact canon_count_pathLenBad hcs hwidth (hne s) (hmem s)

/-! ### ⚠ `hincl` analysis: the `totalWidth`-bad set is the WRONG bad set (do not chase it)

A natural attempt is to discharge `hincl : widthBad D depthBudget ⊆ Bad` and bound `|widthBad|`
by the `(2w)^s` count.  **This is false as stated**, for genuine reasons (recorded so future
work does not chase it):

* `widthBad` uses `(D.restrict ρ).totalWidth`, a **sum** over surviving terms.  A restriction
  with *many small* surviving terms has large `totalWidth` but a **shallow** canonical decision
  tree — it is **not** bad.  (`totalWidth ≤ depthBudget ⟹ shallow DT` is *sufficient but loose*:
  `toDecisionTree_depth_le_totalWidth`.)
* The canonical-path length that the `(2w)^s` count bounds satisfies `path ≤ totalWidth` (each
  block's *current*-free literals `⊆` the term's `ρ`-free literals, since the accumulating
  completion fixes more than `ρ`).  So large `totalWidth` does **not** force a long path.
* Against the count directly: `canonMarkLabel_switching_count`'s `Bad` has every element of flat-
  label length **exactly `s`** (`hlen`).  A `totalWidth`-bad `ρ` with a short canonical path has
  label length `< s`, failing `hlen`.  So the count **cannot** bound the `totalWidth`-bad set.

**Correct reformulation:** the bad set must be **canonical-decision-tree-depth-based** (= the
path length the count bounds), not `totalWidth`-based.  A genuine `hincl` needs a *depth-based*
`widthBad` and a canonical DT whose depth equals the path length — not `Rung4SwitchingCore`'s
`toDecisionTree` (depth bounded by `totalWidth`).  Building that is the real remaining work;
`widthBad_collapse_dt` below is kept as a conditional composition, but its `hincl` hypothesis is
**not** dischargeable with the `totalWidth` `widthBad`. -/

/-- **G1-core reduced + the whole arc composed.**  Given the canonical `(2w)^s` count for a bad
set `Bad`, the parameter inequality `|Short|·(2w)^s < #restrictions`, and the **structural
inclusion** `widthBad ⊆ Bad` (a restriction leaving large residual width is counted by the
canonical encoding), the entire count → DT-collapse arc closes: there is a restriction `ρ` and a
decision tree of depth `≤ depthBudget` computing the DNF `D` on `ρ`'s subcube.

The inclusion `hincl` is the *one* genuine remaining structural fact of G1-core — that large
residual width forces a long canonical path (so `ρ ∈ Bad`).  It reconciles the `SwitchingCounting`
encoding with `Rung4SwitchingCore`'s residual width, and is the irreducible switching-lemma
content; everything else here is proved.  `hlt` is model-backed by `param_ineq_lt`. -/
theorem widthBad_collapse_dt {w s : ℕ} [NeZero w] {cs : List (Clause n)} {D : Rung4DNF n}
    {Bad Short : Finset (Restriction n)} {depthBudget : ℕ}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hne : ∀ ρ ∈ Bad, ∀ b ∈ canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))), b ≠ [])
    (hlen : ∀ ρ ∈ Bad, (ungroupBlocks (canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))))).length = s)
    (hmem : ∀ ρ ∈ Bad, complete ρ (encLits ρ cs) ∈ Short)
    (hincl : widthBad D depthBudget ⊆ Bad)
    (hlt : Short.card * (2 * w) ^ s < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ∃ T : BoolDecisionTree n,
      T.depth ≤ depthBudget ∧
      ∀ x : Fin n → Bool, Rung4Restriction.Extends ρ x → T.eval x = D.eval x := by
  have hcount := canonMarkLabel_switching_count hcs hwidth hne hlen hmem
  have hwbcount : (widthBad D depthBudget).card ≤ Short.card * (2 * w) ^ s :=
    le_trans (Finset.card_le_card hincl) hcount
  exact widthBad_yields_short_dt (exists_good_restriction hwbcount hlt)

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

/-- **`Short ⊆ {stars = K−s}` wiring.**  A bad `ρ` in the star-`K` family whose canonical path
has length `s` has completion with exactly `K−s` stars (`stars_complete_encLits`), so its
completion lands in the family `{stars = K−s}`.  This justifies taking `Short = {stars = K−s}`
and hence `|Short| = C(n,K−s)·2^(n−K+s)` (`card_stars_eq`). -/
theorem completion_mem_stars {cs : List (Clause n)} (ρ : Restriction n) {K s : ℕ}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hstars : stars ρ = K) (hlen : (encLits ρ cs).length = s) :
    complete ρ (encLits ρ cs)
      ∈ Finset.univ.filter (fun σ : Restriction n => stars σ = K - s) := by
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [stars_complete_encLits ρ cs hcs, hstars, hlen]⟩

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
#print axioms PallLean.Paper93.DeepMath.PathB.pathTree_eval
#print axioms PallLean.Paper93.DeepMath.PathB.short_path_yields_short_dt
#print axioms PallLean.Paper93.DeepMath.PathB.restrictLits_all_free
#print axioms PallLean.Paper93.DeepMath.PathB.BoolDecisionTree.leaves_le_two_pow_depth
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.good_restriction_yields_short_dt
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.widthBad_yields_short_dt
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canon_count_pathLenBad
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.pathLenBadGt_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.widthBad_collapse_dt
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.choose_descend_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.param_ineq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.choose_descend_lt
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.param_ineq_lt
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.completion_mem_stars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_freeVars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_stars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_restriction
