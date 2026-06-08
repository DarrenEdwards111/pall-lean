import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SingleRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Negate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3NegTree

/-!
# AC⁰ reduction, foundation 12: the dual single-round collapse (branch only)

The dual of brick 73: an `OR` of bottom CNF gates collapses, under the union-bound restriction, to a single
width-`< s` DNF computing the same function on the subcube.  Each CNF gate is switched via De Morgan
(brick 75) — switch the literal-negated DNF to a shallow tree, negate its leaves (brick 76, preserving
depth) — then rewritten as a width-`≤ depth` DNF (`dtreeToDNF`, brick 66).

* `single_round_collapse_or` — `∃ ρ`, `∃` a width-`< s` DNF computing `or (G.map cnfToCircuit)` on the
  `ρ`-subcube.

With `single_round_collapse` (brick 73), both alternation directions of one collapse round are proven.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting ACircuit

variable {n : ℕ}

private theorem any_congr {α : Type*} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The literal-negated DNF of a CNF (De Morgan). -/
def negDNF (g : List (Clause n)) : List (Clause n) := g.map (fun C => ⟨C.lits.map negLit⟩)

theorem litVarOf_negLit (ℓ : Rung4Literal n) : litVarOf (negLit ℓ) = litVarOf ℓ := by
  cases ℓ <;> rfl

/-- De Morgan in `negDNF` terms. -/
theorem cnfValue_eq_not_dnfValue_negDNF (g : List (Clause n)) (x : Fin n → Bool) :
    cnfValue g x = !(DTree.dnfValue (negDNF g) x) := cnfValue_eq_not_dnfValue g x

theorem consistent_negClause {C : Clause n} (h : Consistent C) :
    Consistent (⟨C.lits.map negLit⟩ : Clause n) := by
  intro v hpn
  obtain ⟨hp, hn⟩ := hpn
  rw [List.mem_map] at hp hn
  obtain ⟨ℓp, hℓp, hep⟩ := hp
  obtain ⟨ℓn, hℓn, hen⟩ := hn
  refine h v ⟨?_, ?_⟩
  · cases ℓn with
    | pos u => rw [negLit] at hen; injection hen with hu; subst hu; exact hℓn
    | neg u => rw [negLit] at hen; exact absurd hen (by simp)
  · cases ℓp with
    | pos u => rw [negLit] at hep; exact absurd hep (by simp)
    | neg u => rw [negLit] at hep; injection hep with hu; subst hu; exact hℓp

/-- **The dual single-round collapse.**  An `OR` of bottom CNF gates collapses, under the union-bound
restriction, to a single width-`< s` DNF computing the same function on the `ρ`-subcube. -/
theorem single_round_collapse_or {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ) (hF : n < F)
    (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ C ∈ g, Consistent C)
    (hnd : ∀ g ∈ G, ∀ C ∈ g, (C.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ C ∈ g, C.lits.length ≤ w)
    (hsmall : (G.card : ℚ)
        * ((2 * p / (1 - p)) ^ s
            * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1) :
    ∃ ρ : Fin n → Option Bool, ∃ dnf : List (Clause n),
      (∀ x, DTree.agreeRestriction ρ x →
        DTree.dnfValue dnf x = (ACircuit.or (G.toList.map cnfToCircuit)).eval x)
      ∧ (∀ T ∈ dnf, T.lits.length < s) := by
  classical
  -- the negated gate set
  have hcons' : ∀ g ∈ G.image negDNF, ∀ T ∈ g, Consistent T := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    exact consistent_negClause (hcons g0 hg0 C hC)
  have hnd' : ∀ g ∈ G.image negDNF, ∀ T ∈ g, (T.lits.map litVarOf).Nodup := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    have : (C.lits.map negLit).map litVarOf = C.lits.map litVarOf := by
      rw [List.map_map]; exact List.map_congr_left (fun ℓ _ => litVarOf_negLit ℓ)
    simpa [this] using hnd g0 hg0 C hC
  have hw' : ∀ g ∈ G.image negDNF, ∀ T ∈ g, T.lits.length ≤ w := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    simpa using hw g0 hg0 C hC
  have hcap_nonneg : 0 ≤ (2 * p / (1 - p)) ^ s
      * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) := by
    have hp1 : (0 : ℚ) < 1 - p := by linarith
    positivity
  have hsmall' : ((G.image negDNF).card : ℚ)
      * ((2 * p / (1 - p)) ^ s
          * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1 :=
    lt_of_le_of_lt
      (by exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le) hcap_nonneg)
      hsmall
  obtain ⟨ρ, hρ⟩ := exists_shallow_all hp0 hp3 w F s (G.image negDNF) hcons' hnd' hw' hsmall'
  have hstars : stars ρ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  -- the good restriction is good for each negated gate
  have hgood : ∀ g ∈ G, (canonicalDTree (negDNF g) w F ρ).depth < s := by
    intro g hg
    exact hρ (negDNF g) (Finset.mem_image_of_mem _ hg)
  refine ⟨ρ,
    G.toList.flatMap (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ))),
    fun x hx => ?_, ?_⟩
  · have h1 : (ACircuit.or (G.toList.map cnfToCircuit)).eval x
        = G.toList.any (fun g => cnfValue g x) := by
      rw [eval_or, List.any_map]
      exact any_congr _ _ _ (fun g _ => cnfToCircuit_eval g x)
    have h2 : DTree.dnfValue
          (G.toList.flatMap (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ)))) x
        = G.toList.any (fun g => cnfValue g x) := by
      rw [DTree.dnfValue, List.any_flatMap]
      apply any_congr
      intro g _
      rw [← DTree.dnfValue, dtreeToDNF_eval, DTree.negTree_eval,
        canonicalDTree_eval (negDNF g) w F ρ x hstars hx, ← cnfValue_eq_not_dnfValue_negDNF]
    rw [h1, h2]
  · intro T hT
    rw [List.mem_flatMap] at hT
    obtain ⟨g, hg, hTg⟩ := hT
    have hwidth := dtreeToDNF_width (DTree.negTree (canonicalDTree (negDNF g) w F ρ)) T hTg
    rw [DTree.negTree_depth] at hwidth
    have hshallow := hgood g (Finset.mem_toList.mp hg)
    omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.single_round_collapse_or
