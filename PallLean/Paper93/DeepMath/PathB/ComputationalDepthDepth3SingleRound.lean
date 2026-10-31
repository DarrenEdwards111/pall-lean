import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowAll
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfCircuit

/-!
# AC⁰ reduction, foundation 8: the single-round collapse (branch only)

The assembly of one collapse round.  Take an `AND` of bottom DNF gates (`and (G.map dnfToCircuit)`,
depth ≥ 3).  The union-bound restriction (`exists_shallow_all`, brick 71) makes every gate's canonical
tree shallow (`depth < s`); each shallow tree rewrites to a width-`< s` CNF (`dtreeToCNF`, brick 67) that
computes the same function on the subcube (`canonicalDTree_eval`, brick 29).  Concatenating those CNFs
gives a **single CNF of width `< s`** — a depth-2 `AND`-of-`OR`s — that computes the original circuit on
the `ρ`-subcube.  Depth `d → 2` in one round.

* `single_round_collapse` — `∃ ρ`, `∃` a width-`< s` CNF computing `and (G.map dnfToCircuit)` on the
  `ρ`-subcube.

This ties the switching machinery (bricks 36–71) to the circuit substrate.  Iterating it down to the
depth-2 parity bound (brick 35) is the remaining multi-round induction.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting ACircuit

variable {n : ℕ}

private theorem all_congr {α : Type*} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **The single-round collapse.**  An `AND` of bottom DNF gates collapses, under the union-bound
restriction, to a single width-`< s` CNF computing the same function on the `ρ`-subcube. -/
theorem single_round_collapse {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ) (hF : n < F)
    (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hsmall : (G.card : ℚ)
        * ((2 * p / (1 - p)) ^ s
            * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1) :
    ∃ ρ : Fin n → Option Bool, ∃ cnf : List (Clause n),
      (∀ x, DTree.agreeRestriction ρ x →
        cnfValue cnf x = (ACircuit.and (G.toList.map dnfToCircuit)).eval x)
      ∧ (∀ C ∈ cnf, C.lits.length < s) := by
  obtain ⟨ρ, hρ⟩ := exists_shallow_all hp0 hp3 w F s G hcons hnd hw hsmall
  refine ⟨ρ, G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)), fun x hx => ?_, ?_⟩
  · have hstars : stars ρ < F :=
      lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
    have h1 : (ACircuit.and (G.toList.map dnfToCircuit)).eval x
        = G.toList.all (fun g => DTree.dnfValue g x) := by
      rw [eval_and, List.all_map]
      exact all_congr _ _ _ (fun g _ => dnfToCircuit_eval g x)
    have h2 : cnfValue (G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ))) x
        = G.toList.all (fun g => DTree.dnfValue g x) := by
      rw [cnfValue, List.all_flatMap]
      apply all_congr
      intro g hg
      rw [← cnfValue, dtreeToCNF_eval, canonicalDTree_eval g w F ρ x hstars hx]
    rw [h1, h2]
  · intro C hC
    rw [List.mem_flatMap] at hC
    obtain ⟨g, hg, hCg⟩ := hC
    have hwidth := dtreeToCNF_width (canonicalDTree g w F ρ) C hCg
    have hshallow := hρ g (Finset.mem_toList.mp hg)
    omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.single_round_collapse
