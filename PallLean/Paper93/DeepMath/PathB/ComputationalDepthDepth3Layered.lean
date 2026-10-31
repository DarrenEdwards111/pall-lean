import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SingleRoundOr
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitSubst

/-!
# AC⁰ reduction, foundation 16: the layered circuit + one collapse step (branch only)

The object the multi-round switching argument recurses on, and the single inductive step that drives its
depth down by one.  A `Layered` circuit is a strictly-alternating tower: a bottom width-bounded `DNF`
(`OR`-of-`AND`s) or `CNF` (`AND`-of-`OR`s), or an `AND`/`OR` of one-level-shallower towers.  We give it a
faithful semantics through `ACircuit` (`toCircuit`), so the per-round switching collapses
(`single_round_collapse` / `single_round_collapse_or`, bricks 73/77) apply verbatim.

* `Layered` / `eval` / `depth` — the type, its Boolean semantics (via `toCircuit`), and its alternation
  depth (a bottom gate counts as depth `2`).
* `collapse_gAnd` — an `AND` of bottom `DNF` gates collapses, on one subcube, to a single bottom `CNF`
  of width `< s`.  This is `single_round_collapse` repackaged in the layered vocabulary.
* `collapse_gOr` — the dual: an `OR` of bottom `CNF` gates collapses to a single bottom `DNF`.
* `gAnd_map_EquivOn` / `gOr_map_EquivOn` — **the iteration glue**: collapsing every child of a gate on a
  *common* subcube collapses the gate itself there.  This is what lifts a bottom collapse up through the
  layer above so the next round can act.

Composed with the round-to-round preservation (bricks 79/80, which keep the collapsed gate's clauses
`Nodup`+`Consistent`) and restriction composition (`round_compose`/`composeR`, bricks 74/78), iterating
these is the full `d → 2` recursion.  Termination at the depth-2 parity bound (brick 35) and the
`poly(w)` base remain.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A strictly-alternating layered AC⁰ circuit: a bottom width-bounded `DNF` (`dnf`) or `CNF` (`cnf`), or
an `AND` (`gAnd`) / `OR` (`gOr`) of one-level-shallower towers. -/
inductive Layered (n : ℕ) where
  | dnf : List (Clause n) → Layered n
  | cnf : List (Clause n) → Layered n
  | gAnd : List (Layered n) → Layered n
  | gOr : List (Layered n) → Layered n

namespace Layered

variable {n : ℕ}

mutual
/-- Faithful realisation as an `ACircuit` (mutual with the list version to recurse through children). -/
def toCircuit : Layered n → ACircuit n
  | dnf cs => dnfToCircuit cs
  | cnf cs => cnfToCircuit cs
  | gAnd gs => ACircuit.and (toCircuitList gs)
  | gOr gs => ACircuit.or (toCircuitList gs)
def toCircuitList : List (Layered n) → List (ACircuit n)
  | [] => []
  | g :: gs => toCircuit g :: toCircuitList gs
end

/-- Boolean semantics, inherited from the `ACircuit` realisation. -/
def eval (L : Layered n) (x : Fin n → Bool) : Bool := (toCircuit L).eval x

mutual
/-- The alternation depth: a bottom gate counts as `2` (an `OR`/`AND` of bounded gates over literals). -/
def depth : Layered n → ℕ
  | dnf _ => 2
  | cnf _ => 2
  | gAnd gs => depthList gs + 1
  | gOr gs => depthList gs + 1
def depthList : List (Layered n) → ℕ
  | [] => 0
  | g :: gs => max (depth g) (depthList gs)
end

/-- `toCircuitList` is the pointwise `toCircuit` map. -/
theorem toCircuitList_eq (gs : List (Layered n)) : toCircuitList gs = gs.map toCircuit := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [toCircuitList, List.map_cons, ih]

@[simp] theorem eval_dnf (cs : List (Clause n)) (x : Fin n → Bool) :
    eval (dnf cs) x = DTree.dnfValue cs x := by
  simp only [eval, toCircuit]; exact dnfToCircuit_eval cs x

@[simp] theorem eval_cnf (cs : List (Clause n)) (x : Fin n → Bool) :
    eval (cnf cs) x = cnfValue cs x := by
  simp only [eval, toCircuit]; exact cnfToCircuit_eval cs x

@[simp] theorem eval_gAnd (gs : List (Layered n)) (x : Fin n → Bool) :
    eval (gAnd gs) x = gs.all (fun g => eval g x) := by
  simp only [eval, toCircuit, ACircuit.eval_and, toCircuitList_eq, List.all_map, Function.comp_def]

@[simp] theorem eval_gOr (gs : List (Layered n)) (x : Fin n → Bool) :
    eval (gOr gs) x = gs.any (fun g => eval g x) := by
  simp only [eval, toCircuit, ACircuit.eval_or, toCircuitList_eq, List.any_map, Function.comp_def]

theorem depth_dnf (cs : List (Clause n)) : depth (dnf cs) = 2 := rfl
theorem depth_cnf (cs : List (Clause n)) : depth (cnf cs) = 2 := rfl
theorem depth_gAnd (gs : List (Layered n)) : depth (gAnd gs) = depthList gs + 1 := rfl
theorem depth_gOr (gs : List (Layered n)) : depth (gOr gs) = depthList gs + 1 := rfl

/-- A tower of bottom `DNF`s has child-depth `≤ 2`, so the `AND` above it has depth `≤ 3`. -/
theorem depthList_map_dnf_le (gs : List (List (Clause n))) : depthList (gs.map dnf) ≤ 2 := by
  induction gs with
  | nil => simp [depthList]
  | cons g gs ih => simp only [List.map_cons, depthList, depth_dnf]; omega

/-- The dual: a tower of bottom `CNF`s has child-depth `≤ 2`. -/
theorem depthList_map_cnf_le (gs : List (List (Clause n))) : depthList (gs.map cnf) ≤ 2 := by
  induction gs with
  | nil => simp [depthList]
  | cons g gs ih => simp only [List.map_cons, depthList, depth_cnf]; omega

/-- Equivalence of two layered circuits on a `ρ`-subcube. -/
def EquivOn (ρ : Fin n → Option Bool) (C C' : Layered n) : Prop :=
  ∀ x, DTree.agreeRestriction ρ x → eval C x = eval C' x

private theorem all_map_eval (f : Layered n → Layered n) (gs : List (Layered n)) (x : Fin n → Bool)
    (h : ∀ g ∈ gs, eval g x = eval (f g) x) :
    gs.all (fun g => eval g x) = (gs.map f).all (fun g => eval g x) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, List.all_cons, List.all_cons, h g (List.mem_cons_self ..),
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

private theorem any_map_eval (f : Layered n → Layered n) (gs : List (Layered n)) (x : Fin n → Bool)
    (h : ∀ g ∈ gs, eval g x = eval (f g) x) :
    gs.any (fun g => eval g x) = (gs.map f).any (fun g => eval g x) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, List.any_cons, List.any_cons, h g (List.mem_cons_self ..),
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

/-- **Iteration glue (`AND`).**  Collapsing every child on a common subcube collapses the `AND`. -/
theorem gAnd_map_EquivOn {ρ : Fin n → Option Bool} (f : Layered n → Layered n)
    (gs : List (Layered n)) (h : ∀ g ∈ gs, EquivOn ρ g (f g)) :
    EquivOn ρ (gAnd gs) (gAnd (gs.map f)) := by
  intro x hx
  rw [eval_gAnd, eval_gAnd]
  exact all_map_eval f gs x (fun g hg => h g hg x hx)

/-- **Iteration glue (`OR`).**  Collapsing every child on a common subcube collapses the `OR`. -/
theorem gOr_map_EquivOn {ρ : Fin n → Option Bool} (f : Layered n → Layered n)
    (gs : List (Layered n)) (h : ∀ g ∈ gs, EquivOn ρ g (f g)) :
    EquivOn ρ (gOr gs) (gOr (gs.map f)) := by
  intro x hx
  rw [eval_gOr, eval_gOr]
  exact any_map_eval f gs x (fun g hg => h g hg x hx)

/-- **The `AND`-bottom collapse step.**  An `AND` of bottom `DNF` gates collapses, under the union-bound
restriction, to a single bottom `CNF` of width `< s` — `single_round_collapse` in layered terms. -/
theorem collapse_gAnd {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ) (hF : n < F)
    (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hsmall : (G.card : ℚ)
        * ((2 * p / (1 - p)) ^ s
            * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1) :
    ∃ ρ : Fin n → Option Bool, ∃ c : List (Clause n),
      EquivOn ρ (gAnd (G.toList.map dnf)) (cnf c) ∧ (∀ C ∈ c, C.lits.length < s) := by
  obtain ⟨ρ, c, hequiv, hwidth⟩ := single_round_collapse hp0 hp3 w F s hF G hcons hnd hw hsmall
  refine ⟨ρ, c, ?_, hwidth⟩
  intro x hx
  have hlhs : eval (gAnd (G.toList.map dnf)) x
      = (ACircuit.and (G.toList.map dnfToCircuit)).eval x := by
    simp only [eval, toCircuit, toCircuitList_eq, List.map_map]; rfl
  have hrhs : eval (cnf c) x = cnfValue c x := by
    simp only [eval, toCircuit]; exact cnfToCircuit_eval c x
  rw [hlhs, hrhs]; exact (hequiv x hx).symm

/-- **The `OR`-bottom collapse step (dual).**  An `OR` of bottom `CNF` gates collapses to a single bottom
`DNF` of width `< s` — `single_round_collapse_or` in layered terms. -/
theorem collapse_gOr {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ) (hF : n < F)
    (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ C ∈ g, Consistent C)
    (hnd : ∀ g ∈ G, ∀ C ∈ g, (C.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ C ∈ g, C.lits.length ≤ w)
    (hsmall : (G.card : ℚ)
        * ((2 * p / (1 - p)) ^ s
            * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1) :
    ∃ ρ : Fin n → Option Bool, ∃ d : List (Clause n),
      EquivOn ρ (gOr (G.toList.map cnf)) (dnf d) ∧ (∀ T ∈ d, T.lits.length < s) := by
  obtain ⟨ρ, d, hequiv, hwidth⟩ := single_round_collapse_or hp0 hp3 w F s hF G hcons hnd hw hsmall
  refine ⟨ρ, d, ?_, hwidth⟩
  intro x hx
  have hlhs : eval (gOr (G.toList.map cnf)) x
      = (ACircuit.or (G.toList.map cnfToCircuit)).eval x := by
    simp only [eval, toCircuit, toCircuitList_eq, List.map_map]; rfl
  have hrhs : eval (dnf d) x = DTree.dnfValue d x := by
    simp only [eval, toCircuit]; exact dnfToCircuit_eval d x
  rw [hlhs, hrhs]; exact (hequiv x hx).symm

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_gAnd
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_gOr
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.gAnd_map_EquivOn
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.gOr_map_EquivOn
