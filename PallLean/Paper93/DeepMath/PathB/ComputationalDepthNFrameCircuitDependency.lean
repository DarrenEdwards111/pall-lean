import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTreeDAGWall

/-!
# N-Frame: opening the size wall — the dependency bound and the first circuit lower bound for SAT

`sat3Target` needs size-specific, sharing-aware methods (W2).  This file opens that wall with its baseline
technique — **dependency counting**, the degenerate case of gate elimination: a circuit computing `f` must contain
a `var i` gate for every variable `f` depends on, because a circuit with no `var i` gate computes a function
independent of `x i`.

  `runFrom_indep` / `output_indep` — **PROVED**: circuits without a `var i` gate ignore coordinate `i`.
  `depends_var_mem` — **PROVED, the method**: a 1/0-pair differing only at `i` forces a `var i` gate.
  `sat3_cbudget_lb` — **PROVED, the first circuit-size lower bound for the SAT target**:
        `sat3M N · sat3V N ≤ cbudget (sat3Family N)` — every circuit computing the definite SAT family has
        `≥ m·v ≈ N/3` gates (the selector-forcing pairs witness `m·v` relevant variables).
  `sat3_budget_lb_improved` — **PROVED**: the same bound for trees, numerically *stronger* than the Nečiporuk
        `m(m−2)/4 ≈ N/36` — the dependency method beats subfunction counting on this layout's constants.

## Honest scope

Linear is the baseline, and for general circuits it is also — scandalously — near the classical state of the art
(general `cbudget` lower bounds stall at small-constant·n; the best known use gate elimination, the non-degenerate
extension of this file's method).  The wall W2 is *entered*, not scaled: superpolynomial `cbudget` remains the open
frontier, now with the correct first tool formalized and calibrated on the true target.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Circuits without a variable's gate ignore it -/

theorem evalGate_indep {n : ℕ} (x x' : Fin n → Bool) (vals : List Bool) (g : CGate n)
    (hg : ∀ j, g = CGate.var j → x j = x' j) :
    evalGate x vals g = evalGate x' vals g := by
  cases g with
  | var j => exact hg j rfl
  | cst b => rfl
  | un op k => rfl
  | bin op k l => rfl

theorem runFrom_indep {n : ℕ} (x x' : Fin n → Bool) (c : List (CGate n))
    (hc : ∀ j, CGate.var j ∈ c → x j = x' j) :
    ∀ vals, runFrom x vals c = runFrom x' vals c := by
  induction c with
  | nil => intro vals; rfl
  | cons g gs ih =>
    intro vals
    show runFrom x (vals ++ [evalGate x vals g]) gs
        = runFrom x' (vals ++ [evalGate x' vals g]) gs
    rw [evalGate_indep x x' vals g (fun j hj => hc j (by
      rw [← hj] at *
      exact List.mem_cons_self))]
    exact ih (fun j hj => hc j (List.mem_cons_of_mem g hj)) _

/-- **The dependency method (proved)**: a 1/0-pair differing only at `i` forces a `var i` gate into every circuit
computing the function. -/
theorem depends_var_mem {n : ℕ} (c : List (CGate n)) (f : (Fin n → Bool) → Bool)
    (hcomp : computes c f) (i : Fin n) (x₁ x₀ : Fin n → Bool)
    (hdiff : ∀ b : Fin n, x₁ b ≠ x₀ b → b = i) (hne : f x₁ ≠ f x₀) :
    CGate.var i ∈ c := by
  by_contra hmem
  apply hne
  rw [← hcomp x₁, ← hcomp x₀]
  show (runFrom x₁ [] c).getD (c.length - 1) false
      = (runFrom x₀ [] c).getD (c.length - 1) false
  rw [runFrom_indep x₁ x₀ c (fun j hj => ?_) []]
  by_cases hji : x₁ j = x₀ j
  · exact hji
  · exact absurd (hdiff j hji ▸ hj) hmem

/-! ### Counting the forced gates -/

/-- The variables read by the circuit. -/
def circuitVars {n : ℕ} (c : List (CGate n)) : Finset (Fin n) :=
  (c.filterMap (fun g => match g with
    | CGate.var i => some i
    | _ => none)).toFinset

theorem mem_circuitVars_of {n : ℕ} (c : List (CGate n)) (i : Fin n)
    (h : CGate.var i ∈ c) : i ∈ circuitVars c := by
  unfold circuitVars
  rw [List.mem_toFinset, List.mem_filterMap]
  exact ⟨CGate.var i, h, rfl⟩

theorem circuitVars_card_le {n : ℕ} (c : List (CGate n)) :
    (circuitVars c).card ≤ c.length :=
  le_trans (List.toFinset_card_le _) (List.length_filterMap_le _ _)

/-! ### The first circuit lower bound for the SAT target -/

/-- **THE FIRST CIRCUIT-SIZE LOWER BOUND FOR SAT (proved)**: every circuit computing the definite SAT family has
at least `m·v ≈ N/3` gates — the selector-forcing pairs witness `m·v` relevant variables, each demanding its own
`var` gate. -/
theorem sat3_cbudget_lb (N : ℕ) (hv : 1 ≤ sat3V N) :
    sat3M N * sat3V N ≤ cbudget (sat3Family N) := by
  have hne : {s | ∃ c : List (CGate N), computes c (sat3Family N) ∧ c.length = s}.Nonempty := by
    refine ⟨(compile 0 (dnfFor (sat3Family N))).length, compile 0 (dnfFor (sat3Family N)), ?_, rfl⟩
    have := compile_computes (dnfFor (sat3Family N))
    rwa [show (fun x => eval (dnfFor (sat3Family N)) x) = sat3Family N from
      funext (fun x => by rw [eval_dnfFor])] at this
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem hne
  rw [show cbudget (sat3Family N)
      = sInf {s | ∃ c : List (CGate N), computes c (sat3Family N) ∧ c.length = s} from rfl,
    ← hlen]
  -- every selector bit's gate is forced
  have hmem : ∀ cj : Fin (sat3M N) × Fin (sat3V N),
      CGate.var (sat3Bit N cj.1 ⟨0, by omega⟩ cj.2.val (by have := cj.2.isLt; omega)) ∈ c := by
    intro cj
    obtain ⟨x₁, x₀, h1, h0, hforce⟩ := sat3_selector_pair N hv cj.1 cj.2
    exact depends_var_mem c (sat3Family N) hcomp _ x₁ x₀ hforce (by
      rw [h1, h0]
      decide)
  -- the forced gates are pairwise distinct variables
  have hinj : Function.Injective (fun cj : Fin (sat3M N) × Fin (sat3V N) =>
      sat3Bit N cj.1 ⟨0, by omega⟩ cj.2.val (by have := cj.2.isLt; omega)) := by
    intro a b h
    have hr1 : (sat3Bit N a.1 ⟨0, by omega⟩ a.2.val
        (by have := a.2.isLt; omega)).val % sat3D N = a.2.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + a.2.val = a.2.val
      omega
    have hr2 : (sat3Bit N b.1 ⟨0, by omega⟩ b.2.val
        (by have := b.2.isLt; omega)).val % sat3D N = b.2.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + b.2.val = b.2.val
      omega
    have hdiv : a.1.val = b.1.val := by
      rw [← sat3Bit_clause N a.1 ⟨0, by omega⟩ a.2.val (by have := a.2.isLt; omega),
        ← sat3Bit_clause N b.1 ⟨0, by omega⟩ b.2.val (by have := b.2.isLt; omega)]
      exact congrArg (fun bit : Fin N => bit.val / sat3D N) h
    have hrem : a.2.val = b.2.val := by
      rw [← hr1, ← hr2]
      exact congrArg (fun bit : Fin N => bit.val % sat3D N) h
    exact Prod.ext (Fin.ext hdiv) (Fin.ext hrem)
  have hsub : Finset.univ.image (fun cj : Fin (sat3M N) × Fin (sat3V N) =>
      sat3Bit N cj.1 ⟨0, by omega⟩ cj.2.val (by have := cj.2.isLt; omega))
      ⊆ circuitVars c := by
    intro i hi
    obtain ⟨cj, -, rfl⟩ := Finset.mem_image.mp hi
    exact mem_circuitVars_of c _ (hmem cj)
  have hcard : sat3M N * sat3V N ≤ (circuitVars c).card := by
    have himg : (Finset.univ.image (fun cj : Fin (sat3M N) × Fin (sat3V N) =>
        sat3Bit N cj.1 ⟨0, by omega⟩ cj.2.val (by have := cj.2.isLt; omega))).card
        = sat3M N * sat3V N := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin]
    rw [← himg]
    exact Finset.card_le_card hsub
  exact le_trans hcard (circuitVars_card_le c)

/-- **The improved tree bound (proved)**: `m·v ≈ N/3 ≤ budget (sat3Family N)` — the dependency method beats the
Nečiporuk `m(m−2)/4 ≈ N/36` on this layout's constants. -/
theorem sat3_budget_lb_improved (N : ℕ) (hv : 1 ≤ sat3V N) :
    sat3M N * sat3V N ≤ budget (sat3Family N) :=
  le_trans (sat3_cbudget_lb N hv) (cbudget_le_budget (sat3Family N))

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.depends_var_mem
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_lb
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_budget_lb_improved
