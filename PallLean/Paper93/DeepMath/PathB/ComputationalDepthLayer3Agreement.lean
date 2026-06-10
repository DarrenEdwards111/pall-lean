import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pApprox
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Averaging

/-!
# Layer 3 — recursive agreement lift (OR/NOT/leaf fragment)

The per-gate agreement steps (`genOrApprox_eval_orOfChildren`, `one_sub_boolToZMod`) are lifted through
the circuit recursion here.  We build a **faithful** OR/NOT/leaf approximant `toAgree` (single-function,
`termination_by sizeOf`, so children are indexed cleanly by `Fin cs.length`), a per-input **goodness**
predicate `AgreeGood` (at each `∨` gate: when the gate is true, some sampled form over the children's
true values is nonzero), and prove by structural induction:
\[
  \text{AgreeGood } x\,R\,C \;\Longrightarrow\;
  \operatorname{eval}_x(\texttt{toAgree}\,C) = \texttt{boolToZMod}\,(C.\operatorname{eval} x).
\]
i.e. the circuit approximant computes the circuit exactly on every *good* input.  `AND`/`MOD` gates are
excluded from this fragment (`AgreeGood` is `False` there); handling them (De Morgan / Fermat) and the
probabilistic "most inputs are good" step are the remaining pieces.  No lower bound; far below P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open MvPolynomial

variable {n : ℕ}

/-- Faithful OR/NOT/leaf circuit approximant: `∨` → `genOrApprox` over children, `¬` → `1 - child`,
leaves → `X i`/`C b`; `AND`/`MOD` are placeholders (excluded by `AgreeGood`). -/
noncomputable def toAgree (p t : ℕ) (R : (k : ℕ) → Fin t → Fin k → ZMod p) :
    BoolCircuitSyntax n → MvPolynomial (Fin n) (ZMod p)
  | .const b => C (boolToZMod p b)
  | .input i => X i
  | .not c => 1 - toAgree p t R c
  | .orGate cs => genOrApprox p (R cs.length) (fun j => toAgree p t R (cs.get j))
  | .andGate cs => 1 - genOrApprox p (R cs.length) (fun j => 1 - toAgree p t R (cs.get j))
  | .modGate _ r cs =>
      1 - ((∑ j : Fin cs.length, toAgree p t R (cs.get j)) - C (r : ZMod p)) ^ (p - 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact lt_of_lt_of_le (List.sizeOf_lt_of_mem (List.getElem_mem _)) (by omega)

/-- Per-input goodness: children good, and at each `∨` gate, when the gate evaluates to `true` some
sampled form over the children's *true* values is nonzero (so the OR approximant fires correctly). -/
def AgreeGood (p t : ℕ) (R : (k : ℕ) → Fin t → Fin k → ZMod p) (x : Fin n → Bool) :
    BoolCircuitSyntax n → Prop
  | .const _ => True
  | .input _ => True
  | .not c => AgreeGood p t R x c
  | .orGate cs => (∀ j : Fin cs.length, AgreeGood p t R x (cs.get j)) ∧
      ((∃ j : Fin cs.length, (cs.get j).eval x = true) →
        ∃ s, ∑ j, R cs.length s j * boolToZMod p ((cs.get j).eval x) ≠ 0)
  | .andGate cs => (∀ j : Fin cs.length, AgreeGood p t R x (cs.get j)) ∧
      ((∃ j : Fin cs.length, (!(cs.get j).eval x) = true) →
        ∃ s, ∑ j, R cs.length s j * boolToZMod p (!(cs.get j).eval x) ≠ 0)
  | .modGate q _ cs => (∀ j : Fin cs.length, AgreeGood p t R x (cs.get j)) ∧ q = p
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact lt_of_lt_of_le (List.sizeOf_lt_of_mem (List.getElem_mem _)) (by omega)

/-- **OR-gate evaluation ↔ some child true** (`.any` ↔ indexed existential). -/
theorem orGate_eval_iff (cs : List (BoolCircuitSyntax n)) (x : Fin n → Bool) :
    (BoolCircuitSyntax.orGate cs).eval x = true ↔ ∃ j : Fin cs.length, (cs.get j).eval x = true := by
  simp only [BoolCircuitSyntax.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨b, ⟨c, hc, rfl⟩, hb⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc
    exact ⟨j, by rw [hj]; exact hb⟩
  · rintro ⟨j, hj⟩
    exact ⟨(cs.get j).eval x, ⟨cs.get j, List.get_mem cs j, rfl⟩, hj⟩

/-- **AND-gate evaluation ↔ all children true** (`.all` ↔ indexed universal). -/
theorem andGate_eval_iff (cs : List (BoolCircuitSyntax n)) (x : Fin n → Bool) :
    (BoolCircuitSyntax.andGate cs).eval x = true ↔ ∀ j : Fin cs.length, (cs.get j).eval x = true := by
  simp only [BoolCircuitSyntax.eval, List.all_eq_true, List.mem_map, id_eq]
  constructor
  · intro h j; exact h _ ⟨cs.get j, List.get_mem cs j, rfl⟩
  · rintro h b ⟨c, hc, rfl⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc
    rw [← hj]; exact h j

/-- **Modular count.**  Summing `boolToZMod` of a Boolean-valued function over a list's indices equals
the number of `true` entries (cast to `ZMod p`) — the bridge for the `MOD` gate's Fermat indicator. -/
theorem sum_boolToZMod_get {α : Type*} (p : ℕ) (f : α → Bool) : ∀ (cs : List α),
    (∑ j : Fin cs.length, boolToZMod p (f (cs.get j))) = (((cs.map f).filter id).length : ZMod p)
  | [] => by simp
  | c :: cs => by
      show (∑ j : Fin (cs.length + 1), boolToZMod p (f ((c :: cs).get j))) = _
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero, List.get_cons_succ', List.map_cons, List.filter_cons]
      rw [sum_boolToZMod_get p f cs]
      cases f c <;> simp [boolToZMod] <;> push_cast <;> ring

/-- **The recursive agreement lift.**  On any *good* input, the OR/NOT/leaf circuit approximant
evaluates to the true circuit value. -/
theorem toAgree_eval (p t : ℕ) [Fact p.Prime] (R : (k : ℕ) → Fin t → Fin k → ZMod p)
    (x : Fin n → Bool) :
    ∀ (C : BoolCircuitSyntax n), AgreeGood p t R x C →
      eval (fun i => boolToZMod p (x i)) (toAgree p t R C) = boolToZMod p (C.eval x)
  | .const b, _ => by simp [toAgree, BoolCircuitSyntax.eval]
  | .input i, _ => by simp [toAgree, BoolCircuitSyntax.eval]
  | .not c, hg => by
      simp only [AgreeGood] at hg
      simp only [toAgree, map_sub, map_one]
      rw [toAgree_eval p t R x c hg, one_sub_boolToZMod]
      simp only [BoolCircuitSyntax.eval]
  | .orGate cs, hg => by
      simp only [AgreeGood] at hg
      obtain ⟨hchildren, hgood⟩ := hg
      simp only [toAgree]
      rw [genOrApprox_eval_orOfChildren p (R cs.length) (fun j => toAgree p t R (cs.get j))
        (fun i => boolToZMod p (x i)) (fun j => (cs.get j).eval x)
        (fun j => toAgree_eval p t R x (cs.get j) (hchildren j)) hgood]
      by_cases hev : (BoolCircuitSyntax.orGate cs).eval x = true
      · rw [if_pos ((orGate_eval_iff cs x).mp hev), hev]
        exact (boolToZMod_true p).symm
      · have hne : ¬ ∃ j : Fin cs.length, (cs.get j).eval x = true :=
          fun h => hev ((orGate_eval_iff cs x).mpr h)
        rw [Bool.not_eq_true] at hev
        rw [if_neg hne, hev]
        exact (boolToZMod_false p).symm
  | .andGate cs, hg => by
      simp only [AgreeGood] at hg
      obtain ⟨hchildren, hgood⟩ := hg
      simp only [toAgree, map_sub, map_one]
      rw [genOrApprox_eval_orOfChildren p (R cs.length) (fun j => 1 - toAgree p t R (cs.get j))
        (fun i => boolToZMod p (x i)) (fun j => !(cs.get j).eval x)
        (fun j => by
          simp only [map_sub, map_one]
          rw [toAgree_eval p t R x (cs.get j) (hchildren j)]
          exact one_sub_boolToZMod p _) hgood]
      have hexists_iff : (∃ j : Fin cs.length, (!(cs.get j).eval x) = true)
          ↔ (BoolCircuitSyntax.andGate cs).eval x = false := by
        rw [← Bool.not_eq_true, andGate_eval_iff, not_forall]
        exact exists_congr fun j => by cases (cs.get j).eval x <;> simp
      by_cases hev : (BoolCircuitSyntax.andGate cs).eval x = true
      · rw [if_neg (show ¬ ∃ j : Fin cs.length, (!(cs.get j).eval x) = true by
          rw [hexists_iff, hev]; simp), hev]
        simp [boolToZMod]
      · rw [Bool.not_eq_true] at hev
        rw [if_pos (hexists_iff.mpr hev), hev]
        simp [boolToZMod]
  | .modGate q r cs, hg => by
      simp only [AgreeGood] at hg
      obtain ⟨hchildren, hqp⟩ := hg
      have hp1 : p - 1 ≠ 0 := by have := (Fact.out (p := p.Prime)).two_le; omega
      have hsum : (∑ j : Fin cs.length, eval (fun i => boolToZMod p (x i)) (toAgree p t R (cs.get j)))
          = ∑ j : Fin cs.length, boolToZMod p ((cs.get j).eval x) :=
        Finset.sum_congr rfl (fun j _ => toAgree_eval p t R x (cs.get j) (hchildren j))
      simp only [toAgree, map_sub, map_one, map_pow, map_sum, eval_C, BoolCircuitSyntax.eval]
      rw [hqp, hsum, sum_boolToZMod_get p (fun C => C.eval x) cs]
      generalize ((cs.map (fun C => C.eval x)).filter id).length = N
      by_cases hmod : (N : ZMod p) = (r : ZMod p)
      · rw [show ((N : ZMod p) - (r : ZMod p)) = 0 from by rw [hmod, sub_self],
          zero_pow hp1, sub_zero]
        have hd : decide (N % p = r % p) = true := by
          simp [(ZMod.natCast_eq_natCast_iff' N r p).mp hmod]
        rw [hd, boolToZMod_true]
      · rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr hmod), sub_self]
        have hd : decide (N % p = r % p) = false := by
          simp only [decide_eq_false_iff_not]
          exact fun h => hmod ((ZMod.natCast_eq_natCast_iff' N r p).mpr h)
        rw [hd, boolToZMod_false]
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact lt_of_lt_of_le (List.sizeOf_lt_of_mem (List.getElem_mem _)) (by omega)

/-! ## Composed error ⊆ goodness failure (the `hsub` ingredient)

The contrapositive of `toAgree_eval`: wherever the circuit approximant *errs*, the goodness predicate
*fails*.  So the composed error set is contained in `{x : ¬ AgreeGood x R C}` — the containment the
circuit-level averaging (`exists_form_total_errors`) consumes as `hsub`.  (Decomposing `¬AgreeGood`
further into a union over independently-formed gates needs a per-gate-indexed form space — the remaining
architectural step beyond the shared-fan-in oracle used here.) -/

/-- **Agreement contrapositive.**  If the approximant errs at `x`, the goodness predicate fails there. -/
theorem toAgree_bad_imp_not_good (p t : ℕ) [Fact p.Prime]
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) (x : Fin n → Bool) (C : BoolCircuitSyntax n) :
    eval (fun i => boolToZMod p (x i)) (toAgree p t R C) ≠ boolToZMod p (C.eval x) →
      ¬ AgreeGood p t R x C :=
  fun hne hg => hne (toAgree_eval p t R x C hg)

open Classical in
/-- **Composed error set ⊆ goodness-failure set.**  The `hsub`-style containment for the whole circuit
approximant. -/
theorem toAgree_cbad_subset (p t : ℕ) [Fact p.Prime]
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) (C : BoolCircuitSyntax n) :
    Finset.univ.filter (fun x : Fin n → Bool =>
        eval (fun i => boolToZMod p (x i)) (toAgree p t R C) ≠ boolToZMod p (C.eval x))
      ⊆ Finset.univ.filter (fun x : Fin n → Bool => ¬ AgreeGood p t R x C) := by
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, toAgree_bad_imp_not_good p t R x C hx.2⟩

/-! ## Decomposing goodness into per-gate local conditions

`AgreeGood` is, by its recursion, the conjunction of a *local* goodness condition at every subcircuit.
Making this explicit (`subcircuits` enumerates them, `localGood` is the per-gate condition) lets the
composed-error containment `cbad ⊆ {¬AgreeGood}` become `cbad ⊆ ⋃_{gate} {¬localGood gate}` — the
union-over-gates shape the circuit averaging consumes.  (Each gate's `localGood` depends only on its
fan-in's form coordinate, so `sum_proj_eq` factors the column sums; no per-gate independence is needed
— linearity of expectation suffices.) -/

/-! All subcircuits of a circuit (itself plus, recursively, its children's). -/
mutual
def subcircuits {n : ℕ} : BoolCircuitSyntax n → List (BoolCircuitSyntax n)
  | .const b => [.const b]
  | .input i => [.input i]
  | .not c => .not c :: subcircuits c
  | .orGate cs => .orGate cs :: subcircuitsList cs
  | .andGate cs => .andGate cs :: subcircuitsList cs
  | .modGate q r cs => .modGate q r cs :: subcircuitsList cs
def subcircuitsList {n : ℕ} : List (BoolCircuitSyntax n) → List (BoolCircuitSyntax n)
  | [] => []
  | c :: cs => subcircuits c ++ subcircuitsList cs
end

/-- The gate-local goodness condition at a single subcircuit (the form condition at `∨`/`∧` gates,
`q = p` at `MOD` gates, trivial otherwise). -/
def localGood (p t : ℕ) (R : (k : ℕ) → Fin t → Fin k → ZMod p) (x : Fin n → Bool) :
    BoolCircuitSyntax n → Prop
  | .orGate cs => (∃ j : Fin cs.length, (cs.get j).eval x = true) →
      ∃ s, ∑ j, R cs.length s j * boolToZMod p ((cs.get j).eval x) ≠ 0
  | .andGate cs => (∃ j : Fin cs.length, (!(cs.get j).eval x) = true) →
      ∃ s, ∑ j, R cs.length s j * boolToZMod p (!(cs.get j).eval x) ≠ 0
  | .modGate q _ _ => q = p
  | _ => True

/-- A subcircuit of a list member is a subcircuit of the list. -/
theorem mem_subcircuitsList {n : ℕ} (c : BoolCircuitSyntax n) :
    ∀ (cs : List (BoolCircuitSyntax n)), c ∈ cs → ∀ G, G ∈ subcircuits c → G ∈ subcircuitsList cs
  | [], hc, _, _ => absurd hc (by simp)
  | c0 :: cs, hc, G, hG => by
      simp only [subcircuitsList]
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact List.mem_append_left _ hG
      · exact List.mem_append_right _ (mem_subcircuitsList c cs hmem G hG)

/-- **Goodness from per-gate local conditions.**  If every subcircuit satisfies its local goodness, the
whole circuit is good — the `⟸` half of the decomposition (the direction `hsub` needs). -/
theorem agreeGood_of_forall (p t : ℕ) [Fact p.Prime] (R : (k : ℕ) → Fin t → Fin k → ZMod p)
    (x : Fin n → Bool) :
    ∀ (C : BoolCircuitSyntax n), (∀ G ∈ subcircuits C, localGood p t R x G) → AgreeGood p t R x C
  | .const _, _ => by simp only [AgreeGood]
  | .input _, _ => by simp only [AgreeGood]
  | .not c, h => by
      simp only [AgreeGood]
      exact agreeGood_of_forall p t R x c
        (fun G hG => h G (by simp only [subcircuits]; exact List.mem_cons_of_mem _ hG))
  | .orGate cs, h => by
      simp only [AgreeGood]
      refine ⟨fun j => agreeGood_of_forall p t R x (cs.get j) (fun G hG => h G ?_), ?_⟩
      · simp only [subcircuits]
        exact List.mem_cons_of_mem _ (mem_subcircuitsList (cs.get j) cs (List.get_mem cs j) G hG)
      · have := h (.orGate cs) (by simp only [subcircuits]; exact List.mem_cons_self ..)
        simpa only [localGood] using this
  | .andGate cs, h => by
      simp only [AgreeGood]
      refine ⟨fun j => agreeGood_of_forall p t R x (cs.get j) (fun G hG => h G ?_), ?_⟩
      · simp only [subcircuits]
        exact List.mem_cons_of_mem _ (mem_subcircuitsList (cs.get j) cs (List.get_mem cs j) G hG)
      · have := h (.andGate cs) (by simp only [subcircuits]; exact List.mem_cons_self ..)
        simpa only [localGood] using this
  | .modGate q r cs, h => by
      simp only [AgreeGood]
      refine ⟨fun j => agreeGood_of_forall p t R x (cs.get j) (fun G hG => h G ?_), ?_⟩
      · simp only [subcircuits]
        exact List.mem_cons_of_mem _ (mem_subcircuitsList (cs.get j) cs (List.get_mem cs j) G hG)
      · have := h (.modGate q r cs) (by simp only [subcircuits]; exact List.mem_cons_self ..)
        simpa only [localGood] using this
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact lt_of_lt_of_le (List.sizeOf_lt_of_mem (List.getElem_mem _)) (by omega)

open Classical in
/-- **`hsub` over gates.**  The composed-error set is contained in the union, over the circuit's gates,
of the per-gate local-goodness failures: `cbad ⊆ ⋃_{G ∈ subcircuits C} {x : ¬ localGood G x}`.  This is
exactly the `hsub` hypothesis of `exists_form_total_errors`, with `gbad G = {x : ¬ localGood G x}` and
gates `= (subcircuits C).toFinset`. -/
theorem cbad_subset_gates (p t : ℕ) [Fact p.Prime]
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) (C : BoolCircuitSyntax n) :
    Finset.univ.filter (fun x : Fin n → Bool =>
        eval (fun i => boolToZMod p (x i)) (toAgree p t R C) ≠ boolToZMod p (C.eval x))
      ⊆ (subcircuits C).toFinset.biUnion (fun G =>
          Finset.univ.filter (fun x : Fin n → Bool => ¬ localGood p t R x G)) := by
  intro x hx
  rw [Finset.mem_filter] at hx
  have hng : ¬ AgreeGood p t R x C := toAgree_bad_imp_not_good p t R x C hx.2
  have hex : ∃ G ∈ subcircuits C, ¬ localGood p t R x G := by
    by_contra hcon
    push_neg at hcon
    exact hng (agreeGood_of_forall p t R x C hcon)
  obtain ⟨G, hG, hnG⟩ := hex
  rw [Finset.mem_biUnion]
  exact ⟨G, List.mem_toFinset.mpr hG, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hnG⟩⟩

/-- **Per-coordinate local-failure count.**  For a gate of fan-in `m` and a fixed input (giving children
values `v`), the number of the gate's own form choices `ρ : Fin t → Fin m → ZMod p` at which local
goodness fails is `≤ (p^{m-1})^t`: equality when some child is true (the kernel count
`orApprox_error_count` over the children-value vector `v`), and `0` when all children are false. -/
theorem localGood_fail_count (p : ℕ) [Fact p.Prime] {m t : ℕ} (v : Fin m → Bool) :
    (Finset.univ.filter (fun ρ : Fin t → Fin m → ZMod p =>
        (∃ j, v j = true) ∧ (∀ s, ∑ j, ρ s j * boolToZMod p (v j) = 0))).card
      ≤ (p ^ (m - 1)) ^ t := by
  classical
  by_cases hv : ∃ j, v j = true
  · rw [show (Finset.univ.filter (fun ρ : Fin t → Fin m → ZMod p =>
          (∃ j, v j = true) ∧ (∀ s, ∑ j, ρ s j * boolToZMod p (v j) = 0)))
          = Finset.univ.filter (fun ρ : Fin t → Fin m → ZMod p =>
              ∀ s, ∑ j, ρ s j * boolToZMod p (v j) = 0) from by
        apply Finset.filter_congr; intro ρ _; simp only [hv, true_and]]
    exact le_of_eq (orApprox_error_count p v hv)
  · rw [show (Finset.univ.filter (fun ρ : Fin t → Fin m → ZMod p =>
          (∃ j, v j = true) ∧ (∀ s, ∑ j, ρ s j * boolToZMod p (v j) = 0))) = ∅ from by
        rw [Finset.filter_eq_empty_iff]; intro ρ _; simp only [hv, false_and, not_false_iff]]
    simp

/-! ## Fan-in enumeration (the `Φ`-index for the averaging instantiation)

The joint form space `Φ` is indexed by the gate fan-ins occurring in the circuit.  `gateFanin` reads a
gate's fan-in (`0` at non-gates), `fanins C` collects them, and `gateFanin_mem_fanins` confirms every
subcircuit's fan-in is indexed — the membership the coordinate extraction (`oracleOf ω k = ω ⟨k,_⟩`)
relies on. -/

/-- A gate's fan-in (number of children); `0` at leaves/`¬`. -/
def gateFanin {n : ℕ} : BoolCircuitSyntax n → ℕ
  | .orGate cs => cs.length
  | .andGate cs => cs.length
  | .modGate _ _ cs => cs.length
  | _ => 0

/-- The finite set of gate fan-ins occurring in a circuit (the `Φ`-index). -/
def fanins {n : ℕ} (C : BoolCircuitSyntax n) : Finset ℕ :=
  ((subcircuits C).map gateFanin).toFinset

/-- Every subcircuit's fan-in is indexed by `fanins C`. -/
theorem gateFanin_mem_fanins {n : ℕ} {C G : BoolCircuitSyntax n} (hG : G ∈ subcircuits C) :
    gateFanin G ∈ fanins C :=
  List.mem_toFinset.mpr (List.mem_map.mpr ⟨G, hG, rfl⟩)

/-- The **joint form space** of a circuit: an independent form tuple per occurring fan-in.  Finite (a
`Fintype`), the `Φ` of `exists_form_total_errors`. -/
abbrev FormSpace (p t : ℕ) {n : ℕ} (C : BoolCircuitSyntax n) : Type :=
  ∀ k : {k // k ∈ fanins C}, Fin t → Fin k.1 → ZMod p

/-- Extend a joint form choice to a full per-fan-in oracle (default `0` off the occurring fan-ins). -/
noncomputable def oracleOf (p t : ℕ) {n : ℕ} (C : BoolCircuitSyntax n) (ω : FormSpace p t C) :
    (k : ℕ) → Fin t → Fin k → ZMod p :=
  fun k => if h : k ∈ fanins C then ω ⟨k, h⟩ else fun _ _ => 0

/-- **Coordinate extraction.**  At an occurring fan-in `k`, the oracle reads exactly the `k`-coordinate
of the joint form choice. -/
theorem oracleOf_eq (p t : ℕ) {n : ℕ} (C : BoolCircuitSyntax n) (ω : FormSpace p t C)
    {k : ℕ} (h : k ∈ fanins C) :
    oracleOf p t C ω k = ω ⟨k, h⟩ :=
  dif_pos h

/-! **`hB` for an OR gate.**  Wiring coordinate extraction (`oracleOf_eq`) + `column_sum_le` +
`localGood_fail_count`: the column sum of an OR gate's local failures over the joint form space is
`≤ 2^n · (∏_{other coords}) · (p^{m-1})^t`.  The template for the `hB` hypothesis of
`exists_form_total_errors`.  (The per-input count is transported across the `Fintype`-instance gap
`A i₀` vs `Fin cs.length → …` via the `Fintype`/`DecidablePred` subsingleton.) -/
open Classical in
theorem gbad_or_column_sum (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n)
    (cs : List (BoolCircuitSyntax n)) (hmem : cs.length ∈ fanins C) :
    ∑ ω : FormSpace p t C,
        (Finset.univ.filter (fun x : Fin n → Bool =>
          ¬ localGood p t (oracleOf p t C ω) x (.orGate cs))).card
      ≤ Fintype.card (Fin n → Bool)
        * (∏ i ∈ Finset.univ.erase (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}),
            Fintype.card (Fin t → Fin i.1 → ZMod p))
        * (p ^ (cs.length - 1)) ^ t := by
  classical
  have hpred : ∀ (ω : FormSpace p t C),
      (Finset.univ.filter (fun x : Fin n → Bool =>
          ¬ localGood p t (oracleOf p t C ω) x (.orGate cs)))
        = Finset.univ.filter (fun x : Fin n → Bool =>
            (∃ j, (cs.get j).eval x = true) ∧
              ∀ s, ∑ j, ω ⟨cs.length, hmem⟩ s j * boolToZMod p ((cs.get j).eval x) = 0) := by
    intro ω
    apply Finset.filter_congr
    intro x _
    simp only [localGood, oracleOf_eq p t C ω hmem, not_forall, _root_.not_imp, not_exists,
      not_not, exists_prop]
  simp only [hpred, Finset.card_filter]
  rw [Finset.sum_comm]
  refine le_trans (b := ∑ _x : Fin n → Bool,
      (∏ i ∈ Finset.univ.erase (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}),
        Fintype.card (Fin t → Fin i.1 → ZMod p)) * (p ^ (cs.length - 1)) ^ t)
    (Finset.sum_le_sum (fun x _ => ?_)) (le_of_eq ?_)
  · rw [sum_proj_eq (A := fun k : {k // k ∈ fanins C} => Fin t → Fin k.1 → ZMod p)
        (⟨cs.length, hmem⟩ : {k // k ∈ fanins C})
        (fun ρ => if (∃ j, (cs.get j).eval x = true) ∧
            ∀ s, ∑ j, ρ s j * boolToZMod p ((cs.get j).eval x) = 0 then (1 : ℕ) else 0)]
    refine Nat.mul_le_mul_left _ ?_
    rw [← Finset.card_filter]
    exact localGood_fail_count (m := (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}).1) (t := t) p
      (fun j => (cs.get j).eval x)
  · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]

/-! **`hB` for an AND gate.**  The De Morgan analogue of `gbad_or_column_sum`: the gate's local failures
read its fan-in coordinate over the *negated* children values, and the same Fubini + marginalisation +
`localGood_fail_count` (over `!(child eval)`) give the same column-sum bound. -/
open Classical in
theorem gbad_and_column_sum (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n)
    (cs : List (BoolCircuitSyntax n)) (hmem : cs.length ∈ fanins C) :
    ∑ ω : FormSpace p t C,
        (Finset.univ.filter (fun x : Fin n → Bool =>
          ¬ localGood p t (oracleOf p t C ω) x (.andGate cs))).card
      ≤ Fintype.card (Fin n → Bool)
        * (∏ i ∈ Finset.univ.erase (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}),
            Fintype.card (Fin t → Fin i.1 → ZMod p))
        * (p ^ (cs.length - 1)) ^ t := by
  classical
  have hpred : ∀ (ω : FormSpace p t C),
      (Finset.univ.filter (fun x : Fin n → Bool =>
          ¬ localGood p t (oracleOf p t C ω) x (.andGate cs)))
        = Finset.univ.filter (fun x : Fin n → Bool =>
            (∃ j, (!(cs.get j).eval x) = true) ∧
              ∀ s, ∑ j, ω ⟨cs.length, hmem⟩ s j * boolToZMod p (!(cs.get j).eval x) = 0) := by
    intro ω
    apply Finset.filter_congr
    intro x _
    simp only [localGood, oracleOf_eq p t C ω hmem, not_forall, not_exists, not_not, exists_prop]
  simp only [hpred, Finset.card_filter]
  rw [Finset.sum_comm]
  refine le_trans (b := ∑ _x : Fin n → Bool,
      (∏ i ∈ Finset.univ.erase (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}),
        Fintype.card (Fin t → Fin i.1 → ZMod p)) * (p ^ (cs.length - 1)) ^ t)
    (Finset.sum_le_sum (fun x _ => ?_)) (le_of_eq ?_)
  · rw [sum_proj_eq (A := fun k : {k // k ∈ fanins C} => Fin t → Fin k.1 → ZMod p)
        (⟨cs.length, hmem⟩ : {k // k ∈ fanins C})
        (fun ρ => if (∃ j, (!(cs.get j).eval x) = true) ∧
            ∀ s, ∑ j, ρ s j * boolToZMod p (!(cs.get j).eval x) = 0 then (1 : ℕ) else 0)]
    refine Nat.mul_le_mul_left _ ?_
    rw [← Finset.card_filter]
    exact localGood_fail_count (m := (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}).1) (t := t) p
      (fun j => !(cs.get j).eval x)
  · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]

/-! **`hB` for a MOD gate.**  `localGood` at a `MOD` gate is `q = p` — independent of forms and input.
So for a valid `AC⁰[p]` gate (`q = p`) the local-failure set is empty and the column sum is `0`. -/
open Classical in
theorem gbad_mod_column_sum (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n) (q r : ℕ)
    (cs : List (BoolCircuitSyntax n)) (hq : q = p) :
    ∑ ω : FormSpace p t C,
        (Finset.univ.filter (fun x : Fin n → Bool =>
          ¬ localGood p t (oracleOf p t C ω) x (.modGate q r cs))).card = 0 := by
  classical
  have hempty : ∀ ω : FormSpace p t C,
      (Finset.univ.filter (fun x : Fin n → Bool =>
        ¬ localGood p t (oracleOf p t C ω) x (.modGate q r cs))) = ∅ := by
    intro ω
    rw [Finset.filter_eq_empty_iff]
    intro x _
    simp only [localGood]
    exact not_not.mpr hq
  simp only [hempty, Finset.card_empty, Finset.sum_const_zero]

/-- **Form-space factorisation.**  `|Φ|` splits as the fan-in-`m` coordinate `(p^m)^t` times the product
of the others — the identity that converts a per-gate bound `≤ 2^n·(∏ others)·(p^{m-1})^t` into
`column·p^t ≤ 2^n·|Φ|`. -/
theorem formSpace_card_factor (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n) {m : ℕ}
    (hmem : m ∈ fanins C) :
    (∏ i ∈ Finset.univ.erase (⟨m, hmem⟩ : {k // k ∈ fanins C}),
        Fintype.card (Fin t → Fin i.1 → ZMod p)) * (p ^ m) ^ t
      = Fintype.card (FormSpace p t C) := by
  rw [show Fintype.card (FormSpace p t C)
      = ∏ k : {k // k ∈ fanins C}, Fintype.card (Fin t → Fin k.1 → ZMod p) from Fintype.card_pi,
    ← Finset.prod_erase_mul Finset.univ
      (fun k : {k // k ∈ fanins C} => Fintype.card (Fin t → Fin k.1 → ZMod p))
      (Finset.mem_univ (⟨m, hmem⟩ : {k // k ∈ fanins C}))]
  congr 1
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin]

/-- The joint form space is nonempty, so `0 < |Φ|` (used to cancel `|Φ|`). -/
theorem formSpace_card_pos (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n) :
    0 < Fintype.card (FormSpace p t C) :=
  Fintype.card_pos

/-! **OR-gate column bound, scaled.**  column*p^t <= 2^n*|Phi| (from gbad_or_column_sum + formSpace_card_factor, using (p^{m-1})^t*p^t = (p^m)^t). -/
open Classical in
theorem column_or_le (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n)
    (cs : List (BoolCircuitSyntax n)) (hmem : cs.length ∈ fanins C) (hcs : 1 ≤ cs.length) :
    (∑ ω : FormSpace p t C, (Finset.univ.filter (fun x : Fin n → Bool =>
        ¬ localGood p t (oracleOf p t C ω) x (.orGate cs))).card) * p ^ t
      ≤ Fintype.card (Fin n → Bool) * Fintype.card (FormSpace p t C) := by
  have hp : p ^ (cs.length - 1) * p = p ^ cs.length := by rw [← pow_succ, Nat.sub_add_cancel hcs]
  have hpow : (p ^ (cs.length - 1)) ^ t * p ^ t = (p ^ cs.length) ^ t := by rw [← mul_pow, hp]
  calc (∑ ω : FormSpace p t C, (Finset.univ.filter (fun x : Fin n → Bool =>
          ¬ localGood p t (oracleOf p t C ω) x (.orGate cs))).card) * p ^ t
      ≤ (Fintype.card (Fin n → Bool)
          * (∏ i ∈ Finset.univ.erase (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}),
              Fintype.card (Fin t → Fin i.1 → ZMod p)) * (p ^ (cs.length - 1)) ^ t) * p ^ t :=
        Nat.mul_le_mul_right _ (gbad_or_column_sum p t C cs hmem)
    _ = Fintype.card (Fin n → Bool)
          * ((∏ i ∈ Finset.univ.erase (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}),
              Fintype.card (Fin t → Fin i.1 → ZMod p)) * ((p ^ (cs.length - 1)) ^ t * p ^ t)) := by ring
    _ = Fintype.card (Fin n → Bool) * Fintype.card (FormSpace p t C) := by
        rw [hpow, formSpace_card_factor]

/-! **AND-gate column bound, scaled** (De Morgan analogue of column_or_le). -/
open Classical in
theorem column_and_le (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n)
    (cs : List (BoolCircuitSyntax n)) (hmem : cs.length ∈ fanins C) (hcs : 1 ≤ cs.length) :
    (∑ ω : FormSpace p t C, (Finset.univ.filter (fun x : Fin n → Bool =>
        ¬ localGood p t (oracleOf p t C ω) x (.andGate cs))).card) * p ^ t
      ≤ Fintype.card (Fin n → Bool) * Fintype.card (FormSpace p t C) := by
  have hp : p ^ (cs.length - 1) * p = p ^ cs.length := by rw [← pow_succ, Nat.sub_add_cancel hcs]
  have hpow : (p ^ (cs.length - 1)) ^ t * p ^ t = (p ^ cs.length) ^ t := by rw [← mul_pow, hp]
  calc (∑ ω : FormSpace p t C, (Finset.univ.filter (fun x : Fin n → Bool =>
          ¬ localGood p t (oracleOf p t C ω) x (.andGate cs))).card) * p ^ t
      ≤ (Fintype.card (Fin n → Bool)
          * (∏ i ∈ Finset.univ.erase (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}),
              Fintype.card (Fin t → Fin i.1 → ZMod p)) * (p ^ (cs.length - 1)) ^ t) * p ^ t :=
        Nat.mul_le_mul_right _ (gbad_and_column_sum p t C cs hmem)
    _ = Fintype.card (Fin n → Bool)
          * ((∏ i ∈ Finset.univ.erase (⟨cs.length, hmem⟩ : {k // k ∈ fanins C}),
              Fintype.card (Fin t → Fin i.1 → ZMod p)) * ((p ^ (cs.length - 1)) ^ t * p ^ t)) := by ring
    _ = Fintype.card (Fin n → Bool) * Fintype.card (FormSpace p t C) := by
        rw [hpow, formSpace_card_factor]

/-! ## The composition: ∃ one form choice agreeing off a controlled error set

Instantiating `exists_form_total_errors` (averaging skeleton) with the concrete circuit data — `cbad` the
composed-error set, `gbad` the per-gate local failures, gates `= subcircuits C`, `hsub` from
`cbad_subset_gates` — yields a *single* joint form `ω` whose composed error is bounded by the sum of the
per-gate column sums.  Each of those is in turn bounded by `gbad_{or,and,mod}_column_sum`. -/
open Classical in
/-- **Circuit composition.**  There is a joint form choice `ω` for which the composed approximant's
disagreement with the circuit, scaled by `|Φ|`, is at most the sum over the circuit's gates of their
per-gate local-failure column sums (each `≤ 2^n·(∏ other coords)·(p^{m-1})^t` by `gbad_*_column_sum`,
`0` for `MOD` gates with `q=p` and for leaves/`¬`). -/
theorem exists_form_circuit_agreement (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n) :
    ∃ ω : FormSpace p t C,
      Fintype.card (FormSpace p t C)
          * (Finset.univ.filter (fun x : Fin n → Bool =>
              eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
                ≠ boolToZMod p (C.eval x))).card
        ≤ ∑ G ∈ (subcircuits C).toFinset, ∑ ω' : FormSpace p t C,
            (Finset.univ.filter (fun x : Fin n → Bool =>
              ¬ localGood p t (oracleOf p t C ω') x G)).card := by
  obtain ⟨ω, _, hω⟩ := exists_form_total_errors (X := Fin n → Bool)
    (Finset.univ : Finset (FormSpace p t C)) Finset.univ_nonempty (subcircuits C).toFinset
    (fun G ω => Finset.univ.filter (fun x : Fin n → Bool =>
      ¬ localGood p t (oracleOf p t C ω) x G))
    (fun ω => Finset.univ.filter (fun x : Fin n → Bool =>
      eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
        ≠ boolToZMod p (C.eval x)))
    (fun G => ∑ ω' : FormSpace p t C,
      (Finset.univ.filter (fun x : Fin n → Bool => ¬ localGood p t (oracleOf p t C ω') x G)).card)
    (fun ω _ => cbad_subset_gates p t (oracleOf p t C ω) C)
    (fun _ _ => le_refl _)
  rw [Finset.card_univ] at hω
  exact ⟨ω, hω⟩

open Classical in
/-- A gate whose local goodness always holds contributes `0` to the error (its failure set is empty). -/
theorem column_zero_of_localGood (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n)
    (G : BoolCircuitSyntax n)
    (h : ∀ (ω : FormSpace p t C) (x : Fin n → Bool), localGood p t (oracleOf p t C ω) x G) :
    (∑ ω : FormSpace p t C, (Finset.univ.filter (fun x : Fin n → Bool =>
        ¬ localGood p t (oracleOf p t C ω) x G)).card) = 0 := by
  have hempty : ∀ ω : FormSpace p t C, (Finset.univ.filter (fun x : Fin n → Bool =>
      ¬ localGood p t (oracleOf p t C ω) x G)) = ∅ := by
    intro ω
    rw [Finset.filter_eq_empty_iff]
    exact fun x _ => not_not.mpr (h ω x)
  simp only [hempty, Finset.card_empty, Finset.sum_const_zero]

open Classical in
/-- **The composed error bound.**  For an `AC⁰[p]` circuit (every `MOD` gate has `q=p`), there is a form
choice `ω` for which the circuit approximant disagrees with the circuit on a `p^{-t}`-per-gate fraction:
`|{x : approximant errs}| · p^t ≤ (#subcircuits) · 2^n`.  This is the Razborov–Smolensky agreement
guarantee — composed degree `≤ ((p-1)t)^depth` (degree side), error `≤ s·p^{-t}` (this). -/
theorem composed_error_le (p t : ℕ) [Fact p.Prime] {n : ℕ} (C : BoolCircuitSyntax n)
    (hmod : ∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C →
      q = p) :
    ∃ ω : FormSpace p t C,
      (Finset.univ.filter (fun x : Fin n → Bool =>
          eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
            ≠ boolToZMod p (C.eval x))).card * p ^ t
        ≤ (subcircuits C).toFinset.card * Fintype.card (Fin n → Bool) := by
  obtain ⟨ω, hω⟩ := exists_form_circuit_agreement p t C
  refine ⟨ω, ?_⟩
  have hperGate : ∀ G ∈ (subcircuits C).toFinset,
      (∑ ω' : FormSpace p t C, (Finset.univ.filter (fun x : Fin n → Bool =>
          ¬ localGood p t (oracleOf p t C ω') x G)).card) * p ^ t
        ≤ Fintype.card (Fin n → Bool) * Fintype.card (FormSpace p t C) := by
    intro G hGmem
    rw [List.mem_toFinset] at hGmem
    match G, hGmem with
    | .const b, _ =>
        rw [column_zero_of_localGood p t C (.const b) (fun ω' x => by simp only [localGood])]; simp
    | .input i, _ =>
        rw [column_zero_of_localGood p t C (.input i) (fun ω' x => by simp only [localGood])]; simp
    | .not c, _ =>
        rw [column_zero_of_localGood p t C (.not c) (fun ω' x => by simp only [localGood])]; simp
    | .orGate cs, hG =>
        by_cases hcs : 1 ≤ cs.length
        · exact column_or_le p t C cs (gateFanin_mem_fanins hG) hcs
        · rw [column_zero_of_localGood p t C (.orGate cs)
            (fun ω' x => by simp only [localGood]; rintro ⟨j, _⟩; exact absurd j.isLt (by omega))]
          simp
    | .andGate cs, hG =>
        by_cases hcs : 1 ≤ cs.length
        · exact column_and_le p t C cs (gateFanin_mem_fanins hG) hcs
        · rw [column_zero_of_localGood p t C (.andGate cs)
            (fun ω' x => by simp only [localGood]; rintro ⟨j, _⟩; exact absurd j.isLt (by omega))]
          simp
    | .modGate q r cs, hG =>
        rw [gbad_mod_column_sum p t C q r cs (hmod q r cs hG)]; simp
  have hsum : (∑ G ∈ (subcircuits C).toFinset, ∑ ω' : FormSpace p t C,
        (Finset.univ.filter (fun x : Fin n → Bool =>
          ¬ localGood p t (oracleOf p t C ω') x G)).card) * p ^ t
      ≤ (subcircuits C).toFinset.card
          * (Fintype.card (Fin n → Bool) * Fintype.card (FormSpace p t C)) := by
    rw [Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum hperGate) ?_
    rw [Finset.sum_const, smul_eq_mul]
  have h1 : Fintype.card (FormSpace p t C)
        * ((Finset.univ.filter (fun x : Fin n → Bool =>
            eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
              ≠ boolToZMod p (C.eval x))).card * p ^ t)
      ≤ Fintype.card (FormSpace p t C)
        * ((subcircuits C).toFinset.card * Fintype.card (Fin n → Bool)) := by
    calc Fintype.card (FormSpace p t C)
          * ((Finset.univ.filter (fun x : Fin n → Bool =>
              eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
                ≠ boolToZMod p (C.eval x))).card * p ^ t)
        = (Fintype.card (FormSpace p t C)
            * (Finset.univ.filter (fun x : Fin n → Bool =>
              eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
                ≠ boolToZMod p (C.eval x))).card) * p ^ t := by ring
      _ ≤ (∑ G ∈ (subcircuits C).toFinset, ∑ ω' : FormSpace p t C,
            (Finset.univ.filter (fun x : Fin n → Bool =>
              ¬ localGood p t (oracleOf p t C ω') x G)).card) * p ^ t :=
          Nat.mul_le_mul_right _ hω
      _ ≤ (subcircuits C).toFinset.card
            * (Fintype.card (Fin n → Bool) * Fintype.card (FormSpace p t C)) := hsum
      _ = Fintype.card (FormSpace p t C)
            * ((subcircuits C).toFinset.card * Fintype.card (Fin n → Bool)) := by ring
  exact Nat.le_of_mul_le_mul_left h1 (formSpace_card_pos p t C)

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toAgree
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.AgreeGood
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orGate_eval_iff
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.andGate_eval_iff
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.sum_boolToZMod_get
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toAgree_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toAgree_bad_imp_not_good
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toAgree_cbad_subset
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.mem_subcircuitsList
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.agreeGood_of_forall
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.cbad_subset_gates
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.localGood_fail_count
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.gateFanin_mem_fanins
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.oracleOf_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.gbad_or_column_sum
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.gbad_and_column_sum
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.gbad_mod_column_sum
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.exists_form_circuit_agreement
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.formSpace_card_factor
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.column_or_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.column_and_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.column_zero_of_localGood
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.composed_error_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.column_and_le
