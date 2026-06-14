import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DecisionTreeObserver

/-!
# Composing the AC⁰ decision-tree layer with the MOD layer, across the no-go

The MOD no-go (`ACCSwitchingModBridge.mod_gate_parity_nonconstant`) says switching cannot make a `MOD` gate constant:
a random restriction never collapses it.  So an `ACC⁰` circuit cannot be flattened by switching *through* its `MOD`
gates.  This file gives the honest way the two layers compose **without** violating the no-go: the `MOD` gates are
treated as **oracles** that the (switching-collapsed) `AC⁰` top *queries* — never collapsed.

Concretely: if the `AC⁰` top is a decision tree `T` of depth `d` over the `m` `MOD`-gate-output positions, then the
composed function `x ↦ T(g₁(x), …, g_m(x))` is `ObservedBy` a boundary of `≤ 2^d` cells (the leaf `T` reaches).  Each
leaf-cell is `{x : the ≤ d gates queried along the path give these outputs}`; the function is constant on each cell.
The `MOD` gates are evaluated as oracles along the path — never forced constant — so the no-go is respected, yet the
combined boundary is `2^d`, *independent of the gates' moduli and of how many variables they read*.

The composition is via a general primitive `dt_oracle_observed`: a decision tree over *any* family of Boolean
oracle-subfunctions `h : Fin m → (Fin n → Bool) → Bool` has a `≤ 2^{depth}` boundary (the same sum-typed leaf observer
as `dt_observed`, branching on `h i x` instead of `x i`).  Instantiating `h j = (gⱼ).eval` gives the `AC⁰`-over-`MOD`
composition.

## What is proved (clean axioms, no `sorry`)

* `dt_oracle_observed` — a depth-`d` decision tree over Boolean oracle-subfunctions has a `≤ 2^d` observer boundary.
* `acc0_over_mod_observed` — `x ↦ T(g₁(x),…,g_m(x))` (`T` a depth-`d` DT, `gⱼ` `MOD` gates) is `ObservedBy` a `≤ 2^d`
  boundary, with the `MOD` gates queried as oracles (not collapsed).
* `acc0_over_mod_searchable` — that function is SAT-searchable in `< 2^n` once `2^d < 2^n`.

## Honest scope — where the no-go still bites

This is the **deterministic observer-composition law**: *given* a depth-`d` decision tree `T` over the `MOD`-gate
outputs, the boundary is `2^d`.  It does **not** supply that such a shallow `T` exists, and that is exactly where the
no-go bites in its deeper form: the gate outputs `gⱼ(x)` are *determined* by `x` (not independent random bits), so the
switching lemma's random-restriction analysis does **not** transfer to collapse the top *over the gate outputs*.  Thus
the law composes a *single* `AC⁰`-over-`MOD` level (`MOD` gates as oracles); iterating switching through a `MOD` layer
to reach lower `AC⁰` layers remains blocked — the genuine open `ACC⁰` frontier.  I do not fake that step.  Still the
cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModComposition

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0DecisionTreeObserver

variable {n : ℕ}

/-- **The decision-tree oracle composition (proved, induction): a decision tree over Boolean oracle-subfunctions
`h : Fin m → (Fin n → Bool) → Bool` computes a function `ObservedBy` a `≤ 2^{depth}` boundary.**  Identical to
`dt_observed` but each query node branches on the oracle value `h i x` rather than a raw bit `x i`; the boundary is the
leaf reached, with at most `2^{depth}` leaves. -/
theorem dt_oracle_observed {m : ℕ} (T : BoolDecisionTree m) (h : Fin m → (Fin n → Bool) → Bool) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S),
      ObservedBy (fun x => BoolDecisionTree.eval T (fun j => h j x)) stat ∧ Fintype.card S ≤ 2 ^ T.depth := by
  induction T with
  | leaf b =>
      exact ⟨Unit, inferInstance, inferInstance, fun _ => (), ⟨fun _ => b, fun _ => rfl⟩, by simp⟩
  | query i lo hi ihlo ihhi =>
      obtain ⟨Sl, fl, dl, statl, ⟨gl, hgl⟩, hcl⟩ := ihlo
      obtain ⟨Sh, fh, dh, stath, ⟨gh, hgh⟩, hch⟩ := ihhi
      letI := fl; letI := dl; letI := fh; letI := dh
      refine ⟨Sl ⊕ Sh, inferInstance, inferInstance,
        fun x => if h i x then Sum.inr (stath x) else Sum.inl (statl x), ?_, ?_⟩
      · refine ⟨Sum.elim gl gh, fun x => ?_⟩
        simp only [BoolDecisionTree.eval, Sum.elim_inr, Sum.elim_inl, apply_ite (Sum.elim gl gh)]
        rw [show hi.eval (fun j => h j x) = gh (stath x) from hgh x,
            show lo.eval (fun j => h j x) = gl (statl x) from hgl x]
      · simp only [Fintype.card_sum, BoolDecisionTree.depth]
        calc Fintype.card Sl + Fintype.card Sh
            ≤ 2 ^ lo.depth + 2 ^ hi.depth := Nat.add_le_add hcl hch
          _ ≤ 2 ^ max lo.depth hi.depth + 2 ^ max lo.depth hi.depth :=
              Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
                             (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
          _ = 2 ^ (max lo.depth hi.depth + 1) := by rw [pow_succ]; ring

/-- **AC⁰-over-MOD composition across the no-go (proved).**  A depth-`d` decision-tree top `T` over the `m`
`MOD`-gate-output positions, composed with the `MOD` gates `g` as oracles, computes a function `ObservedBy` a `≤ 2^d`
boundary — the `MOD` gates are queried along each path, never collapsed (respecting the no-go). -/
theorem acc0_over_mod_observed {m : ℕ} (T : BoolDecisionTree m) (g : Fin m → ModGate n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S),
      ObservedBy (fun x => BoolDecisionTree.eval T (fun j => (g j).eval x)) stat ∧
        Fintype.card S ≤ 2 ^ T.depth :=
  dt_oracle_observed T (fun j => (g j).eval)

/-- **The AC⁰-over-MOD composite is SAT-searchable below brute force when `2^d < 2^n` (proved).** -/
theorem acc0_over_mod_searchable {m : ℕ} (T : BoolDecisionTree m) (g : Fin m → ModGate n)
    (hreg : 2 ^ T.depth < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (gg : S → Bool),
      (Satisfiable (fun x => BoolDecisionTree.eval T (fun j => (g j).eval x)) ↔
          ∃ s ∈ Finset.univ.image stat, gg s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n := by
  obtain ⟨S, fS, dS, stat, ⟨gg, hgg⟩, hcard⟩ := acc0_over_mod_observed T g
  letI := fS; letI := dS
  exact ⟨S, fS, dS, stat, gg, observed_sat_iff gg hgg,
    lt_of_le_of_lt (le_trans (observed_cellCount_le stat) hcard) hreg⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ModComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModComposition.dt_oracle_observed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModComposition.acc0_over_mod_searchable
