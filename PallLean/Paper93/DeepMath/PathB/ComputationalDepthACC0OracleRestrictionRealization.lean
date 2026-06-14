import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModComposition

/-!
# The position → `x` bridge: realizing oracle-output restrictions by input restrictions

`…ACC0DNFControlSwitching` proved the DNF-control switching collapse — but its restriction `ρ` is over the **oracle
output positions** (`Fin k → Option Bool`), not the actual input variables `x` (`Fin n → Option Bool`).  The `MOD`
outputs are *determined* by `x`, so a position-restriction need not correspond to any input restriction.  This file is
that bridge: **when can a fixed oracle-output pattern be `forced` by an input restriction?**

* `RealizableByInputRestriction ρ gate` — there is an input restriction `σ` such that *every* completion of `σ` forces
  each fixed gate `j` (`ρ j = some b`) to output `b`.  ("Forcing" a `MOD` gate requires fixing its whole support — the
  no-go `mod_gate_parity_nonconstant`.)
* `realizable_of_disjoint` — **positive fragment**: if the gate supports are pairwise disjoint and each fixed output is
  achievable, the pattern is realizable (set each fixed gate's support independently — disjointness ⇒ no conflict).
* `position_restriction_not_always_realizable` — **the no-go**: for *overlapping* gates the bridge can FAIL — two `MOD`
  gates on the same support with conflicting targets cannot both be forced, since they compute the same statistic.

So the position → `x` bridge is **true on the disjoint fragment and false in general** — which is exactly why it must
stay fragment-restricted (a socket for arbitrary circuits), not a free theorem.

## What is proved (clean axioms, no `sorry`)

* `Extends`, `RealizableByInputRestriction` — input restrictions and the realizability predicate.
* `modGate_eval_congr` — a `MOD` gate's value depends only on its support.
* `realizable_of_disjoint` — the positive fragment (disjoint supports + per-gate achievability).
* `position_restriction_not_always_realizable` — the no-go (conflicting overlapping gates).

## Honest scope

This solves the *forcing* half of the bridge (fix the determined gates) on the disjoint fragment, and proves the
general bridge is genuinely false.  It does **not** yet supply the *full* composition with switching — that also needs
the *free* gates to stay free under `σ` so the collapsed control's free positions remain genuine (a refinement that the
disjoint case supports but is not assembled here).  Composing realizable restrictions with the DNF switching collapse
into an `x`-level circuit speedup, for the disjoint fragment, is the next assembly step; for overlapping gates the no-go
shows it cannot hold unconditionally.  Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel

variable {n k : ℕ}

/-- `x` extends the input restriction `σ` (agrees on every fixed coordinate). -/
def Extends (x : Fin n → Bool) (σ : Fin n → Option Bool) : Prop :=
  ∀ i v, σ i = some v → x i = v

/-- The oracle-output restriction `ρ` is **realizable by an input restriction**: some `σ` forces every fixed gate to
its `ρ`-value on all completions. -/
def RealizableByInputRestriction (ρ : Fin k → Option Bool) (gate : Fin k → ModGate n) : Prop :=
  ∃ σ : Fin n → Option Bool, ∀ j b, ρ j = some b → ∀ x, Extends x σ → (gate j).eval x = b

/-- **A `MOD` gate's value depends only on its support (proved).** -/
theorem modGate_eval_congr (G : ModGate n) {x x' : Fin n → Bool}
    (h : ∀ i ∈ G.support, x i = x' i) : G.eval x = G.eval x' := by
  have hw : weightOn G.support x = weightOn G.support x' := by
    unfold weightOn
    exact Finset.sum_congr rfl (fun i hi => by rw [h i hi])
  unfold ModGate.eval modQStatOn
  rw [hw]

/-- **Positive fragment (proved): disjoint supports + per-gate achievability ⇒ realizable.**  Set each fixed gate's
(whole) support to a witnessing assignment; disjointness guarantees the per-gate settings never conflict. -/
theorem realizable_of_disjoint (ρ : Fin k → Option Bool) (gate : Fin k → ModGate n)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (gate j).support (gate j').support)
    (hach : ∀ j b, ρ j = some b → ∃ a : Fin n → Bool, (gate j).eval a = b) :
    RealizableByInputRestriction ρ gate := by
  classical
  -- a per-gate witnessing assignment (arbitrary on unfixed gates)
  have key : ∀ j, ∃ a : Fin n → Bool, ∀ b, ρ j = some b → (gate j).eval a = b := by
    intro j
    by_cases hj : (ρ j).isSome
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hj
      obtain ⟨a, ha⟩ := hach j b hb
      refine ⟨a, fun b' hb' => ?_⟩
      rw [hb] at hb'
      rw [← Option.some.inj hb']; exact ha
    · refine ⟨fun _ => false, fun b hb => ?_⟩
      rw [hb] at hj
      simp at hj
  choose a ha using key
  -- the input restriction: fix coordinate i to the witness of the (unique) fixed gate whose support contains i
  refine ⟨fun i => if h : ∃ j, (∃ b, ρ j = some b) ∧ i ∈ (gate j).support
      then some (a (Classical.choose h) i) else none, ?_⟩
  intro j b hjb x hx
  -- x agrees with `a j` on `gate j`'s support, hence evaluates to `b`
  have hagree : ∀ i ∈ (gate j).support, x i = a j i := by
    intro i hi
    have hex : ∃ j', (∃ b', ρ j' = some b') ∧ i ∈ (gate j').support := ⟨j, ⟨b, hjb⟩, hi⟩
    have hspec := Classical.choose_spec hex
    have hchoose : Classical.choose hex = j := by
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisj (Classical.choose hex) j hne) hspec.2) hi
    have hσi : (fun i => if h : ∃ j', (∃ b', ρ j' = some b') ∧ i ∈ (gate j').support
        then some (a (Classical.choose h) i) else none) i = some (a (Classical.choose hex) i) :=
      dif_pos hex
    have hxi : x i = a (Classical.choose hex) i := hx i (a (Classical.choose hex) i) hσi
    rw [hxi, hchoose]
  rw [modGate_eval_congr (gate j) hagree]
  exact ha j b hjb

/-- **The no-go (proved): for overlapping gates the bridge can fail.**  Two `MOD₂` gates on the same support `{0}` with
targets `0` and `1` cannot both be forced to output `true` — they compute the same statistic, so any input gives the
same residue, and `0 ≠ 1` in `ZMod 2`. -/
theorem position_restriction_not_always_realizable :
    ∃ (kk nn : ℕ) (gate : Fin kk → ModGate nn) (ρ : Fin kk → Option Bool),
      ¬ RealizableByInputRestriction ρ gate := by
  refine ⟨2, 1, ![⟨2, {0}, 0⟩, ⟨2, {0}, 1⟩], fun _ => some true, ?_⟩
  rintro ⟨σ, hσ⟩
  set x : Fin 1 → Bool := fun i => (σ i).getD false with hx
  have hext : Extends x σ := by
    intro i v hv; rw [hx]; simp [hv]
  have h0 := hσ 0 true rfl x hext
  have h1 := hσ 1 true rfl x hext
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ModGate.eval] at h0 h1
  have e0 : modQStatOn {0} 2 x = 0 := of_decide_eq_true h0
  have e1 : modQStatOn {0} 2 x = 1 := of_decide_eq_true h1
  rw [e0] at e1
  exact absurd e1 (by decide)

end PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization.realizable_of_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization.position_restriction_not_always_realizable
