import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalParity

/-!
# Block-DT model, foundation 30: the adaptive canonical switching package (culmination) (branch only)

The bundled, machine-checked result of the adaptive-canonical-tree arc (increment 3), and an honest
statement of exactly where the AC⁰ lower bound stands.

## What is proved (`adaptive_canonical_switching`)

For a width-`≤ w` DNF `cs`, a restriction `σ` with `stars σ < F`, the adaptive canonical decision tree
`canonicalDTree cs w F σ` satisfies, simultaneously:

1. **eval-correctness on the subcube** — it computes the DNF on every `σ`-consistent input
   (`canonicalDTree_eval`);
2. **depth upper bound** — `depth ≤ F · w` (`canonicalDTree_depth_le`);
3. **parity depth lower bound** — if it computes parity on the subcube, `depth ≥ stars σ`
   (`canonicalDTree_depth_ge_of_parity`).

This is a sound+complete shallow decision tree for the restricted DNF, with matched depth bounds.

## Honest status of the AC⁰ lower bound

(2) and (3) are *consistent*: deterministically `depth = stars σ` is achievable, and parity genuinely
*is* computable by a depth-`stars σ` canonical tree (read every survivor).  So a **single** restriction
yields no contradiction — there is no clean deterministic `depth < stars σ` bound, and none can exist.

The AC⁰ lower bound (`parity ∉ AC⁰`) instead requires the **probabilistic** ingredient: that *most*
restrictions make the canonical descent short (`blockStream.length < s`), which is the switching
**count** — `block_switching_count_tight`, `block_switching_prob_closed`, `circuit_collapse_budget`
(bricks 1–13, 20).  Bridging that count to this adaptive tree (the two decision-tree models) over the
`d-2` rounds is the genuine remaining work, and it is where the bulk of the switching lemma's difficulty
lives.  The unconditional depth-2 case is already closed deterministically: `dnf_parity_size_bound` (a
width-`≤ w` DNF for parity needs `≥ n/w` terms).

Nothing here is faked: every component is a proved theorem with clean axioms, and the remaining bridge is
named precisely rather than asserted.  AC⁰ ceiling; not P≠NP-strength.

Clean, no `sorry`, no `native_decide`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The adaptive canonical switching package.**  For a width-`≤ w` DNF and `stars σ < F`: the adaptive
canonical tree computes the DNF on the subcube, has depth `≤ F·w`, and (if it computes parity) depth
`≥ stars σ`. -/
theorem adaptive_canonical_switching (cs : List (Clause n)) (w F : ℕ) (σ : Fin n → Option Bool)
    (hsf : stars σ < F) (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    (∀ x, DTree.agreeRestriction σ x →
        (canonicalDTree cs w F σ).eval x = DTree.dnfValue cs x)
      ∧ (canonicalDTree cs w F σ).depth ≤ F * w
      ∧ ((∀ x, DTree.agreeRestriction σ x → DTree.dnfValue cs x = DTree.parity x) →
          stars σ ≤ (canonicalDTree cs w F σ).depth) :=
  ⟨fun x hx => canonicalDTree_eval cs w F σ x hsf hx,
   canonicalDTree_depth_le cs w hw F σ,
   fun hpar => canonicalDTree_depth_ge_of_parity cs w F σ hsf hpar⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.adaptive_canonical_switching
