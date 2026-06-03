import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DepthReplayTie

/-!
# The tight `depth ≤ s` direction: what is available, and the irreducible core

The master squeeze takes, as its one bridge hypothesis, a *shallow* refuting tree (`depth < t`).
Producing it from a good restriction is the tight `depth ≤ s` direction.  This file pins down,
honestly, exactly what is and is not provable here.

## What is proved

* `canonicalDT_depth_le_stars` — the **unconditional** bound: `(canonicalDT cs (stars ρ) ρ).depth
  ≤ stars ρ` (every query fixes a distinct free variable, so no branch exceeds the star count).
* `stars_le_imp_depth_le` — the **trivial direction** of "few stars ⟹ shallow":
  `stars ρ ≤ b ⟹ depth ≤ b`.

## Why the tight switching direction is irreducible here

`canonicalDT.depth` is the **maximum over all branches** (the genuine stop-on-satisfied depth).
The switching *count* bounds `canonLabelLen` — the length of the **single satisfying-completion
path** (`encLits`), one specific branch.  These are not comparable:

* `canonicalDT_depth_ge_replay` already shows `depth ≥` the canonical *falsify* path length — a
  branch — so `depth ≥` (single-path measures);
* but a good restriction (`canonLabelLen ≤ budget`) need not have `depth ≤ budget`: the deepest
  branch can falsify many terms (one query each) and run far past the satisfying-completion path.

So the tight `depth ≤ s` for a good restriction requires bounding the **deepest branch**, i.e. the
switching count for *tree depth* under random restrictions — encoding the deepest-leaf path, whose
decoder faces the same active-clause-identification core as `hdec` (discharged here only for the
single falsify path, in the ρ-falsifies-nothing regime).  That deepest-branch count is **not** a
corollary of the single-path machinery and is the genuine remaining hard core; it is **not faked**.

The honest status: the *unconditional* `depth ≤ stars` and the *trivial* few-stars direction are
proved; the *tight* `depth ≤ s` (with `stars ρ ≫ s`, the switching phenomenon) is the irreducible
deepest-branch switching lemma, distinct from everything discharged in this arc.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Unconditional depth bound.**  The canonical tree (run with fuel `= stars ρ`) has depth at
most the star count: each query fixes a distinct free variable, so no branch is longer than the
number of free variables. -/
theorem canonicalDT_depth_le_stars (cs : List (Clause n)) (ρ : Fin n → Option Bool) :
    (canonicalDT cs (SwitchingCounting.stars ρ) ρ).depth ≤ SwitchingCounting.stars ρ :=
  canonicalDT_depth_le cs (SwitchingCounting.stars ρ) ρ

/-- **Few stars ⟹ shallow (the trivial direction).**  A restriction with at most `b` stars has a
canonical tree of depth at most `b`.  (The switching phenomenon — depth `≤ s` even when `stars ρ`
is large — is the deepest-branch count, not this.) -/
theorem stars_le_imp_depth_le (cs : List (Clause n)) (ρ : Fin n → Option Bool) {b : ℕ}
    (h : SwitchingCounting.stars ρ ≤ b) :
    (canonicalDT cs (SwitchingCounting.stars ρ) ρ).depth ≤ b :=
  le_trans (canonicalDT_depth_le_stars cs ρ) h

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDT_depth_le_stars
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_le_imp_depth_le
