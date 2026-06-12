import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBranchingObserver

/-!
# Faithfulness ⇒ non-mergeability: the continuation bridge (the heart of Option B)

`BranchingObserver` proved *if* sectors are non-mergeable *then* boundary is large.  But non-mergeability was
a **hypothesis**.  This file supplies the missing half — the reason a *correct* observer cannot merge: it
**derives** non-mergeability from **correctness over continuations**.

This is exactly the principle articulated as the heart of the matter:

> SAT's witness hypercube cannot be quotiented into few observer-boundary states *without identifying
> satisfiable and unsatisfiable continuations*.

## The model

Inputs split as `prefix × suffix`.  An observer reads the `prefix` and emits a boundary state (`view : prefix
→ Fin (2^entropy)`); the decision `dec : prefix → suffix → Bool` is the truth of the instance.

* **Faithful** (`Faithful`): the boundary state determines behavior on *every* continuation —
  `view p = view q → ∀ s, dec p s = dec q s`.  A faithful observer never merges two prefixes that some suffix
  would tell apart.  (This is *soundness across completions*: the only honest meaning of "the observer's
  boundary suffices to finish the computation".)
* **Separated** (`Separated`): a set of prefixes that *are* told apart — for any two, some continuation
  decides them differently.  (A communication fooling set.)

## The theorem

> `faithful_separated_forces_boundary` — a faithful observer over a separated set of `K` prefixes has
> boundary entropy `≥ log₂ K`.

Now non-mergeability is **proved** (faithful + separated ⇒ `Nonmergeable`), not assumed.  This closes the
gap the abstraction left open: correctness over continuations *forces* the boundary up.

## Instantiation and the honest wall

`equality_continuation_forces_boundary` instantiates it on the canonical **EQUALITY** decision
`dec p s = (p == s)`: all `2ⁿ` prefixes are pairwise separated (`s = p` decides `p` vs `q`), so *every*
faithful observer of this `prefix|suffix` split has boundary `≥ n`.  This is a genuine, unconditional
super-logarithmic boundary lower bound — **for this fixed decomposition**.

And it is *still* not a hardness proof, for the standing reason: EQUALITY has an `O(n)`-size circuit, so a
*different* decomposition makes it cheap.  The bound is on the boundary of one fixed split; a separation
needs `≥ ω(log n)` under **every** admissible decomposition (`= CookLevinFrontierHyp`).  What this file adds
is real: the faithfulness→boundary implication is now a theorem, so the only remaining open quantity is the
*minimum over decompositions* — the wall is now drawn at exactly one quantifier.
-/

namespace PallLean.Paper93.DeepMath.PathB.ContinuationObserver

open PallLean.Paper93.DeepMath.PathB

variable {Pre Suf : Type*}

/-- **Faithful observer**: its boundary state determines behavior on every continuation.  Two prefixes with
the same boundary view must agree under *all* suffixes — the observer never merges prefixes a completion
would separate. -/
def Faithful (O : BranchingObserver Pre) (dec : Pre → Suf → Bool) : Prop :=
  ∀ p q : Pre, O.view p = O.view q → ∀ s : Suf, dec p s = dec q s

/-- **Separated set** (communication fooling set): prefixes pairwise told apart by some continuation. -/
def Separated (dec : Pre → Suf → Bool) (F : Finset Pre) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, p ≠ q → ∃ s : Suf, dec p s ≠ dec q s

/-- **Faithfulness ⇒ non-mergeability (the bridge).**  A faithful observer keeps a separated set
non-mergeable: if it merged two of them, faithfulness would force them to agree on all continuations,
contradicting separation. -/
theorem faithful_separated_nonmergeable (O : BranchingObserver Pre) (dec : Pre → Suf → Bool)
    (hf : Faithful O dec) {F : Finset Pre} (hsep : Separated dec F) :
    O.Nonmergeable F := by
  intro p hp q hq hview
  by_contra hpq
  obtain ⟨s, hs⟩ := hsep p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) hpq
  exact hs (hf p q hview s)

/-- **Correctness over continuations forces the boundary up.**  A faithful observer over a separated set of
`K` prefixes has boundary entropy `≥ log₂ K`.  (Non-mergeability is now *derived* from faithfulness, not
assumed.) -/
theorem faithful_separated_forces_boundary (O : BranchingObserver Pre) (dec : Pre → Suf → Bool)
    (hf : Faithful O dec) {F : Finset Pre} (hsep : Separated dec F) :
    Nat.log 2 F.card ≤ O.entropy :=
  O.many_nonmergeable_sectors_force_boundary F (faithful_separated_nonmergeable O dec hf hsep)

/-- **Exponential form.**  If a faithful observer faces `≥ 2^k` pairwise-separated prefixes, its boundary
entropy is `≥ k`.  With `k = ω(log n)` this is the shape of a separation — for the given decomposition. -/
theorem faithful_separated_exp (O : BranchingObserver Pre) (dec : Pre → Suf → Bool)
    (hf : Faithful O dec) {F : Finset Pre} (hsep : Separated dec F) {k : ℕ} (hmany : 2 ^ k ≤ F.card) :
    k ≤ O.entropy :=
  O.exp_nonmergeable_sectors_force_boundary F (faithful_separated_nonmergeable O dec hf hsep) hmany

/-! ## Instantiation: the EQUALITY decision (canonical fooling set) -/

/-- The EQUALITY decision on an `n`-bit `prefix|suffix` split: `dec p s = (p == s)`. -/
def eqDec (n : ℕ) (p s : Fin n → Bool) : Bool := decide (p = s)

/-- Every pair of distinct prefixes is separated by EQUALITY: take the continuation `s = p`. -/
theorem eqDec_separated (n : ℕ) : Separated (eqDec n) (Finset.univ : Finset (Fin n → Bool)) := by
  intro p _ q _ hpq
  refine ⟨p, ?_⟩
  have h1 : eqDec n p p = true := by simp [eqDec]
  have h2 : eqDec n q p = false := by simp only [eqDec, decide_eq_false_iff_not]; exact fun h => hpq h.symm
  rw [h1, h2]; decide

/-- **EQUALITY forces faithful-observer boundary `≥ n` (for this split).**  Every faithful observer of the
`prefix|suffix` EQUALITY decision has boundary entropy `≥ n`: its `2ⁿ` prefixes are pairwise separated, so it
must keep them all distinct.  A genuine super-logarithmic boundary lower bound — but for one fixed
decomposition (EQUALITY is easy under another), so not a hardness proof. -/
theorem equality_continuation_forces_boundary (n : ℕ)
    (O : BranchingObserver (Fin n → Bool)) (hf : Faithful O (eqDec n)) :
    n ≤ O.entropy := by
  refine faithful_separated_exp O (eqDec n) hf (eqDec_separated n) (k := n) ?_
  have : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Finset.card_univ, Fintype.card_fun]
  rw [this]

end PallLean.Paper93.DeepMath.PathB.ContinuationObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ContinuationObserver.faithful_separated_forces_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.ContinuationObserver.equality_continuation_forces_boundary
