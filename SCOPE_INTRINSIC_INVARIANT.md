# SCOPE: a "representation/padding-invariant by definition" invariant for P vs NP

This assesses recommendation #2 from `SCOPE_OBSERVER_BOUNDARY_THREAD.md`: *find an invariant that is representation-
and padding-invariant by definition — not patched to be, but intrinsically so — and use it to separate P from NP.*
It is a **map of the obstruction**, not a construction. **Verdict: this direction does not make P vs NP easier.
A representation/padding-invariant-by-definition invariant that separates P from NP is forced by a dichotomy —
each horn is a known barrier (or is circular), and the only path that dodges all known barriers is the GCT
program, whose concrete instantiation is proven insufficient and whose surviving form is stuck.** Where the claim
touches machine-checked results, they are cited.

## 1. What the target precisely requires

An invariant here means a map `I : {Boolean functions / languages} → value` such that

* **(representation-invariant by definition)** `I(L)` depends only on the language `L`, not on any machine,
  circuit, formula, cut, query scheme, or serialization that computes it — i.e. `I` is literally a function of
  the truth table, quantified over nothing;
* **(padding-invariant)** `I(L) = I(pad(L))` for the padding maps (adding dummy input bits, or dummy
  computation) — the invariant is not inflated or deflated by content-free structure.

To separate P from NP it must additionally be **useful**: `I` polynomially bounded on every `L ∈ P` and provably
super-polynomial on some `L ∈ NP`.

The observer thread failed *because* its measures were representation-**dependent** (defined through a cut / BP /
query scheme) and padding-**sensitive** (the canonical query scheme's innovation was exactly the clock —
`ChargedCanonicalQueryAudit.canonical_schemeResource_eq_clock`, `charged_dynamic_padding_sensitive`). The proposal
is to remove both defects by definition. This document asks whether that is possible while staying useful.

## 2. The dichotomy

Every candidate `I` satisfying (representation-invariant) + (padding-invariant) falls into exactly one of two
classes, and each is a dead end for a *different* reason.

### Horn A — intrinsic function properties (poly-bounded / collapse)

`I` is an intrinsic combinatorial measure of the truth table: sensitivity, block sensitivity, certificate /
decision-tree complexity, polynomial degree, Fourier weight, communication complexity, subfunction / residual
count, residual-span rank. These *are* representation- and padding-invariant by definition (dummy variables
contribute nothing). But they are all **polynomially bounded in `n` at each length** and are properties of `f_n`
at a *fixed* input length — they do not scale with the *time to compute `L` across all lengths*. Both P-languages
and NP-languages realize the full range of every such measure, so none separates.

This horn is not speculative here — it is what our own machine-checked results show for the observer boundary,
which is exactly such an intrinsic measure once you quantify away the cut:

* **min over decompositions → trivial.** `DimensionUpperBound.unrestricted_min_trivial`: for every `f`,
  `∃ S, dimResiduals S f ≤ 1`. The empty cut makes the representation-invariant *minimum* useless.
* **max over decompositions → high for a P-language.** `DimensionFullRank.eqFun_dim_ge`: the equality function
  (which is in P) has `dimResiduals ≥ 2^k` on a structured block. So the representation-invariant *maximum* is
  already exponential for an easy function — a P-language achieves the extreme value, hence no separation.

So *both* canonical ways to make our boundary intrinsic (min and max over all cuts) fail, and they fail in the
two characteristic ways of Horn A: the min collapses, the max is blind to easiness. This is the horn the observer
thread was implicitly on, and it is closed.

### Horn B — inf over representations (circular)

`I` is a complexity measure defined as an infimum over computations: circuit size, formula size, branching-program
size, time-bounded Kolmogorov complexity `K^t`. These are trivially representation-invariant (the inf ranges over
all representations) and approximately padding-invariant. But `I` here **is the complexity** — lower-bounding it
is verbatim the separation we want. Worse, the `inf` reintroduces the universal quantifier over representations
that the observer thread could not discharge: this is precisely the **machine-completeness bridge** named as the
decisive open step in `SCOPE_OBSERVER_BOUNDARY_THREAD.md §3`. Making the invariant intrinsic by taking an inf does
not remove that quantifier — it *is* that quantifier.

## 3. The barriers that enforce the dichotomy

The dichotomy is not an accident of these examples; three known barriers pin it in place.

* **Natural proofs (Razborov–Rudich).** A Horn-A invariant with a hardness threshold (`I(f) > t ⇒ f` hard) is a
  combinatorial property `Φ_t`. Intrinsic combinatorial measures are **constructive** (computable from the
  `2^n`-bit truth table in time `2^{O(n)}`) and **large** (hold for random `f`). If such a property were
  **useful** (implied super-polynomial circuit lower bounds) it would break sub-exponential pseudorandom function
  generators. So a *useful* intrinsic invariant is barred — unless it is **non-constructive** or **non-large**.
  Non-large means SAT-specific, which discards the "invariant" generality and re-opens machine-completeness.
  Non-constructive means either Horn B (the inf, circular) or the one genuine escape (§5).
* **Circularity.** Horn B is the complexity itself; "prove `I` is large on SAT" is the problem restated.
* **Relativization / padding (Baker–Gill–Solovay).** Padding-invariance is a syntactic, oracle-blind condition,
  and the Horn-A measures that satisfy it (local counting / sensitivity-type) are exactly the ones that
  relativize. A relativizing invariant cannot separate P from NP. This is the softer of the three links — padding-
  invariance does not *formally* imply relativization — but empirically the padding-invariant intrinsic measures
  are the relativizing ones.

## 4. Padding-invariance is a double-edged requirement

There are two padding-invariances, and the thread wanted the first while the dichotomy delivers the second:

* **benign:** *do not be inflated by content-free padding* (reject the false signal that fooled the canonical
  query scheme). Desirable.
* **fatal:** *be blind to the amount of computation.* Since padding adds computation/length without changing
  membership structure, a robustly padding-invariant invariant cannot see the very resource (time/size) whose
  growth separates P from NP.

Complexity **is** resource usage; an invariant defined to ignore added resources is structurally unable to
measure the separating quantity unless it re-normalizes "resource per bit of genuine information" — which is a
disguised inf over representations, i.e. Horn B. So the clean version of the requirement is self-limiting.

## 5. The one path that dodges every known barrier — GCT

There is exactly one program that produces a representation-invariant-by-definition invariant which is
**non-constructive** (evading natural proofs) and **non-relativizing** (algebraic-geometric, oracle-free):
**Geometric Complexity Theory** (Mulmuley–Sohoni). It measures complexity by orbit-closure containment and
separates via representation-theoretic *obstructions* in the coordinate rings — invariants defined intrinsically
by the symmetry group of the function, computed via plethysm/Kronecker coefficients (which are `#P`-hard, hence
non-constructive). This is genuinely the "invariant that is representation-invariant by definition and dodges the
barriers."

Its status is the reason this is not an easier road:

* GCT is for **algebraic** complexity (VP vs VNP / permanent vs determinant), not Boolean P vs NP directly.
* The concrete **occurrence-obstruction** instantiation was **proven insufficient** (Bürgisser–Ikenmeyer–Panova,
  2016: no occurrence obstructions separate padded permanent from determinant).
* The surviving **multiplicity-obstruction** version is open but with **no known construction**, further
  limitation results (Ikenmeyer–Panova and others), and coefficients that are `#P`-hard to even compute.

So the one non-barriered path relocates P vs NP onto GCT's multiplicity-obstruction problem — itself a decades-old,
deeply stuck program with its own no-go theorems. The `border rank / GCT` angle is already logged as a dead angle
for the N-frame arc; this scope confirms why at the level of the whole "intrinsic invariant" idea.

## 6. Verdict and recommendation

A representation/padding-invariant-by-definition invariant that separates P from NP is:

1. an **intrinsic function property** — poly-bounded / collapsing (Horn A; our `unrestricted_min_trivial` and
   `eqFun_dim_ge` are machine-checked instances), barred from usefulness by **natural proofs**; or
2. an **inf over representations** — **circular**, and identical to the machine-completeness bridge; or
3. a **GCT multiplicity obstruction** — the only barrier-free path, but algebraic rather than Boolean, with its
   occurrence version proven dead and its multiplicity version stuck and `#P`-hard.

**This direction does not make P vs NP easier.** It is not a fresh attack; it maps onto GCT (or onto the natural-
proofs / circularity barriers). No new Lean artifact is warranted — the assessment is meta-mathematical, and its
two concrete horns are *already* formalized (`unrestricted_min_trivial`, `eqFun_dim_ge`).

Honest recommendation: do **not** pursue this as a route to separation. The productive continuations remain the
ones from the observer-thread scope: keep proving **restricted-model** lower bounds (the Nečiporuk × BP-width
matrix is complete and clean-axiom), presented as such. If GCT is of interest, the only *buildable* honest target
is formalizing a **known** representation-theoretic fact (e.g. a small occurrence/multiplicity computation), never
a separation. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
