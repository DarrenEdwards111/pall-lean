# Circuit gluing, interface separation, and projector application

2026-09-11. Continuation of `50052e57`, investigating the proposed idea of
circuits being joined through shared wires and then separated.

There is now an executable, proved circuit-gluing operation and an exact
factorization of its response through its computed interface bits. There is
also a compact application formula for the unchanged production projector
on separated affine products and the designated quadratic sheet. These are
concrete construction results. They do not establish SAT separation.

## Joining actual circuits without copying shared computations

`GodMoveCircuitGluing.glue` takes a left gate list, a list of selected left
output ports, and a right gate list. The right circuit's inputs consist of
those port bits and its own independent input variables.

The compiler retains the left circuit once. Each right-side port input
becomes an identity gate reading the existing left wire; internal right
wire references are offset by the left gate count. Repeated ports are legal.
The result has exactly

```
length(glue left ports right) = length(left) + length(right).
```

The complete wire-trace identity and final-output identity are derived from
the existing `CGate` evaluator. Forward and out-of-range references retain
its default-false behavior; the theorem does not silently impose a new
well-formedness condition. The final-output theorem requires a nonempty
right circuit, since otherwise the combined circuit's last wire belongs to
the left circuit. The complete trace identity has no such restriction.

This constructs the specified one-way composition. It does not discover a
small balanced cut for every arbitrary circuit or establish such a cut for
every SAT computation.

## What separating the interface actually costs

If the left side supplies `r` Boolean bits, its interface has up to `2^r`
joint states. For a left input `x` and right input `y`, Lean proves

```
response(x,y) = Σ_s [ports(x)=s] · finish(s,y).
```

The sum ranges over `r`-bit states. `GodMoveGluedCircuitRank` derives this
factorization from the output of the compiled glued circuit; it does not
assume a matrix factorization unrelated to computation. Consequently,

```
rank(response) ≤ 2^r.
```

The same circuit also factors through the complete left wire trace, giving
`rank(response) ≤ 2^(length(left))` even with repeated ports. The compiler
does not enumerate either set of joint states; those expansions describe
the response matrix algebraically.

A `q`-dimensional response minor therefore forces `ceil(log₂ q) ≤ r` by
this argument. It does not force `q ≤ r`. Conversely, a proved interface
bound `r ≤ c log₂ n` gives `rank(response) ≤ n^c` for positive `n`.
Establishing the logarithmic interface bound is a substantive requirement.

The exponential ceiling is sharp. `GodMoveEqualityCircuit` uses the
existing verified binary-gate compiler to build equality of two `r`-bit
strings with exactly `4r+1` gates. Its actual output matrix is the
`2^r × 2^r` identity. The module proves that its rank exceeds every eventual
polynomial in that circuit's gate count. Thus even a small fixed gate
library and bounded fan-in do not give polynomial response rank across an
arbitrary displayed input split.

This response rank is a calibration of the circuit-cut argument. It is not
identified with, or substituted for, the production N-Frame invariant.

## Applying the actual projector to separated factors

For

```
p(X) = ∏_i (a_i + b_i X_i),
```

the complemented coefficient read by the production projector factors
coordinate by coordinate. This follows from the proved disjoint-support
coefficient theorem, not from an assumed rank bound. It gives

```
J_k p = [z^k] ∏_i (-b_i(1-X_i) + z(a_i+b_i)(2X_i-1)).
```

The existing shared coefficient DAG computes this expression. The new
output descriptor stores its rational input factors explicitly, with
`16m` factor nodes and `2+3m(k+1)` recurrence nodes. Its denotation equals
`(boundaryGauge m k).projection p`; a general coefficient-contraction
oracle is not an input to the constructor.

For the actual designated sheet

```
Q(X) = ∏_i (1-X_i+X_i²),
```

the local complemented coefficients at degrees zero and one are exactly
those of the unit monomial's complement. Hence

```
J_k Q = J_k (∏_i X_i).
```

The same output descriptor therefore applies directly to this sheet.
This uses coefficient identities in the full polynomial ring; it does not
normalize `Q` on the Boolean cube and lose the sheet's structure.
The output here is `J_k Q`; it need not equal `Q`. The application theorem
does not assert global SPDP-rank monotonicity. Its production-target wrapper
uses the existing sheet identity under the stated machine, size, and partition
hypotheses, including `D.timeBound ≤ 4` and `D.numStates ≤ n`.

These bounds concern a compact output representation, not its expanded
coefficients or a bit-level machine clock. Supplied rational coefficients
have their own encoding lengths. The degree recurrence retains shared
registers; the separate-factor coefficient identity requires distinct
variable supports. Reusing the same variable in two multiplicative factors
introduces coefficient convolution and does not satisfy that premise.

Restricted tractability under decomposability is also familiar in Boolean
knowledge compilation. Darwiche's [model-counting paper](https://arxiv.org/abs/cs/0003044)
gives efficient operations for deterministic DNNF. It supplies no claim of
polynomial-size compilation of every SAT instance into the needed restricted
form. The Lean result here is the narrower explicit polynomial-product
application above, not a formalization of that general literature.

## The unresolved step in the paper's gluing argument

The local paper `p-vs-np1.pdf`, pp.195–196, Theorem 203, glues local gadgets
and asserts a logarithmic interface bound before invoking Width⇒Rank.
The new circuit-cut theorem makes the quantitative need explicit: `r`
Boolean wires give an exponential state factor, and a logarithmic bound
on the relevant `r` would be sufficient for polynomial response rank.
Locality alone does not supply that bound or a matching N-Frame extraction.

On pp.201–202, Lemmas 213–214 count interface-anonymous profiles and use that
count for SPDP admissibility. Counting type histograms does not by itself
prove that differently labelled derivative rows lie in a small common
linear space. A valid identification and span bound are still required.

The existing `RuntimeFaithfulGodMoveFrame` stores the injection from
transported challenges into distinct live runtime slots as a field.
`GlobalGodMoveLiveBoundaryBridge` likewise leaves universal live-minor
extraction as a premise. The actual gluing proof above does not discharge
either premise.

The designated projector is now applicable in compact form to the explicit
separated family, including `Q`. What remains is a runtime-controlled
construction for the actual SAT source, with the required hard structure
preserved by that construction. The existing source-specific extraction
and lower bound do not supply its missing runtime upper bound.

## Verification

The full source-matched audit passed on Lean 4.28.0: **109 modules,
528 source-closure files, 870 printed axiom checks, zero warnings**.
The only reported axioms were `propext`, `Classical.choice`, and `Quot.sound`.
The six new modules account for 47 checks. The command was:

```
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/glued-circuit-checks
```

The local `results.json` records `all_passed: true`; individual module logs
contain the axiom traces. No production definitions are changed.
