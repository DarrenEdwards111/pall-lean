# Exact circuit budget of three-bit majority

## Result

The file
[`PallLean/Paper93/DeepMath/PathB/ComputationalDepthMajoritySemanticBoundary.lean`](PallLean/Paper93/DeepMath/PathB/ComputationalDepthMajoritySemanticBoundary.lean)
proves:

```lean
theorem majorityThreeFloor_cbudget_eq_seven :
    cbudget majorityThreeFloor = 7
```

Here `majorityThreeFloor` is the Boolean majority function on three inputs and
`cbudget` is the minimum length of a `CGate` circuit computing it.  A `CGate`
wire is either an input coordinate or an arbitrary binary Boolean operation on
two distinct earlier wires.  Thus the result is not restricted to a named
basis such as AND/OR/NOT.

## What is proved

- A seven-wire `CGate` circuit computes three-bit majority.
- No six-wire `CGate` circuit computes three-bit majority.
- Consequently the exact minimum circuit length is seven.

The lower bound is semantic: it applies to all 16 possible binary Boolean
operations at each genuine binary transition, rather than merely to a fixed
gate basis.

## Proof architecture

1. Normalize a hypothetical six-wire majority circuit.
2. Prove it has three variable wires and exactly three genuine binary wires.
3. Extract the three binary wires in chronological order.
4. Compress their sources into `Fin 3`, `Fin 4`, and `Fin 5` semantic indices.
5. Transport circuit liveness and exact wire values into a
   `SixCircuitSemanticScheduleCertificate`.
6. Exclude every live three-transition schedule with
   `liveThreeTransition_semantic_exclusion`.
7. Combine the six-wire exclusion with the explicit seven-wire upper bound.

The final concrete transport theorem is:

```lean
theorem majoritySixSemanticScheduleExtractor_proved :
    MajoritySixSemanticScheduleExtractor
```

It discharges the previously isolated circuit-to-semantic-boundary adapter;
the exact-budget theorem is therefore unconditional within the definitions of
the formalized model.

## Kernel and axiom audit

The source ends with:

```lean
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.liveThreeTransition_semantic_exclusion
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majorityThreeFloor_cbudget_eq_seven
```

The reported dependencies are only Lean/mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound`.  The proof uses no `sorry`,
custom axiom, `native_decide`, `bv_decide`, `Lean.ofReduceBool`, or
`Lean.trustCompiler`.

## Reproduce

From the repository root:

```bash
lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthMajoritySemanticBoundary.lean
```

For the complete library build:

```bash
lake build
```

## Scope

This is an exact lower bound for one explicit three-variable Boolean function
in the repository's unrestricted-binary-operation, earlier-wire `CGate` model.
It does not by itself assert a lower bound for general circuits, larger
majority functions, or a standard gate-count convention that omits input
wires.  Those require separate translations or generalizations.
