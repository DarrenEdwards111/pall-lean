# Attempt: irreversible information loss as observer energy

2026-09-08. Not Lean verified; no P versus NP separation.

## Candidate

Replace raw entanglement rank by information irreversibly erased over the decider's execution. Test whether a decider without a witness must erase superpolynomially many bits while a witness-bearing verifier need not.

## Construction and obstruction

For any finite NAND circuit C of s gates computing f, allocate one zero ancilla per gate. Replace each gate by target ^= NAND(a,b), leaving its controls unchanged. This map is reversible: applying it twice restores the target. It has a constant-size reversible-gate implementation (NOT and Toffoli; repeated controls can be simplified). After all gates, XOR the answer into a separate output bit z; reverse all computation gates. The total map on initialized workspace is

    (x, 0^s, z) -> (x, 0^s, z XOR f(x)).

There are 2s lifted-gate uses plus one answer copy. No logical erasure occurs: both input and output are retained, and workspace is restored reversibly. This is not a claim that f has small s. If a polynomial-time decider existed, standard polynomial-overhead circuit simulation followed by this construction would not force superpolynomial erasure. Bennett's uniform reversible machine construction gives the same qualitative conclusion without treating an arbitrary function oracle as one cheap step.

This construction can stay inside the decider's own observer boundary; the verifier and its witness are not used. A boundary rule excluding polynomial temporary workspace would require justification if the theorem is to cover ordinary polynomial-time computation.

The finite check covers all 36 two-gate NAND wiring choices and all 8 input/output-bit initializations, 288 cases. It checks restoration of ancillas and preservation of input. It is not a formal general proof or a physical heat simulation.

## Important limit

Logical reversibility does not imply a real finite-speed device emits zero heat. Noise, reliability, control and storage may incur physical costs. Those require an explicit physical model and do not follow as a superpolynomial runtime bound from logical erasure alone. Nor is a reusable clean workspace available for free physically; the resource requirement here is only polynomial when s is polynomial.

## Attempted repair: accumulated activity

Charging all reversible operations or history storage avoids the zero-erasure example, but then proving an unavoidable superpolynomial charge requires a lower bound on operations or necessary space-time. One cannot infer it from the number of candidate witnesses. An algorithm may retain the input and uncompute its internal history, without ever receiving the NP observer's witness.

## Independent information check

For a deterministic halting machine M on a random n-bit input X, its entire trace tau(X) is a deterministic function of X. Consequently H(tau(X)|X)=0 and H(tau(X)) <= H(X) <= n, irrespective of trace length. This does not make computing tau cheap. It means Shannon uncertainty and time to generate a trace are different quantities. Summing marginal entropies over time also counts repeated copies repeatedly and is not automatically fresh information or dissipated heat.

## Sources

C. H. Bennett, Logical Reversibility of Computation (1973):
https://www.cs.princeton.edu/courses/archive/fall04/cos576/papers/bennett73.html

Outcome: irreversible bit loss and ordinary trace entropy do not supply the missing universal lower bound. A different execution-sensitive cost plus a SAT necessity theorem is still required.
