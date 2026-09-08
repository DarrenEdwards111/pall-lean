# Witness-cut and postselection attempt (2026-09-08)

Status: mathematical derivations with exhaustive finite CNF checks; NOT Lean verified. No separation proved.

## 1. A different cut: the normalized satisfying-witness state

Let F_n(x,y) = AND_i [(NOT x_i OR y_i) AND (x_i OR NOT y_i)].
It has 2n variables and 2n clauses and accepts exactly x=y. Thus its normalized satisfying state is

    |S_F> = 2^(-n/2) SUM_x |x>_A |x>_B.

The coefficient matrix is I/sqrt(2^n). Its Schmidt rank is 2^n, and its reduced density matrix is I/2^n, with entropy n bits. This is a witness/witness cut, not the previously tested witness/answer cut.

Nevertheless the formula is visibly satisfiable (all zero suffices); verification takes O(n) literal operations, polynomial also under explicit indexed encoding. High satisfying-state entanglement is not a pointwise lower bound on SAT decision time. This does not rule out a worst-case lower bound on a different hard family.

## 2. Postselection probability is preparation-protocol dependent

Projecting the uniform superposition of all 2n-bit strings onto satisfying assignments succeeds with probability 2^(-n). Independent repetition of this particular protocol takes 2^n trials in expectation. But n Hadamards followed by n pairwise CNOTs prepare the same state deterministically. Thus reciprocal postselection probability is not an unavoidable state-preparation cost either.

The direct preparation uses gates across A/B. If separate observers prohibit these gates, it is not an allowed local-only preparation. The classical SAT decision shortcut still applies: an ordinary decider need not prepare this state at all. A reduction establishing that every decider must implement the restricted task is required.

## 3. Dynamic log-rank, rather than raw rank

For a pure state of Schmidt rank R across a fixed cut and an operator U = SUM_{j=1}^s A_j tensor B_j, applying U gives at most sR product terms, hence R(U psi) <= s R(psi). If U is unitary, its inverse has a decomposition with the same number s, so R(psi) <= s R(U psi). Therefore |log2 R(U psi) - log2 R(psi)| <= log2 s.

A gate on one qubit on each side has s <= 4 (expand in the four matrix units on the first qubit); a local unitary preserves rank. Thus G cross-cut two-qubit gates starting from a product state imply log2 R_final <= 2G. For the equality state this yields G >= n/2, only linear; the n-CNOT construction matches up to a factor two. This does NOT posit an additive small change of raw rank.

More generally a pure state of q explicit qubits has log2 R <= min(q_A,q_B) <= q/2. A superpolynomial pointwise log-rank lower bound cannot occur in polynomially many explicit qubits. Accumulated rank variation could be larger, but proving unavoidable superpolynomial variation is a new time lower bound, not implied by final-state rank.

## 4. Remaining positive research target

An algorithm-independent reduction from correct SAT decision to a precisely specified restricted boundary process, together with a SAT-specific lower bound on that process, remains absent. Separate thermodynamic boundaries, postselection rarity, and high final entanglement do not establish this reduction.

Background: Jozsa and Linden, https://arxiv.org/abs/quant-ph/0201143, distinguish necessary entanglement conditions for pure-state quantum speedup from a sufficient characterization of computational power. The explicit examples and operator-rank calculation above are supplied here, not claimed as new literature results.

check.py exhaustively verifies the CNF truth table for n=1..8 and records the exact analytic spectrum consequences. It does not test unrestricted algorithms or constitute a formal Lean proof.
