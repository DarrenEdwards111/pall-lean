# Lifting Theorem Outline — From Residual Explosion to Computation Lower Bounds

## The Current Theorem (What We Have)

**Proved (0 sorry):** For Tseitin formulas on d-regular ε-edge-expanders:

```
∀ C, ∃ n₀, ∀ n ≥ n₀, OBDD_width(T(G_n)) > n^C
```

The engine: at any good cut k, there are ≥ 2^c distinct residual functions
(c = Ω(n/d²)), forcing OBDD width ≥ 2^c.

## The Problem

This is an **OBDD** lower bound (ordered, read-once branching program).
But poly-time TMs don't produce OBDDs — they produce general branching programs.

- P ⊆ poly-size general BPs (trivially, from TM simulation)
- Tseitin satisfiability ∈ P (check parity sum, linear time)
- So Tseitin HAS poly-size general BPs
- The exponential OBDD lower bound doesn't contradict this

**The gap = L vs P.** Logspace ↔ poly-width BPs. Our lower bound lives in OBDD-world.

## The Lifting Strategy

### Key Observation
Our residual explosion is really a **communication complexity** lower bound in disguise.

Split variables at cut k into Alice's (edges 0..k-1) and Bob's (edges k..m-1).
After Alice fixes her variables, Bob sees one of 2^c distinct residual functions.
Any deterministic communication protocol needs ≥ c bits.

**This is already a partition communication complexity lower bound.**

### What Lifting Buys Us

**Göös–Pitassi–Watson (2015):**
For search problem S and index gadget IND_n:
```
det-cc(S ∘ IND_n) ≥ Ω(query_depth(S) · log n)
```

**Translation:** If S has high query complexity, then S composed with a gadget
has high communication complexity, which implies large dag-like proof complexity
and large branching program SIZE (not just width).

### The Concrete Plan

#### Step 1: Define the Tseitin Search Problem

```
SEARCH-TSEITIN(G, t):
  Input: edge labeling x ∈ {0,1}^m
  Output: a vertex v where parity constraint is violated
          (i.e., ⊕_{e incident to v} x_e ≠ t_v)
  Promise: total parity is odd (so violation exists)
```

This is a **total search problem** (TFNP) — a solution always exists.

#### Step 2: Establish Query Lower Bound

**Claim:** Any deterministic decision tree for SEARCH-TSEITIN on expander G
must have depth Ω(m).

**Why:** To find the violated vertex, you must distinguish which vertex is violated.
On an expander, vertices are "locally similar" — each has degree d, each
participates in similar parity constraints. Without reading Ω(m) edge labels,
you can't distinguish between two vertices that share no edges.

*This needs formalization, but should follow from expansion properties.*

**Alternative (stronger):** Use the **residual counting** we already have.
After querying q variables, at most 2^q distinct states are reachable.
But there are 2^c distinct residuals at any balanced cut.
So q ≥ c = Ω(n/d²) queries are needed.

#### Step 3: Lift via Gadget Composition

Define the lifted problem:
```
LIFTED-TSEITIN = SEARCH-TSEITIN ∘ IND_n
```

Each of the m edge variables x_i is replaced by a gadget:
- Alice gets a pointer p_i ∈ [n]
- Bob gets a string y_i ∈ {0,1}^n
- The "true" value of edge i is y_i[p_i]

**Lifting theorem gives:**
```
det-cc(LIFTED-TSEITIN) ≥ Ω(c · log n) = Ω(n · log n / d²)
```

#### Step 4: From Communication Complexity to Computation

**Known connections:**
1. **cc → proof size:** High cc for search version of unsatisfiable formula
   → large tree-like resolution proofs (Ben-Sasson, Wigderson)
2. **cc → BP size:** Via Karchmer-Wigderson games,
   cc lower bounds → circuit depth lower bounds → BP lower bounds
3. **Dag-like cc → dag-like resolution:** Göös-Pitassi-Watson showed
   lifted cc lower bounds give dag-like resolution lower bounds

**What this gives for Tseitin:**
- Tree-like resolution lower bound: **already known** (Ben-Sasson, Wigderson 1999)
- Dag-like resolution lower bound for lifted Tseitin: **follows from GPW**
- General BP lower bound: **requires additional argument**

## The Honest Assessment

### What Works
- Residual explosion → partition cc lower bound: **DONE** (follows from our theorems)
- Query lower bound for SEARCH-TSEITIN: **very plausible**, follows from expansion
- Lifting to high cc for composed problem: **follows from GPW machinery**
- Proof complexity lower bounds: **achievable**

### Where the Barrier Is
- General BP lower bound for an NP function: **major open problem**
  - Best known: Nečiporuk's n²/log²n for explicit functions
  - Our method gives exponential OBDD bounds but NOT general BP bounds
  - Tseitin is in P, so it has poly-size general BPs — no contradiction possible
  
- The fundamental issue: **the lift changes the problem**
  - SEARCH-TSEITIN is in P (easy to solve)
  - LIFTED-SEARCH-TSEITIN is harder (high cc)
  - But we need the UNLIFTED problem to be hard for BPs
  - Lifting adds artificial structure that creates hardness

### The Path That Could Work

**Option A: Lift an NP-complete search problem**
Instead of Tseitin (which is in P), use an NP-complete problem that has
similar residual explosion properties. If such a problem exists and has
high query complexity, then:
- Lifting gives high cc
- High cc gives proof complexity lower bounds  
- Proof complexity separations are genuine contributions

**Option B: Use the method for proof complexity, not circuit complexity**
Tseitin + lifting already gives:
```
Dag-like resolution proofs of Tseitin(G) ∘ IND require size 2^{Ω(n log n)}
```
This is a genuine (already known) result. Our framework REPROVES it
with cleaner machinery.

**Option C: Target a restricted computation model between OBDD and general BP**
- Syntactic read-k BPs (each variable read at most k times)
- Oblivious BPs (fixed variable ordering, but re-reads allowed)
- Nondeterministic BPs
Our residual method may extend to some of these with additional work.

## Recommended Next Steps

1. **Formalize the partition cc lower bound** — this is almost free from existing theorems.
   Just restate: 2^c residuals → cc ≥ c for the natural partition.

2. **Prove the query lower bound for SEARCH-TSEITIN** — decision tree depth ≥ c.
   This should follow from: after querying q < c variables, two inputs exist
   that agree on queried variables but have violations at different vertices.

3. **State the lifted lower bound** — even if we don't formalize GPW itself,
   stating the theorem with GPW as a cited result is valuable.

4. **Identify which NP-complete problems have residual explosion** —
   this is the key research question. Candidates:
   - Graph coloring (on expanders)
   - Clique/independent set
   - Subset sum variants

## Key References

- Göös, Pitassi, Watson (2015): "Deterministic Communication vs Partition Number"
- Göös, Pitassi, Watson (2018): "Query-to-Communication Lifting for BPP"  
- Razborov (2003): "Resolution Lower Bounds for the Weak Pigeonhole Principle"
- Ben-Sasson, Wigderson (1999): "Short Proofs are Narrow — Resolution Made Simple"
- Jukna (2012): "Boolean Function Complexity" (branching program hierarchy)
- Nečiporuk (1966): "On a Boolean function" (BP size lower bounds)
