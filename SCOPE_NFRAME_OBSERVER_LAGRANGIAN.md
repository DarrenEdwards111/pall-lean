# The N-Frame Lagrangian as a route-selector for the observer programme

**Status: a research *compass*, not a proof.**  This document does not prove anything and claims no progress
on `P ≠ NP`.  It uses the *structure* of the N-Frame Lagrangian `S_NF` (a real functional in this repo) as a
**least-action prioritiser**: it scores the candidate God-Move attack routes by an action and reads off the
least-action path.  The scores are *ordinal/qualitative* (a ranking), each tied to a proved result or a proved
barrier so the ranking is grounded, not arbitrary.

---

## 1. The real N-Frame Lagrangian (grounded)

In the repo (`PathB/EulerLagrangeStationarity.lean`, `NFrame/AlphaCoercivityBound.lean`,
`NFrame/EulerLagrangeAlpha.lean`) the N-Frame action over a field configuration `Φ` on a graph `G` is

```
S_NF[Φ]  =  α · ⟨Φ, L_G Φ⟩        (kinetic / smoothness — graph Laplacian L_G)
          + β · χ · (sgn-coupling) (parity / continuation distinction)
          + λ · barrier(Φ)         (logdet feasibility barrier)
```

with the Euler–Lagrange stationarity `δ_Φ S_NF = 0`, proved (α-term) as
`α · L_G Φ = (β/2) · χ · ∂sgn(Φ)` (`kineticTerm_gradient_eq_laplacian_action`,
`S_NF_EL_reduces_to_alpha_min_Kn`).  On a **Ramanujan/expander** `G` the kinetic operator `L_G` has a large
spectral gap — *smooth* (globally consistent) configurations are cheap, *locally-cheating* ones are expensive.
That is the amplification structure we reuse below.

## 2. The route-selection action (by analogy)

Map a *route* (an attack on the separation) to a configuration, and define its **boundary action**

```
S(route)  =  α·𝐁(route)          boundary cost     (kinetic — must control boundary entropy)
          +  β·𝐃(route)          decomposition freedom penalty (parity/continuation coupling)
          +  λ·𝐄(route)          approximation error (barrier — penalises infeasible bridges)
          −     𝐀(route)          expander amplification gain (spectral-gap credit)
```

| term | observer meaning | grounded in |
|---|---|---|
| `𝐁` boundary cost | how much boundary entropy the route must force/control | `boundaryEntropy`, the rungs §II of the capstone |
| `𝐃` decomposition freedom | how much the adversary's choice of decomposition fights you | `equality_decomposition_gap` (the gap is the penalty) |
| `𝐄` approximation error | feasibility of the polynomial/representation bridge | exact-enriched failure, approx-bridge §6 ACC⁰ note |
| `𝐀` amplification gain | spectral-gap credit: expander forces high boundary *cheaply* | expander-Tseitin `c·t`, `ForcingFamily` |

**Least action `S` = most promising route.**  The Lagrangian's lesson, transported: a route is cheap exactly
when the expander amplification (`−𝐀`) pays for the boundary cost (`+α𝐁`) while the decomposition-freedom and
approximation penalties (`β𝐃`, `λ𝐄`) stay finite — i.e. when `L_G`'s spectral gap does the work and `sgn`/`barrier`
don't blow up.

## 3. Scoring the current routes

| route | `α𝐁` | `β𝐃` | `λ𝐄` | `−𝐀` | **action `S`** | evidence |
|---|---|---|---|---|---|---|
| **1. All-decompositions SAT LB** | huge | **huge** (every decomposition) | low | partial | **very high** | `= CookLevinFrontierHyp`, open |
| **2. ACC⁰ mixed-moduli bridge** | high | medium | **huge** (cross-modulus) | low | **high** | `JointModularBarrier`: proved blocked |
| **3. Structured forcing families** | medium | **low** (class controlled) | low | **high** (expander pays) | **low** | `ForcingFamily`, Tseitin `c·t` — *proofs already work* |
| **4. Observer→DP→Williams** | low (low-boundary side) | low | medium | medium | **medium** | engine 1 proved; Williams isolated |

The decisive terms:

* Route 1's `β𝐃` is maximal — the decomposition-freedom penalty *is* the open quantifier; the expander credit
  `−𝐀` only partially offsets it (it pays on *structured* classes, not all).
* Route 2's `λ𝐄` is maximal — the cross-modulus approximation barrier is the proved obstruction
  (`mod_q_indicators_false` *is* the barrier).
* Route 3 has every penalty controlled and the amplification credit large (the expander Laplacian's gap is
  exactly the `ForcingFamily` "pay-the-frontier" mechanism) — **least action**.
* Route 4 is feasible (engine 1 proved) but its Williams term is deep; medium action, conceptually valuable.

## 4. The least-action path

```
structured forcing families  →  expander-amplified structured classes  →  observer-to-DP algorithmic schema
        (route 3)                         (route 3 + 𝐀)                          (route 4)
```

Read off the action: **start where `S` is lowest (route 3), spend the expander credit to enlarge the
structured class without raising `β𝐃` (route 3 + amplification), then cash the resulting low-boundary
structure into the algorithmic engine (route 4)** — rather than paying route 1's `β𝐃` or route 2's `λ𝐄`
up front.

Concretely, the next *productive* moves the action ranks (all in the regime where proofs work):

1. **New forcing families** (lower `α𝐁`, controlled `β𝐃`): instantiate `ForcingFamily` for PHP / pebbling
   proof-space, or for a constrained branching-program order — each a proved `min` lower bound in a new
   structured class.
2. **Expander-amplify a forcing family** (spend `−𝐀`): show the expander Laplacian's spectral gap *enlarges*
   the address-respecting class for which `min` stays super-log, narrowing the gap to all-decompositions
   without crossing it.
3. **Feed the structured low-boundary structure to engine 1** (route 4): a genuinely structured (not trivial)
   `LowBoundaryInstance` from a forcing-family-adjacent decomposition, then the conditional Williams chain.

## 5. Honest status

* This is a **prioritiser**, not a theorem.  The action is qualitative; it ranks attacks by tying each
  Lagrangian term to a proved result (`−𝐀`, low `β𝐃` on structured classes) or a proved barrier (`λ𝐄` for
  ACC⁰, `β𝐃` for all-decompositions).
* It does **not** lower the action of route 1 (`P ≠ NP`) or route 2 (`NP ⊄ ACC⁰`): the open quantifier and the
  cross-modulus barrier remain exactly as costly as the proofs/barriers say.
* Its recommendation matches the capstone's honest read: **stay in the structured-`min` regime, use the
  expander as the amplifier, and treat the algorithmic engine as the cash-out** — least action, all on proved
  ground, with the open quantifier left untouched and clearly the most expensive route.
