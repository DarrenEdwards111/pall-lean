import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0IKWNisanWigderson

/-!
# DerandKarpLiptonSeparation — the Karp–Lipton collapse chain (composition glue proved)

Entry 189 left **`DerandKarpLiptonSeparation`** (`Derandomization → ¬ (NEXP ⊆ ACC⁰)`: a derandomisation collapses to the
separation) as a sub-socket of the IKW chain.  This file opens it up into the classical **Karp–Lipton collapse chain**
and proves the composition glue.

The chain (Babai–Fortnow–Lund / Impagliazzo–Kabanets–Wigderson + derandomisation + the hierarchy):

1. **Karp–Lipton collapse**: `NEXP ⊆ ACC⁰ ⟹ NEXP = MA` — if `NEXP` has small circuits, the doubly-exponential
   guess-and-verify collapses `NEXP` into `MA` (the deep BFL/IKW collapse).
2. **Derandomisation collapses `MA`**: a derandomisation (a PRG defeating the relevant class) gives `MA = NP` — Arthur's
   coins are simulated nondeterministically.
3. **Nondeterministic time hierarchy**: `NEXP ≠ NP`.

Composing: `NEXP ⊆ ACC⁰ ⟹ NEXP = MA = NP`, contradicting `NEXP ≠ NP`.  Hence a derandomisation makes `NEXP ⊆ ACC⁰`
contradictory — exactly `DerandKarpLiptonSeparation`.

## What is proved (clean axioms, no `sorry`)

* **`KarpLiptonCollapse NEXP ACC0 MA := NEXP ⊆ ACC0 → NEXP = MA`** — the Karp–Lipton/BFL collapse (named socket).
* **`DerandCollapsesMAtoNP Derandomization MA NP := Derandomization → MA = NP`** — the derandomisation collapse (named
  socket).
* **`NexpNeqNp NEXP NP := NEXP ≠ NP`** — the nondeterministic time hierarchy (named socket).
* **`derandKarpLipton_discharge`** — the composition glue, **proved**: the three sub-sockets ⇒ the entry-189
  `DerandKarpLiptonSeparation` socket, by `fun hd hsub => hier ((kl hsub).trans (derand hd))`.

## Honest scope

This decomposes `DerandKarpLiptonSeparation` into the three genuine classical ingredients — the **Karp–Lipton/BFL
collapse** (`NEXP ⊆ ACC⁰ ⟹ NEXP = MA`), the **derandomisation collapse** (`MA = NP`), and the **nondeterministic time
hierarchy** (`NEXP ≠ NP`) — and proves the *composition glue* (transitivity of the collapses contradicts the
hierarchy).  The three ingredients remain named sub-sockets, each a proven classical theorem requiring complexity-theory
infrastructure (the doubly-exponential guess-verify, the hardness–randomness tradeoff, the diagonalisation hierarchy)
absent here.  This proves the *logical composition* of the Karp–Lipton route, not the ingredients.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonCollapse

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0IKWNisanWigderson (DerandKarpLiptonSeparation)

/-- **The Karp–Lipton / BFL collapse socket.**  If `NEXP` has small (`ACC⁰`) circuits, then `NEXP = MA` — the
doubly-exponential guess-and-verify collapses `NEXP` into Merlin–Arthur (Babai–Fortnow–Lund, Impagliazzo–Kabanets–
Wigderson).  Stated, not proved. -/
def KarpLiptonCollapse (NEXP ACC0 MA : CClass) : Prop := NEXP ⊆ ACC0 → NEXP = MA

/-- **The derandomisation collapse socket.**  A derandomisation (a PRG defeating the relevant class) collapses
`MA = NP` — Arthur's random coins are simulated by nondeterministic guessing.  Stated, not proved. -/
def DerandCollapsesMAtoNP (Derandomization : Prop) (MA NP : CClass) : Prop := Derandomization → MA = NP

/-- **The nondeterministic time hierarchy socket.**  `NEXP ≠ NP` — diagonalisation separates nondeterministic
exponential from nondeterministic polynomial time.  Stated, not proved. -/
def NexpNeqNp (NEXP NP : CClass) : Prop := NEXP ≠ NP

/-- **The Karp–Lipton composition glue (PROVED).**  The three ingredients compose to the entry-189
`DerandKarpLiptonSeparation` socket: a derandomisation `hd` and a circuit hypothesis `hsub : NEXP ⊆ ACC⁰` give
`NEXP = MA` (Karp–Lipton) and `MA = NP` (derandomisation), so `NEXP = NP` by transitivity, contradicting the hierarchy
`NEXP ≠ NP`.  Hence the derandomisation refutes `NEXP ⊆ ACC⁰`. -/
theorem derandKarpLipton_discharge (NEXP ACC0 MA NP : CClass) (Derandomization : Prop)
    (kl : KarpLiptonCollapse NEXP ACC0 MA)
    (derand : DerandCollapsesMAtoNP Derandomization MA NP)
    (hier : NexpNeqNp NEXP NP) :
    DerandKarpLiptonSeparation NEXP ACC0 Derandomization :=
  fun hd hsub => hier ((kl hsub).trans (derand hd))

end PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonCollapse.derandKarpLipton_discharge
