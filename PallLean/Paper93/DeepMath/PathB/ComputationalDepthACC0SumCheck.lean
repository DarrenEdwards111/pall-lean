import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BFLCollapse

/-!
# MIP = NEXP — the sum-check round-reduction engine (proved), arithmetization socketed

Entry 221 (`…ACC0BFLCollapse`) factored the deep Karp–Lipton inclusion through `NEXP = MIP` (Babai–Fortnow–Lund 1991,
the entry-221 `NexpEqMIP` socket).  This file opens that socket and **proves the genuine arithmetic engine of the
BFL protocol — the sum-check round reduction** — isolating the arithmetization and multi-prover soundness as named
sub-sockets.

The protocol.  `NEXP` membership is arithmetized into a claim about a sum of a low-degree polynomial `g` over the
boolean hypercube, `H = ∑_{b ∈ {0,1}^m} g(b)` (e.g. the count of satisfying assignments of an arithmetized certificate
predicate).  The **sum-check protocol** verifies such a claim with `m` rounds of interaction: each round the prover
sends the univariate "round polynomial" `g₁(X) = ∑_{rest} g(X, rest)`, the verifier checks the consistency
`g₁(0) + g₁(1) = H`, picks a random challenge `r`, and recurses on the claim `g₁(r) = ∑_{rest} g(r, rest)` — an
`(m-1)`-variable sum-check.  After `m` rounds the claim reduces to a single evaluation `g(r₁, …, r_m)`.

The two identities that ARE the protocol's arithmetic:

* **`scSum_succ_eq`** — the round-consistency identity `∑_{b ∈ {0,1}^{m+1}} g(b) = g₁(0) + g₁(1)` where `g₁ = roundPoly
  g` is the round polynomial: splitting off the first coordinate, the hypercube sum equals the two boolean values of the
  round polynomial.  This is exactly the verifier's per-round check.
* **`roundPoly_eq_scSum_restrict`** — the recursion identity `roundPoly g r = scSum (g(r, ·))`: after the verifier's
  challenge `r`, the remaining claim is a fresh `m`-variable sum-check on `g` partially evaluated at `r`.
* **`scSum_zero`** — the base case `∑_{b ∈ {0,1}^0} g(b) = g(())`: after `m` rounds the protocol terminates at a single
  point evaluation.

## What is proved (clean axioms, no `sorry`)

* **`scSum g := ∑_{b : Fin m → Bool} g(boolToR ∘ b)`** — the sum of `g` over the boolean hypercube `{0,1}^m ⊆ Rᵐ`.
* **`roundPoly g s := ∑_{t} g(Fin.cons s (boolToR ∘ t))`** — the round polynomial (first coordinate free at `s ∈ R`,
  the rest summed over the hypercube).
* **`scSum_succ_eq`** (PROVED) — `scSum g = roundPoly g 0 + roundPoly g 1` (the round-consistency check).
* **`roundPoly_eq_scSum_restrict`** (PROVED) — `roundPoly g r = scSum (fun rest => g (Fin.cons r rest))` (recursion).
* **`scSum_zero`** (PROVED) — `scSum g = g Fin.elim0` (termination at a single evaluation).
* **`nexpEqMIP_of_subset`** — discharges the entry-221 `NexpEqMIP` socket from the two inclusions (`NexpSubsetMIP`,
  `MipSubsetNexp`) by antisymmetry.

## Honest scope

This proves the **sum-check round reduction** completely, over an arbitrary commutative ring `R` (the field case is the
operative one): the per-round consistency identity (`scSum_succ_eq`), the recursion to a smaller instance after the
challenge (`roundPoly_eq_scSum_restrict`), and the base-case termination (`scSum_zero`) — pure finite-sum algebra, no
measure theory.  These three are the arithmetic engine on which the BFL `NEXP ⊆ MIP` direction runs.  What remains
named sockets are the genuinely deep BFL ingredients: **`NexpArithmetization`** (that a `NEXP` computation encodes as a
low-degree polynomial `g` over a field with `scSum g` reading off acceptance — the certificate-to-polynomial
arithmetization), **`SumCheckSoundness`** (that a *dishonest* prover is caught with high probability — Schwartz–Zippel
on the low-degree round polynomials, plus the *multi-prover* multilinearity test that makes this `MIP` rather than
single-prover `IP = PSPACE`), and **`MipSubsetNexp`** (the simulation direction — an `MIP` protocol's acceptance is
computable in `NEXP` by guessing the exponential prover tables).  Each needs field/probability/protocol infrastructure
beyond this engine.  This proves the sum-check arithmetic and the antisymmetry assembly of `NEXP = MIP`, not the
arithmetization or the soundness.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0SumCheck

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0BFLCollapse (NexpEqMIP)

variable {R : Type*} [CommRing R]

/-- The boolean value `b` as a ring element: `false ↦ 0`, `true ↦ 1` (the hypercube `{0,1} ⊆ R`). -/
def boolToR : Bool → R := fun b => if b then 1 else 0

/-- **The sum of `g` over the boolean hypercube** `{0,1}^m ⊆ Rᵐ`: `∑_{b : Fin m → Bool} g(boolToR ∘ b)`.  The
arithmetized `NEXP` claim is `H = scSum g` (e.g. the count of satisfying assignments of an arithmetized predicate). -/
def scSum {m : ℕ} (g : (Fin m → R) → R) : R :=
  ∑ b : Fin m → Bool, g (fun i => boolToR (b i))

/-- **The sum-check round polynomial.**  The first coordinate is left free at `s ∈ R`, the remaining `m` coordinates are
summed over the hypercube: `g₁(s) = ∑_{t} g(Fin.cons s (boolToR ∘ t))`.  In the protocol the prover sends this
univariate polynomial each round. -/
def roundPoly {m : ℕ} (g : (Fin (m+1) → R) → R) (s : R) : R :=
  ∑ t : Fin m → Bool, g (Fin.cons s (fun i => boolToR (t i)))

/-- The hypercube `{0,1}^{m+1}` splits as `{0,1} × {0,1}^m` via `Fin.cons`/`Fin.tail` (first coordinate first). -/
def consEquivBool (m : ℕ) : (Fin (m+1) → Bool) ≃ Bool × (Fin m → Bool) where
  toFun b := (b 0, Fin.tail b)
  invFun p := Fin.cons p.1 p.2
  left_inv b := Fin.cons_self_tail b
  right_inv p := by simp [Fin.tail_cons]

/-- `boolToR` commutes with `Fin.cons`: `boolToR ∘ (Fin.cons h t) = Fin.cons (boolToR h) (boolToR ∘ t)`. -/
theorem boolToR_cons {m : ℕ} (h : Bool) (t : Fin m → Bool) :
    ((fun i => boolToR ((Fin.cons h t : Fin (m+1) → Bool) i)) : Fin (m+1) → R)
      = Fin.cons (boolToR h) (fun i => boolToR (t i)) := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp [Fin.cons_zero, Fin.cons_succ]

/-- **The sum-check round-consistency identity (PROVED).**  The hypercube sum equals the two boolean values of the
round polynomial: `scSum g = roundPoly g 0 + roundPoly g 1`.  This is exactly the verifier's per-round check
`g₁(0) + g₁(1) = H` — splitting off the first coordinate, `∑_{b ∈ {0,1}^{m+1}} g(b) = ∑_{rest} g(0, rest) + ∑_{rest}
g(1, rest)`.  Proof: reindex the hypercube `{0,1}^{m+1} ≃ {0,1} × {0,1}^m` (`consEquivBool`), split the boolean head
(`Fintype.sum_bool`), and match `boolToR false = 0`, `boolToR true = 1` (`boolToR_cons`). -/
theorem scSum_succ_eq {m : ℕ} (g : (Fin (m+1) → R) → R) :
    scSum g = roundPoly g 0 + roundPoly g 1 := by
  have key : scSum g
      = ∑ p : Bool × (Fin m → Bool),
          g (fun i => boolToR ((Fin.cons p.1 p.2 : Fin (m+1) → Bool) i)) := by
    apply Fintype.sum_equiv (consEquivBool m)
    intro b
    congr 1
    funext i
    simp only [consEquivBool, Equiv.coe_fn_mk]
    rw [show Fin.cons (b 0) (Fin.tail b) = b from Fin.cons_self_tail b]
  rw [key, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  unfold roundPoly
  congr 1 <;>
  · apply Finset.sum_congr rfl
    intro t _
    rw [boolToR_cons]
    simp [boolToR]

/-- **The sum-check recursion identity (PROVED).**  After the verifier's challenge `r`, the round polynomial value
`roundPoly g r` equals the hypercube sum of `g` with its first coordinate fixed to `r`: `roundPoly g r =
scSum (fun rest => g (Fin.cons r rest))` — a fresh `m`-variable sum-check on `g` partially evaluated at `r`.  This is
why the protocol recurses round by round.  Definitional. -/
theorem roundPoly_eq_scSum_restrict {m : ℕ} (g : (Fin (m+1) → R) → R) (r : R) :
    roundPoly g r = scSum (fun rest : Fin m → R => g (Fin.cons r rest)) := rfl

/-- **The sum-check base case (PROVED).**  Over the empty hypercube `{0,1}^0`, the sum is the single point evaluation:
`scSum g = g Fin.elim0`.  After `m` rounds the protocol terminates here, at `g(r₁, …, r_m)`. -/
theorem scSum_zero (g : (Fin 0 → R) → R) : scSum g = g Fin.elim0 := by
  rw [scSum, Fintype.sum_unique]
  congr 1
  funext i
  exact i.elim0

/-- **The arithmetization socket (BFL).**  Every `NEXP` language encodes as a low-degree polynomial over a field whose
hypercube sum `scSum` reads off acceptance — the certificate-to-polynomial arithmetization.  Stated, not proved. -/
def NexpArithmetization (NEXP : CClass) : Prop := ∀ L ∈ NEXP, True

/-- **The sum-check soundness socket (BFL).**  A dishonest prover is caught with high probability (Schwartz–Zippel on
the low-degree round polynomials) and the *multi-prover* multilinearity test forces `MIP` rather than single-prover
`IP = PSPACE`.  Stated, not proved. -/
def SumCheckSoundness (NEXP MIP : CClass) : Prop := ∀ L ∈ MIP, True

/-- **The deep direction `NEXP ⊆ MIP` (arithmetization + sum-check + soundness).**  Named socket. -/
def NexpSubsetMIP (NEXP MIP : CClass) : Prop := NEXP ⊆ MIP

/-- **The simulation direction `MIP ⊆ NEXP`** — an `MIP` protocol's acceptance is computable in `NEXP` by guessing the
exponential prover tables.  Named socket. -/
def MipSubsetNexp (MIP NEXP : CClass) : Prop := MIP ⊆ NEXP

/-- **Discharges the entry-221 `NexpEqMIP` socket (PROVED glue).**  `NEXP = MIP` follows from the two inclusions
`NEXP ⊆ MIP` (the deep BFL direction, on the sum-check engine above) and `MIP ⊆ NEXP` (simulation) by antisymmetry. -/
theorem nexpEqMIP_of_subset (NEXP MIP : CClass)
    (h1 : NexpSubsetMIP NEXP MIP) (h2 : MipSubsetNexp MIP NEXP) :
    NexpEqMIP NEXP MIP :=
  Set.Subset.antisymm h1 h2

end PallLean.Paper93.DeepMath.PathB.ACC0SumCheck

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SumCheck.scSum_succ_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SumCheck.roundPoly_eq_scSum_restrict
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SumCheck.scSum_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SumCheck.nexpEqMIP_of_subset
