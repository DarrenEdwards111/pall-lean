import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0QuantError
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModPExact
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTExactCompose
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsFastSat
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsRealizationSplit

/-!
# ACC⁰ frontier summary — the dependency graph as Lean theorems

A single readable file that re-states the converged `ACC⁰` boundary map as Lean theorems, so the corpus's claim is
checkable at a glance.  Each "pillar" below is *re-exported from its proved source*; the Williams route is assembled
into one conditional theorem whose only open inputs are the two genuine walls.

```
 AC⁰ polynomial method (quantitative)         PROVED   ac0_approximation_quantitative      (…ACC0QuantError)
 MOD_p exact low-degree over F_p              PROVED   modp_exact_low_degree               (…ACC0ModPExact)
 exact SYM∘AND decoding (every ACC0Circuit)   PROVED   exact_symAnd_decoding               (…ACC0YBTExactCompose)
 Williams fastSat count-search (quantitative) PROVED   fastSat_quantitative                (…ACC0WilliamsFastSat)
 realization socket split + self-audit        PROVED   timeHierarchy_is_the_separation     (…ACC0WilliamsRealizationSplit)
 ───────────────────────────────────────────────────────────────────────────────────────────────────────
 Williams route to NEXP ⊄ ACC⁰                CONDITIONAL on the two remaining walls:
   williams_route_reduces_to_two_sockets :
     (exact + quasipolynomial SYM∘AND for all ACC⁰)  ∧  (NTIME-hierarchy / Williams' method)  ⇒  NEXP ⊄ ACC⁰
```

## What is proved (clean axioms, no `sorry`)

* `ac0_approximation_quantitative` — re-export of `approximable_full`: every `MOD`-free circuit has an `F₂`
  approximant of degree `≤ t^depth` and error `≤ size·2^{-t}`.
* `modp_exact_low_degree` — re-export of `modp_exact_eval`: `MOD_p` is *exactly* the degree-`(p−1)` `F_p` polynomial.
* `exact_symAnd_decoding` — re-export of `acc0circuit_hasSymAndForm`: every `ACC0Circuit` has an *exact* `SYM∘AND`
  form (size `symAndSize C`).
* `fastSat_quantitative` — re-export of `symAnd_williams_fastSat`: a low-degree `SYM∘AND` decides SAT by a count-cell
  search with quantitative Williams savings.
* `timeHierarchy_is_the_separation` — re-export of the self-audit: the deep realization sub-socket is `⟺ NEXP ⊄ ACC⁰`.
* **`williams_route_reduces_to_two_sockets`** — the headline: the whole route is one conditional theorem; its only
  non-routine inputs are (A) the exact-quasipolynomial `SYM∘AND` socket and (B) the time-hierarchy socket.

## Honest scope — the two remaining walls, named and isolated

The route is **conditional**, not a proof.  Open input (A) = an exact `SYM∘AND` of *quasipolynomial* size for all
`ACC⁰` (the size wall — exactness is proved, `…ACC0YBTExactCompose`; quasipoly size is open and stops at prime-power
`MOD`, the composite-`MOD` barrier).  Open input (B) = the nondeterministic time hierarchy / Williams' algorithmic
method (`timeHierarchy_is_the_separation` proves it *is* the separation).  Everything between them — encoding, cost
arithmetic, depth induction, decoding — is proved or routine.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox
open PallLean.Paper93.DeepMath.PathB.ACC0OrStep
open PallLean.Paper93.DeepMath.PathB.ACC0QuantDegree
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat
open PallLean.Paper93.DeepMath.PathB.ACC0QuantError
open PallLean.Paper93.DeepMath.PathB.ACC0ModPExact
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRealizationSplit

/-! ## The proved pillars (re-exported) -/

/-- **Pillar 1 (proved): the AC⁰ polynomial method, quantitative.**  Every `MOD`-free circuit `C` has an `F₂`
approximant of degree `≤ t^(depth C)` and error `≤ size·2^{-t}` (here in the `2^t·error ≤ size·2^n` form). -/
theorem ac0_approximation_quantitative {n t : ℕ} (ht : 1 ≤ t) (C : Circ n) :
    ∃ Q : MvPolynomial (Fin n) (ZMod 2),
      Q.totalDegree ≤ t ^ cdepth C
        ∧ 2 ^ t * (perr Q (fun x => Circ.eval x C)).card ≤ Circ.size C * Fintype.card (Fin n → Bool) :=
  approximable_full ht C

/-- **Pillar 2 (proved): `MOD_p` is exactly the degree-`(p−1)` polynomial over `F_p` (Fermat).** -/
theorem modp_exact_low_degree {n p : ℕ} [Fact p.Prime] (x : Fin n → Bool) (S : Finset (Fin n)) :
    eval (fun i => boolToZMod p (x i)) (modpPoly p S) = boolToZMod p (modpBool p S x) :=
  modp_exact_eval x S

/-- **Pillar 3 (proved): every `ACC0Circuit` has an *exact* `SYM∘AND` form** (of size `symAndSize C`).  The decoding /
composition half of YBT — proved in full; only quasipolynomial *size* remains open. -/
theorem exact_symAnd_decoding {n : ℕ} (C : ACC0Circuit n) :
    HasSymAndForm (fun x => eval C x) (symAndSize C) :=
  acc0circuit_hasSymAndForm C

/-- **Pillar 4 (proved): the Williams `fastSat` count-search is quantitative.**  A degree-`≤D` injective `SYM∘AND`
decides SAT by the count-cell image and delivers Williams savings `≥ 2^k` when the gate count fits `2^{n−k}`. -/
theorem fastSat_quantitative {n m D : ℕ} (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool)
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ D) {k : ℕ} (hkn : k ≤ n)
    (hfit : (∑ i ∈ Finset.range (D + 1), n.choose i) + 1 ≤ 2 ^ (n - k)) :
    2 ^ k * (Finset.univ.image
        (ACC0SymmetricObserver.gateCount (fun j x => ACC0PolyToSymAnd.monoAND (mono j) x))).card
      ≤ 2 ^ n :=
  (symAnd_williams_fastSat mono h hinj hdeg hkn hfit).2.2

/-! ## The Williams route, reduced to two sockets -/

/-- **Self-audit (proved, re-exported): the deep realization sub-socket *is* the separation.**  Once a uniform
`ACC⁰`-SAT speedup is established, the time-hierarchy sub-socket is logically equivalent to `NEXP ⊄ ACC⁰`. -/
theorem timeHierarchy_is_the_separation {Uniform NEXPnotACC0 : Prop} (hu : Uniform) :
    TimeHierarchySocket Uniform NEXPnotACC0 ↔ NEXPnotACC0 :=
  timeHierarchy_socket_iff_separation Uniform NEXPnotACC0 hu

/-- **The headline (proved): the entire Williams route is one conditional theorem on two deep sockets.**

Given
* **(A)** the exact-quasipolynomial `SYM∘AND` socket for all `ACC⁰` — here the `MixedACCDepthReductionSocket`
  (depth-2 residue normal form), the *size* content of YBT; and
* **(B)** the time-hierarchy / Williams' algorithmic-method socket `TimeHierarchySocket`,

together with the *routine* realization sub-sockets (`EncodingSocket`, `CostBridgeSocket`, `UniformitySocket`),
the separation `NEXP ⊄ ACC⁰` follows.  All content is in (A) and (B); the rest is proved or routine. -/
theorem williams_route_reduces_to_two_sockets
    {EncodedAlg TimeBounded Uniform NEXPnotACC0 : Prop}
    -- (A) the exact-quasipolynomial SYM∘AND / depth-reduction socket:
    (hExact : ∀ (n : ℕ) (C : ACC0Circuit n),
      ACC0ResidueDepthReduction.MixedACCDepthReductionSocket C)
    -- routine realization bookkeeping:
    (s1 : EncodingSocket EncodedAlg)
    (s2 : CostBridgeSocket EncodedAlg TimeBounded)
    (s3 : UniformitySocket TimeBounded Uniform)
    -- (B) the deep time-hierarchy socket:
    (hTimeHierarchy : TimeHierarchySocket Uniform NEXPnotACC0) :
    NEXPnotACC0 :=
  residue_cashout_bundled hExact
    (routine_reduce_to_timeHierarchy EncodedAlg TimeBounded Uniform NEXPnotACC0 s1 s2 s3 hTimeHierarchy)

end PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.ac0_approximation_quantitative
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.exact_symAnd_decoding
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.williams_route_reduces_to_two_sockets
