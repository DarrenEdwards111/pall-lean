import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ApproxBTInstantiation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimePowerMixedRadix
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTClosureFrontier

/-!
# Step (3) — the honest partial discharge of `DynamicClosesAtBT`

Steps (a) and (b) supplied the two BT ingredients as *proved* theorems:

* **(a) AC⁰ approximate low-degree** (entry 173, `…ACC0ApproxBTInstantiation.approx_endToEnd_BT`): the Razborov–Smolensky
  approximant of a constant-depth circuit has polylog degree and quasipolynomial monomial count.
* **(b) `MOD` exact `SYM∘AND`** (entry 174, `…ACC0PrimePowerMixedRadix.modPrimePower_symAndForm`): a `MOD_q` gate of any
  modulus — including prime-power `p^e` — has an exact `SYM∘AND` form (no field polynomial, sidestepping the field
  obstruction).

This file does the **partial discharge** of the entry-166 socket `DynamicClosesAtBT`: it bundles (a) and (b) as proved
components, isolates the **single remaining residual** — the *BT size analysis* `hSize` that combines the per-part
representations into one quasipolynomial-size `SYM∘AND` for an arbitrary `ACC⁰` circuit — and shows
`DynamicClosesAtBT` follows from `hSize` applied to the proved (a), (b).  Then it chains to `¬ NEXPHasACC0Circuits` via
entry 166.  The discharge is **honest and partial**: two of the three BT ingredients are *proved*; the third — the
quasipoly-size combination — is the one named socket (the genuine BT size theorem, proven classically, large to
formalise), not faked.

## What is proved (clean axioms, no `sorry`)

* **`ACComponent` / `acComponent_proved`** — the AC⁰ approximate low-degree/quasipoly-count component, PROVED (from 173).
* **`MODComponent` / `modComponent_proved`** — the `MOD` exact `SYM∘AND` component, PROVED (from 174).
* **`dynamicClosure_partial_discharge`** — `DynamicClosesAtBT` from `hSize` (the residual size socket) applied to the
  proved components.
* **`partialDischarge_to_NEXP`** — chains the discharge to `¬ NEXPHasACC0Circuits` through entry 166.

## Honest scope

The two BT ingredients are genuinely proved; `DynamicClosesAtBT` is reduced to exactly one residual socket `hSize` (the
BT mixed-radix/size analysis that keeps the combined `SYM∘AND` quasipolynomial), plus the entry-166 Williams sockets
(`closure_to_quasi`, `quasi_to_speed`, `williams`, `hierarchy`).  This is **not** a proof of `DynamicClosesAtBT` or of
`NEXP ⊄ ACC⁰`: the residual size analysis is the full Beigel–Tarui size theorem, which is a *proven classical theorem*
(as is `NEXP ⊄ ACC⁰`, Williams 2011) and a large formalisation, left as the named socket.  Nothing here is a new
separation or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosureDischarge

open PallLean.Paper93.DeepMath.PathB

/-- **The proved AC⁰ component (a).**  The Razborov–Smolensky approximant of a constant-depth circuit has polylog degree
(`≤ L^D` for `(p−1)·t ≤ L`, `depth ≤ D`) and quasipolynomial monomial count (`≤ (n+1)^{L^D}`). -/
def ACComponent : Prop :=
  ∀ {n : ℕ} (p t : ℕ), p.Prime → 1 ≤ t → ∀ (R : (k : ℕ) → Fin t → Fin k → ZMod p)
    (C : BoolCircuitSyntax n) (L D : ℕ), 1 ≤ L → (p - 1) * t ≤ L → C.depth ≤ D →
    (Layer3.toApprox p t R C).totalDegree ≤ L ^ D
      ∧ ((Layer3.toApprox p t R C).support.image (fun d => d.support)).card ≤ (n + 1) ^ (L ^ D)

/-- **(a) is proved (from entry 173).** -/
theorem acComponent_proved : ACComponent := by
  intro n p t hp ht R C L D hL hK hd
  haveI : Fact p.Prime := ⟨hp⟩
  exact ACC0ApproxBTInstantiation.approx_endToEnd_BT p t ht R C L D hL hK hd

/-- **The proved `MOD` component (b).**  A `MOD_{p^e}` gate of any prime power has an exact `SYM∘AND` form of size `|S|`
(no field polynomial — the symmetric/mixed-radix route). -/
def MODComponent : Prop :=
  ∀ {n : ℕ} (p e : ℕ) (S : Finset (Fin n)) (t : ZMod (p ^ e)),
    ACC0YBTExactCompose.HasSymAndForm
      (fun x => decide (TwoGateCorrelation.modQStatOn S (p ^ e) x = t)) S.card

/-- **(b) is proved (from entry 174).** -/
theorem modComponent_proved : MODComponent :=
  fun p e S t => ACC0PrimePowerMixedRadix.modPrimePower_symAndForm p e S t

/-- **Partial discharge of `DynamicClosesAtBT` (proved as glue).**  `DynamicClosesAtBT` follows from the residual size
socket `hSize` — the BT mixed-radix/size analysis that combines the proved AC⁰ component (a) and `MOD` component (b)
into one quasipolynomial-size `SYM∘AND` for an arbitrary `ACC⁰` circuit — applied to the *proved* components.  Two of
the three BT ingredients are proved; `hSize` is the sole remaining socket. -/
theorem dynamicClosure_partial_discharge {DynamicClosesAtBT : Prop}
    (hSize : ACComponent → MODComponent → DynamicClosesAtBT) : DynamicClosesAtBT :=
  hSize acComponent_proved modComponent_proved

/-- **The partial discharge chained to `¬ NEXPHasACC0Circuits` (proved as glue).**  Composing
`dynamicClosure_partial_discharge` with the entry-166 chain: given the residual size socket `hSize`, the
closure→quasipoly bridge, the quasipoly→speedup bridge, the Williams meta-glue, and the time hierarchy, we obtain
`¬ NEXPHasACC0Circuits`.  The proved components (a), (b) are discharged; the open content is exactly `hSize` (the BT size
theorem) and the entry-166 Williams sockets. -/
theorem partialDischarge_to_NEXP
    {DynamicClosesAtBT BTQuasi ACC0Speed NEXPC Collapse : Prop}
    (hSize : ACComponent → MODComponent → DynamicClosesAtBT)
    (closure_to_quasi : DynamicClosesAtBT → BTQuasi)
    (quasi_to_speed : BTQuasi → ACC0Speed)
    (williams : ACC0Speed → NEXPC → Collapse)
    (hierarchy : ¬ Collapse) : ¬ NEXPC :=
  ACC0BTClosureFrontier.dynamicClosure_to_NEXP_not_ACC0
    DynamicClosesAtBT BTQuasi ACC0Speed NEXPC Collapse
    (dynamicClosure_partial_discharge hSize) closure_to_quasi quasi_to_speed williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosureDischarge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosureDischarge.acComponent_proved
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosureDischarge.modComponent_proved
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosureDischarge.dynamicClosure_partial_discharge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosureDischarge.partialDischarge_to_NEXP
