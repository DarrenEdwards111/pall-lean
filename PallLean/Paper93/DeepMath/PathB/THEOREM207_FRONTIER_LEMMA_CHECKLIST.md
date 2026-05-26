# Theorem 207 frontier lemma checklist (mechanical closure plan)

This checklist turns the remaining global God-Move frontier into explicit Lean
lemma targets.

## Goal
Close unconditional strict-class route by deriving the no-decider endpoint
without legacy seam assumptions.

---

## Module A — Global capacity object

### A1. Capacity object (single global functional)
**File:** `ComputationalDepthGlobalGodMoveCapacity.lean`

- [ ] `def GlobalGodMoveCapacityFunctional (enc : ThreeCNFEncoding) : Type`
- [ ] fields:
  - [ ] `cap : Nat -> Nat`
  - [ ] global observer bound on live boundary
  - [ ] polynomial exponent witness

### A2. Uniform upper bound theorem
**Target theorem:**
- [ ] `uniform_liveBoundary_upperBound_of_globalGodMoveCapacity`

Status: implemented in calibrated form via `GlobalGodMoveCapacityWitness`.

---

## Module B — NP lower vs capacity mismatch

### B1. Arithmetic mismatch at matched scale
**Target theorem:**
- [ ] `book1_obstruction_at_globalGodMoveCapacityExponent`

Proof ingredients:
- [ ] `arithmetic_gap_for_exponent`
- [ ] capacity upper bound from Module A

Status: implemented.

### B2. Full strict-class universal obstruction (non-vacuous)
**Target theorem:**
- [ ] `UniversalBook1BoundaryBudgetObstruction enc`

Current status:
- [ ] only calibrated/capacity and low-action lifted forms are proved.
- [ ] full strict-class non-vacuous derivation still frontier unless capacity/coverage is strengthened to cover all strict observers.

---

## Module C — Global God-Move coverage bridge

### C1. Coverage hypothesis theorem shape
**File:** `ComputationalDepthGlobalGodMoveLowActionBridge.lean`

- [ ] `StrictObserverLowActionGodMoveCoverage enc`
- [ ] `universalBook1BoundaryBudgetObstruction_of_lowActionGodMoveCoverage`

Status: implemented as bridge theorem shape (assumption form).

### C2. Frontier theorem to prove
**Load-bearing missing theorem:**
- [ ] `strictObserverLowActionGodMoveCoverage_theorem : StrictObserverLowActionGodMoveCoverage enc`

This is the concrete global God-Move theorem required to remove remaining assumption.

---

## Module D — Strict-port contradiction closure

### D1. Port => no-decider (already available)
**File:** `ComputationalDepthTheorem207StrictPort.lean`

- [ ] `no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_universalBook1Obstruction`
- [ ] `theorem207StrictPort_iff_no_DTMDecidesSATWithEncoding`

Status: implemented.

### D2. Capacity-form closure
**File:** `ComputationalDepthGlobalGodMoveCapacity.lean`

- [ ] `no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_globalGodMoveCapacity`

Status: implemented (calibrated).

---

## Module E — Standard-model bridge

### E1. Bridge object
**File:** `ComputationalDepthStrictPortStandardBridge.lean`

- [ ] `StandardPvsNPBridge`
- [ ] `theorem207StrictPort_iff_standardPvsNP`

Status: implemented.

### E2. Final external equivalence theorem (model-level)
- [ ] prove concrete instance of `StandardPvsNPBridge` for intended standard model.

---

## Execution order (recommended)

1. [ ] Prove `strictObserverLowActionGodMoveCoverage_theorem` (C2).
2. [ ] Derive full strict-class non-vacuous `UniversalBook1BoundaryBudgetObstruction` from C2 + B1.
3. [ ] Instantiate D1 to get unconditional no-decider in strict model.
4. [ ] Instantiate E2 to export standard `P ≠ NP` statement.

---

## Success criterion

Unconditional closure in this route is complete when:
- [ ] C2 is proved (not assumed), and
- [ ] E2 is proved for the chosen standard SAT-decider formalization.
