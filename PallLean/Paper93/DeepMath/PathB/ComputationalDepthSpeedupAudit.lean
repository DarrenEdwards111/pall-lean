import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteTradingClasses

/-!
# Auditing the speedup interface arithmetic before building the machine

Camp-4 discipline, applied to the second mountain.  `ConcreteSpeedup : ∀ b, 1 ≤ b → ∀ L,
DTS(2b) L → Σ₂(b) L` is Nepomnjaščiĭ speedup: split a time-`n^{2b}`, small-space deterministic
run into `k` segments, `∃` the `k` boundary configurations `∀` a segment-challenge, verify one
segment.  Before building that machine, we check the arithmetic against the corpus's ACTUAL two
conventions — and it produces a clean, two-sided verdict.

## The two load-bearing conventions (verified against the definitions)

* `Sigma2 a` clocks `ClockLe a` on `|encPair x (encPair w₁ w₂)|` — the WHOLE triple, witnesses
  included.  So the Σ₂ budget GROWS with the guessed checkpoint sequence.  (Mirror of the
  camp-4/NTIME convention; here it will HELP.)
* `SpaceGrowthLe M x S` bounds the tape at `|x| + S`, and the forced initializer copies the
  input onto the tape.  So a configuration snapshot is the whole tape — `Θ(|x|)` bits, NOT
  polylog.  This is a one-tape feature the textbook √(TS) balance does not have.

## Verdict 1 — the interface is SATISFIABLE (no camp-4 break)

Choose `k = m = (n+1)^b` (checkpoints × segment length `= (n+1)^{2b} =` the DTS clock).  Each
config is `Θ(n)`, so the tight witness has `witnessLB = k·(n+1) = (n+1)^{b+1}` bits, and one
segment check costs at most scan (`≤ witnessLB`) + simulate (`m·(n+1) = witnessLB`), i.e.
`≤ 2·witnessLB`.  The Σ₂ budget, clocked on the triple (`≥ witnessLB`), is
`c·(witnessLB+1)^b`.

* **`speedup_budget_suffices`** (proved, for ALL `n`) — `checkCost ≤ sigma2Budget`.  The check
  always fits: `witnessLB ≤ (witnessLB+1)^b` for `b ≥ 1`.  UNLIKE camp 4 (`naive_budget_fails`:
  `∃` failing input), here NO input fails — the witness-inflated clock supplies abundant budget.
  So the speedup machine obligation is constructible; the interface needs no repair.

## Verdict 2 — but the one-tape config size costs a FULL POWER in the faithful reading

The budget only closes because the clock is measured on the inflated triple.  In the FAITHFUL
reading (time as a function of `|x|` alone), the `Θ(n)` config size forces the natural
construction's cost to degree `b+1`, not `b`:

* **`witnessLB_eq`** (proved) — `witnessLB = (n+1)^{b+1}`.
* **`faithful_degree_gap`** (proved, strict for `n ≥ 1`) — `(n+1)^b < witnessLB`: the
  construction's worst-case machine time (scan to the challenged checkpoint) exceeds the
  socket's claimed `n^b` by a full power.  Faithfully, one-tape Nepomnjaščiĭ yields `Σ₂(b+1)`,
  not `Σ₂(b)`; the inflated clock is what hides the gap.
* **`sigma2_clock_grows_with_witness`** (proved) — the Σ₂ budget is monotone in witness length,
  exhibiting the inflation directly: `Σ₂(b)` here is not clocked purely in `|x|`.

## The forward flag (the real remaining concern — for the slowdown/engine audit)

The speedup machine is safe to build against the inflated interface (Verdict 1 proves it).  But
the full-power config overhead is a DEBT: a faithful de-inflation would demand `Σ₂(b+1)`, and
the engine's chain `DTS(2q²) ⊆ Σ₂(qp) ⊆ NTIME(p²)` assumed the CLEAN `DTS(2b) ⊆ Σ₂(b)`.  Whether
the `√2` window (`p² < 2q²`) survives the concrete one-tape overheads — the literature pushes
alternation-trading to `~n^{1.8}` precisely by wrangling these — is NOT decided here and must be
the slowdown/engine audit.  Build speedup against the inflated socket, but TRACK this debt; do
not claim the clean `DTS(2b) ⊆ Σ₂(b)` as faithful.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SpeedupAudit

/-- Checkpoint count = segment length = `(n+1)^b` (their product `(n+1)^{2b}` is the DTS clock). -/
def kSeg (n b : ℕ) : ℕ := (n + 1) ^ b

/-- The tight witness length: `k` configurations, each of size `Θ(n)` (one-tape holds the
input), so `k·(n+1)`.  Also the scan bound to reach the challenged checkpoint. -/
def witnessLB (n b : ℕ) : ℕ := kSeg n b * (n + 1)

/-- One segment check: scan to the checkpoint (`≤ witnessLB`) + simulate `m = (n+1)^b` steps at
one-tape overhead `≤ (n+1)` each (`= witnessLB`), times a machine constant `C`. -/
def checkCost (C n b : ℕ) : ℕ := C * (2 * witnessLB n b)

/-- The Σ₂`(b)` budget: `ClockLe b` on the triple length, which is `≥ witnessLB`. -/
def sigma2Budget (c n b : ℕ) : ℕ := c * (witnessLB n b + 1) ^ b

/-- `witnessLB = (n+1)^{b+1}` — the full-power config overhead, made explicit. -/
theorem witnessLB_eq (n b : ℕ) : witnessLB n b = (n + 1) ^ (b + 1) := by
  unfold witnessLB kSeg
  rw [pow_succ]

/-- For `b ≥ 1`, `N ≤ (N+1)^b` — the elementary fact the budget rides on. -/
theorem le_pow_self (N b : ℕ) (hb : 1 ≤ b) : N ≤ (N + 1) ^ b := by
  calc N ≤ N + 1 := Nat.le_succ N
    _ = (N + 1) ^ 1 := (pow_one _).symm
    _ ≤ (N + 1) ^ b := Nat.pow_le_pow_right (by omega) hb

/-- **Verdict 1 (proved).**  The segment check always fits the Σ₂ budget — for EVERY input `n`.
Unlike camp 4's `naive_budget_fails` (an existentially failing input), the speedup interface has
no failing input: the witness-inflated clock supplies abundant budget, so the machine obligation
is constructible and the interface needs no repair. -/
theorem speedup_budget_suffices (C n b : ℕ) (hb : 1 ≤ b) :
    checkCost C n b ≤ sigma2Budget (2 * C) n b := by
  have hPQ : witnessLB n b ≤ (witnessLB n b + 1) ^ b := le_pow_self _ b hb
  calc checkCost C n b = 2 * C * witnessLB n b := by unfold checkCost; ring
    _ ≤ 2 * C * (witnessLB n b + 1) ^ b := Nat.mul_le_mul (le_refl _) hPQ
    _ = sigma2Budget (2 * C) n b := by unfold sigma2Budget; ring

/-- **Verdict 2a (proved).**  The one-tape config size pushes the construction's cost to degree
`b+1`: `(n+1)^b < witnessLB` for `n ≥ 1`.  Faithfully (time in `|x|` alone), one-tape
Nepomnjaščiĭ yields `Σ₂(b+1)`, not `Σ₂(b)` — a full-power loss the inflated clock conceals. -/
theorem faithful_degree_gap (n b : ℕ) (hn : 1 ≤ n) : (n + 1) ^ b < witnessLB n b := by
  rw [witnessLB_eq, pow_succ]
  have h1 : 1 ≤ (n + 1) ^ b := Nat.one_le_pow _ _ (by omega)
  have h2 : (n + 1) ^ b * 2 ≤ (n + 1) ^ b * (n + 1) := Nat.mul_le_mul (le_refl _) (by omega)
  omega

/-- **Verdict 2b (proved).**  The Σ₂ budget is monotone in witness length — direct evidence that
`Σ₂(b)` here is clocked on the triple, not on `|x|`.  This inflation is what makes Verdict 1
free and Verdict 2 a hidden debt. -/
theorem sigma2_clock_grows_with_witness (c b w w' : ℕ) (h : w ≤ w') :
    c * (w + 1) ^ b ≤ c * (w' + 1) ^ b :=
  Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left (by omega) b)

/-- The two verdicts, side by side (proved): the budget suffices for all inputs (constructible),
AND the faithful construction cost strictly exceeds the socket's degree for every nonempty input
(the tracked debt). -/
theorem speedup_audit_summary (C n b : ℕ) (hb : 1 ≤ b) (hn : 1 ≤ n) :
    checkCost C n b ≤ sigma2Budget (2 * C) n b ∧ (n + 1) ^ b < witnessLB n b :=
  ⟨speedup_budget_suffices C n b hb, faithful_degree_gap n b hn⟩

end PallLean.Paper93.DeepMath.PathB.SpeedupAudit

#print axioms PallLean.Paper93.DeepMath.PathB.SpeedupAudit.speedup_budget_suffices
#print axioms PallLean.Paper93.DeepMath.PathB.SpeedupAudit.faithful_degree_gap
#print axioms PallLean.Paper93.DeepMath.PathB.SpeedupAudit.sigma2_clock_grows_with_witness
#print axioms PallLean.Paper93.DeepMath.PathB.SpeedupAudit.speedup_audit_summary
