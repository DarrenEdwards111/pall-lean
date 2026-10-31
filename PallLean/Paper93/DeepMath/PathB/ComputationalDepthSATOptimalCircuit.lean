import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUhligCancellation

/-!
# Proving `t ≤ r` for SAT's circuit: there is no single circuit — it is the cost-minimizing adversary

`UhligCancellation` reduced the socket for SAT's seam to one inequality on the amortization split:
`t ≤ r` (the shareable template is at most the per-copy work).  The ask is to prove it "for SAT's
specific circuit".  This file makes precise the one thing that framing hides: **there is no single SAT
circuit.**  The lower bound quantifies over *all* circuits computing SAT, and the cost-minimizing
adversary chooses the split `(t, r)` to *maximize* sharing — pushing `t` up.  So `t ≤ r` must hold at the
adversary's optimum, and that is a `∀`-circuits statement, not a property of one fixed circuit.

## The model

A circuit for the two disjoint copies is its amortization split: a `template` `t` and `local` `r` with
`t + r = C`, the single-copy cost (`= D d`).  Its two-copy cost is `t + 2r` — share the template, pay
both locals.

## What is proved

* **`cost_eq`** — the two-copy cost is `2C − t`: *every unit of template lowers the cost*.  So the
  cost-minimizing circuit **maximizes** `t` (maximizes mass production).
* **`more_sharing_cheaper`** — monotone form: more template ⟹ lower cost.  The adversary shares maximally.
* **`socket_iff_template_below_half`** — for any circuit, `t ≤ r` ⟺ `2t ≤ C`: the socket is "the template
  is at most half the single-copy cost".
* **`socket_binds_at_adversary`** — the crux: if `Kopt` is the *maximum-sharing* circuit, then the socket
  holds at `Kopt` **iff** it holds at *every* circuit.  Proving `t ≤ r` "for SAT's circuit" IS proving it
  for the cost-minimizing adversary IS proving it for all circuits — the `∀`-circuits lower bound.
* **`mass_producer_violates`** — a circuit with `t > r` exists (`massProducer`, `t = 3 > r = 1`): mass
  production is *consistent*.  So the bound is genuinely SAT-specific — a general argument cannot give it;
  it must rule the mass-producer out **for SAT**.

## Honest verdict — this is the terminal reduction; the next move is a technique, not a reframe

"Prove `t ≤ r` for SAT's specific circuit" has no single-circuit reading: the inequality must hold at the
cost-minimizing adversary, which (by `socket_binds_at_adversary`) is exactly the statement over *all*
circuits — upper-bounding SAT's maximum mass-production by half a copy.  Mass-producing circuits exist in
general (`mass_producer_violates`), so nothing generic delivers it; it requires SAT's specific
incompressibility.  This is the surviving Uhlig `NonlinearHorn` = `cost_super` = `P ≠ NP`, now in its
tightest possible form: a single inequality `t ≤ r` at the sharing-maximising adversary.  No reframe
tightens a single inequality further — crossing it needs a genuinely new (necessarily non-natural)
lower-bound technique that upper-bounds SAT's mass-production.  I have reduced it to that single
adversarial inequality and proved everything around it; the inequality itself is the wall.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATOptimalCircuit

/-- **A circuit for the two disjoint copies**, as its amortization split.  `template` `t` is the
shareable sub-computation, `local_` `r` the per-copy work, and `realizes : t + r = C` ties them to the
single-copy cost `C = D d`.  Different circuits split the same `C` differently — the adversary picks the
split. -/
structure TwoCopyCircuit (C : ℕ) where
  /-- shareable template cost `t` -/
  template : ℕ
  /-- per-copy local cost `r` -/
  local_ : ℕ
  /-- the split realizes the single-copy cost -/
  realizes : template + local_ = C

/-- The two-copy cost `t + 2r`: one shared template, two locals. -/
def TwoCopyCircuit.cost {C : ℕ} (K : TwoCopyCircuit C) : ℕ := K.template + 2 * K.local_

/-! ### The adversary maximizes sharing -/

/-- **The two-copy cost is `2C − t` (proved).**  Every unit of template lowers the cost, so the
cost-minimizing circuit maximizes `t` — it mass-produces as much as it can. -/
theorem cost_eq {C : ℕ} (K : TwoCopyCircuit C) : K.cost = 2 * C - K.template := by
  have h := K.realizes
  simp only [TwoCopyCircuit.cost]
  omega

/-- **More sharing is cheaper (proved).**  A circuit with a larger template costs no more.  The
adversary drives `t` up to minimize cost. -/
theorem more_sharing_cheaper {C : ℕ} (K K' : TwoCopyCircuit C) (h : K.template ≤ K'.template) :
    K'.cost ≤ K.cost := by
  have h1 := K.realizes
  have h2 := K'.realizes
  rw [cost_eq, cost_eq]
  omega

/-! ### The socket, and why it binds at the adversary -/

/-- **The socket ⟺ the template is at most half the copy (proved).**  For any circuit, `t ≤ r` holds
exactly when `2t ≤ C`.  This is `UhligCancellation.socket_iff_local_dominates` on the split. -/
theorem socket_iff_template_below_half {C : ℕ} (K : TwoCopyCircuit C) :
    K.template ≤ K.local_ ↔ 2 * K.template ≤ C := by
  have h := K.realizes
  omega

/-- **The socket binds at the adversary = it binds everywhere (proved) — the crux.**  If `Kopt` has the
maximum template among all circuits for the copy, then `2·(Kopt.template) ≤ C` (the socket at the
cost-minimizing, sharing-maximising circuit) holds **iff** `2·(K.template) ≤ C` holds for *every*
circuit `K`.  So proving `t ≤ r` "for SAT's circuit" is proving it at the adversary, which is proving it
for all circuits — the `∀`-circuits lower bound. -/
theorem socket_binds_at_adversary {C : ℕ} (Kopt : TwoCopyCircuit C)
    (hopt : ∀ K : TwoCopyCircuit C, K.template ≤ Kopt.template) :
    (2 * Kopt.template ≤ C) ↔ (∀ K : TwoCopyCircuit C, 2 * K.template ≤ C) := by
  constructor
  · intro h K
    have hk := hopt K
    omega
  · intro h
    exact h Kopt

/-! ### The bound is genuinely SAT-specific: mass production is consistent -/

/-- A concrete **mass-producer**: single-copy cost `C = 4`, template `3` exceeding local `1`. -/
def massProducer : TwoCopyCircuit 4 := ⟨3, 1, by omega⟩

/-- **A mass-producing circuit violates the socket (proved).**  `massProducer` has `2·template = 6 > 4 =
C`, i.e. `t > r`: it shares more than half a copy.  Such circuits exist in general, so no generic
argument gives `t ≤ r` — it must rule the mass-producer out **for SAT**, which is SAT's specific
incompressibility. -/
theorem mass_producer_violates : ¬ (2 * massProducer.template ≤ 4) := by decide

/-- **Mass production beats doubling (proved).**  `massProducer`'s two-copy cost `5` is strictly below
`2C = 8`: sharing genuinely saves.  The socket for SAT must forbid exactly this on SAT's seam. -/
theorem mass_producer_beats_doubling : massProducer.cost < 2 * 4 := by decide

end PallLean.Paper93.DeepMath.PathB.SATOptimalCircuit

#print axioms PallLean.Paper93.DeepMath.PathB.SATOptimalCircuit.cost_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SATOptimalCircuit.more_sharing_cheaper
#print axioms PallLean.Paper93.DeepMath.PathB.SATOptimalCircuit.socket_iff_template_below_half
#print axioms PallLean.Paper93.DeepMath.PathB.SATOptimalCircuit.socket_binds_at_adversary
#print axioms PallLean.Paper93.DeepMath.PathB.SATOptimalCircuit.mass_producer_violates
#print axioms PallLean.Paper93.DeepMath.PathB.SATOptimalCircuit.mass_producer_beats_doubling
