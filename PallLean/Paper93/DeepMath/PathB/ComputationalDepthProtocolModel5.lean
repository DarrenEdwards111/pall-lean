import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProtocolModel4

/-!
# Communication protocol model 5: the one-round reduction (attempt)

An honest attempt at the one-round / round-elimination lemma.  Two pieces are
genuinely provable and go in here; the third, the analytic core, is the wall and is
**not** in this file (nor faked as a socket).

## Provable: the round-elimination mechanism
Peeling the first message reduces the protocol to a subprotocol on a restricted
domain, a strictly smaller instance:

* **`cont`** — the continuation after the first message;
* **`trans_peel_alice` / `trans_peel_bob` (proved)** — the transcript is the first
  bit followed by the continuation's transcript;
* **`cost_cont_lt_alice` / `cost_cont_lt_bob` (proved)** — the continuation is
  strictly cheaper (the instance shrinks each round).

## Provable: the silent-player kernel (base case)
A party who never speaks cannot influence the transcript or the output, so a task
that depends on that party's input needs at least one round from them:

* **`noBob` / `noAlice`** — the protocol never lets Bob / Alice speak;
* **`run_indep_of_noBob` / `run_indep_of_noAlice` (proved)** — then the output is
  independent of that party's input.

## The wall (NOT in this file, NOT faked)
The analytic one-round *lower* bound — that a first message too short to resolve the
universal-relation block leaves a genuine (ℓ−1)-fold instance, so `ℓ` rounds are
forced — is GMWW's information-complexity core (KRW19 `RoundElimStep`).  It is not
proved here or anywhere in the arc; it is the research-level step.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CommProtocol

variable {α β τ : Type*}

/-! ## The round-elimination mechanism -/

/-- The continuation of a protocol after its first message on inputs `x, y`. -/
def cont : Protocol α β τ → α → β → Protocol α β τ
  | .leaf t, _, _ => .leaf t
  | .alice f l r, x, _ => bif f x then r else l
  | .bob g l r, _, y => bif g y then r else l

/-- **The first message peels off (Alice, proved)**: the transcript is the first bit
followed by the continuation's transcript. -/
theorem trans_peel_alice (f : α → Bool) (l r : Protocol α β τ) (x : α) (y : β) :
    trans (Protocol.alice f l r) x y = f x :: trans (cont (Protocol.alice f l r) x y) x y := by
  simp only [trans, cont]
  cases f x <;> rfl

/-- **The first message peels off (Bob, proved)**. -/
theorem trans_peel_bob (g : β → Bool) (l r : Protocol α β τ) (x : α) (y : β) :
    trans (Protocol.bob g l r) x y = g y :: trans (cont (Protocol.bob g l r) x y) x y := by
  simp only [trans, cont]
  cases g y <;> rfl

/-- **The continuation is strictly cheaper (Alice, proved)**: the instance shrinks. -/
theorem cost_cont_lt_alice (f : α → Bool) (l r : Protocol α β τ) (x : α) (y : β) :
    cost (cont (Protocol.alice f l r) x y) < cost (Protocol.alice f l r) := by
  simp only [cont, cost]
  cases f x <;> simp only [cond_false, cond_true] <;> omega

/-- **The continuation is strictly cheaper (Bob, proved)**. -/
theorem cost_cont_lt_bob (g : β → Bool) (l r : Protocol α β τ) (x : α) (y : β) :
    cost (cont (Protocol.bob g l r) x y) < cost (Protocol.bob g l r) := by
  simp only [cont, cost]
  cases g y <;> simp only [cond_false, cond_true] <;> omega

/-! ## The silent-player kernel -/

/-- The protocol never lets Bob speak (no `bob` nodes). -/
def noBob : Protocol α β τ → Prop
  | .leaf _ => True
  | .alice _ l r => noBob l ∧ noBob r
  | .bob _ _ _ => False

/-- The protocol never lets Alice speak (no `alice` nodes). -/
def noAlice : Protocol α β τ → Prop
  | .leaf _ => True
  | .bob _ l r => noAlice l ∧ noAlice r
  | .alice _ _ _ => False

/-- **A silent Bob leaves the transcript independent of `y` (proved)**. -/
theorem trans_indep_of_noBob (P : Protocol α β τ) (x : α) (y y' : β) (h : noBob P) :
    trans P x y = trans P x y' := by
  revert h
  induction P with
  | leaf t => intro _; rfl
  | alice f l r ihl ihr =>
    intro h
    obtain ⟨hl, hr⟩ := h
    simp only [trans]
    cases f x with
    | false => simp only [cond_false]; rw [ihl hl]
    | true => simp only [cond_true]; rw [ihr hr]
  | bob g l r ihl ihr =>
    intro h
    exact absurd h (by simp [noBob])

/-- **A silent Alice leaves the transcript independent of `x` (proved)**. -/
theorem trans_indep_of_noAlice (P : Protocol α β τ) (x x' : α) (y : β) (h : noAlice P) :
    trans P x y = trans P x' y := by
  revert h
  induction P with
  | leaf t => intro _; rfl
  | bob g l r ihl ihr =>
    intro h
    obtain ⟨hl, hr⟩ := h
    simp only [trans]
    cases g y with
    | false => simp only [cond_false]; rw [ihl hl]
    | true => simp only [cond_true]; rw [ihr hr]
  | alice f l r ihl ihr =>
    intro h
    exact absurd h (by simp [noAlice])

/-- **A silent Bob cannot affect the output (proved)**: the base-case round lower
bound — a `y`-dependent task needs at least one Bob round. -/
theorem run_indep_of_noBob (P : Protocol α β τ) (x : α) (y y' : β) (h : noBob P) :
    run P x y = run P x y' :=
  run_eq_of_trans_eq P x y x y' (trans_indep_of_noBob P x y y' h)

/-- **A silent Alice cannot affect the output (proved)**. -/
theorem run_indep_of_noAlice (P : Protocol α β τ) (x x' : α) (y : β) (h : noAlice P) :
    run P x y = run P x' y :=
  run_eq_of_trans_eq P x y x' y (trans_indep_of_noAlice P x x' y h)

end PallLean.Paper93.DeepMath.PathB.CommProtocol

#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.trans_peel_alice
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.cost_cont_lt_alice
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.run_indep_of_noBob
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.run_indep_of_noAlice
