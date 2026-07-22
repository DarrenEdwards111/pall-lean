import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW18

/-!
# KRW brick 19: the round-elimination argument skeleton

The GMWW / Håstad–Wigderson lower bound for the composed universal relation is
proved by ROUND ELIMINATION: a protocol with `c` rounds for the `(ℓ+1)`-fold
composed relation is converted into a protocol with `c-1` rounds for the `ℓ`-fold
one; iterating, `ℓ`-fold composition needs `≥ ℓ` rounds, the linear bound.

This brick formalizes the ITERATION (the argument's logical skeleton) and NOTHING
MORE.  The single hard step — the per-round reduction — is the actual GMWW content
(an information-complexity / round-reduction argument), and it is a NAMED SOCKET
here, NOT proved.

* **`RoundElimStep Solv`** — the round-elimination SOCKET: `Solv (ℓ+1) (c+1) →
  Solv ℓ c` (one round eliminated drops the composition level).  This is GMWW's
  hard lemma — assumed, not proved;
* **`RoundBase Solv`** — the trivial base: a nontrivial level cannot be solved with
  `0` rounds;
* **`round_elim_lb` (proved)** — from the socket and base, `Solv ℓ c → ℓ ≤ c`: the
  `ℓ`-fold composition needs `≥ ℓ` rounds.  This is the iteration, machine-checked.

HONEST SCOPE — emphatic.  This is the SKELETON, not the theorem.  `round_elim_lb`
is a two-line induction; ALL the mathematical content of GMWW lives in
`RoundElimStep`, which is an unproved hypothesis.  Instantiating it faithfully
(`Solv r c :=` "the `r`-fold composed universal relation has a `c`-round
protocol", and proving the reduction) is the research-level work NOT done here.
Nothing here is `P ≠ NP`, and nothing here proves GMWW.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- The round-elimination step (GMWW's hard lemma, a SOCKET): eliminating one
round drops the composition level by one. -/
def RoundElimStep (Solv : ℕ → ℕ → Prop) : Prop :=
  ∀ ℓ c, Solv (ℓ + 1) (c + 1) → Solv ℓ c

/-- The base: a nontrivial composition level cannot be solved with `0` rounds. -/
def RoundBase (Solv : ℕ → ℕ → Prop) : Prop :=
  ∀ ℓ, ¬ Solv (ℓ + 1) 0

/-- **The round-elimination iteration (proved)**: from the per-round reduction
(`RoundElimStep`) and the base, the `ℓ`-fold composition needs `≥ ℓ` rounds.  This
is the argument's SKELETON; the content is in the socket `RoundElimStep`. -/
theorem round_elim_lb {Solv : ℕ → ℕ → Prop}
    (hstep : RoundElimStep Solv) (hbase : RoundBase Solv) :
    ∀ ℓ c, Solv ℓ c → ℓ ≤ c := by
  intro ℓ
  induction ℓ with
  | zero => intro c _; omega
  | succ ℓ ih =>
    intro c hc
    cases c with
    | zero => exact absurd hc (hbase ℓ)
    | succ c' =>
      have hℓ := ih c' (hstep ℓ c' hc)
      omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.round_elim_lb
