import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSigma2Collapse

/-!
# The proof-complexity face of the certificate: circuit lower bounds with short proofs = Razborov's program

`Sigma2Collapse` pinned the Σ₂→NP collapse to `MCSP ∈ coNP` — a short, poly-checkable certificate of
*hardness*.  Read a certificate for what it is: a short, verifiable **proof that a truth table has no small
circuit** — a proof of a circuit lower bound.  So the collapse condition is exactly the question of
**Razborov's program**: are circuit lower bounds provable by short, feasibly-verifiable proofs (a
polynomially-bounded proof system, feasible bounded arithmetic)?

Model a Cook–Reckhow proof system for hardness statements: proofs `Cert`, a poly-time checker
`Verify : Cert → Func → Prop`, and **soundness** — it only certifies genuinely hard functions.
`HasProof f := ∃ c, Verify c f` is then an NP-style certificate; `ProvesAllHardness` says every hard
function has one.  Two facts follow, and they are the two walls, in proof-complexity clothing:

* **Sound + complete = the collapse condition.**  A sound proof system that proves all hardness gives
  `Hard f ↔ HasProof f` (`sound_complete_iff`) — precisely `Sigma2Collapse.CollapseCondition` with `Verify`
  as the certificate.  So "short LB proofs exist" *is* `MCSP ∈ coNP` (Cook–Reckhow: the hardness language
  has short proofs iff it is in NP, feeding the `MCSPcoNP` dichotomy: NP-intermediate or NP = coNP).

* **A feasibly-provable lower bound is a natural proof.**  The verifier that accepts (certificate in hand)
  exactly the hard functions is *constructive* (poly-time), *useful* (sound — it certifies hardness), and
  *large* (hard functions are the majority — the `HardSlice` counting), because completeness makes
  `Hard ⊆ HasProof` (`provable_lb_is_large`).  Constructive + useful + large = a natural property; under
  Razborov–Rudich it cannot exist (`razborov_program_barrier`).  This is Razborov's theorem in spirit:
  strong circuit lower bounds are *not* provable in feasible theories (unless one-way functions break) —
  the same obstruction that blocks feasible interpolation for strong proof systems.

## What is proved

* **`ProofSystem`** — a sound Cook–Reckhow proof system for hardness statements.
* **`sound_complete_iff`** — a sound system that proves all hardness gives `Hard f ↔ HasProof f`: the
  collapse condition, `MCSP ∈ coNP`.
* **`provable_lb_is_useful`** — a proof certifies genuine hardness (soundness = usefulness).
* **`provable_lb_is_large`** — completeness makes `Hard ⊆ HasProof`, so provability is a *large* property.
* **`razborov_program_barrier`** — under Razborov–Rudich (a constructive, useful, large property breaks
  one-way functions), no feasible proof system proves all circuit-hardness statements.

## Honest verdict — the proof-complexity face lands on the same wall

Turning the certificate into a proof does not escape anything, and it clarifies why.  "Circuit lower bounds
have short, checkable proofs" is `MCSP ∈ coNP` verbatim (`sound_complete_iff`) — so it inherits the whole
`MCSPcoNP` box (NP-intermediate or NP = coNP).  And independently, a feasibly-*verifiable*, feasibly-*complete*
proof of hardness is a natural property (constructive + useful + large), which Razborov–Rudich bars
(`razborov_program_barrier`).  That is Razborov's program's own conclusion: feasible theories do not prove
strong circuit lower bounds, because a feasible proof would *be* a natural proof.  The proof-complexity face
and the natural-proofs barrier are the same wall — `cost_super` — seen from proof theory.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ProofComplexityLB

variable {Func Cert : Type}

/-- A sound Cook–Reckhow proof system for hardness statements: statements `Hard`, a (poly-time) proof
checker `Verify`, and soundness — a checkable proof certifies only genuinely hard functions. -/
structure ProofSystem (Func Cert : Type) where
  /-- the statement "`f` is hard" (coMCSP) -/
  Hard : Func → Prop
  /-- the proof checker: `Verify c f` says `c` is a valid proof that `f` is hard (poly-time) -/
  Verify : Cert → Func → Prop
  /-- soundness: a verifiable proof certifies genuine hardness -/
  sound : ∀ f, (∃ c, Verify c f) → Hard f

/-- `f` has a (short, verifiable) proof of hardness — an NP-style certificate. -/
def HasProof (PS : ProofSystem Func Cert) (f : Func) : Prop := ∃ c, PS.Verify c f

/-- The proof system proves every hardness statement: completeness for hard functions. -/
def ProvesAllHardness (PS : ProofSystem Func Cert) : Prop := ∀ f, PS.Hard f → HasProof PS f

/-! ### Sound + complete = the collapse condition (MCSP ∈ coNP) -/

/-- **Sound + complete = the collapse condition (proved).**  A sound proof system that proves all hardness
yields `Hard f ↔ HasProof f` — exactly `Sigma2Collapse.CollapseCondition` with `Verify` as the certificate.
"Circuit lower bounds have short proofs" *is* `MCSP ∈ coNP`. -/
theorem sound_complete_iff (PS : ProofSystem Func Cert) (hpa : ProvesAllHardness PS) (f : Func) :
    PS.Hard f ↔ HasProof PS f :=
  ⟨hpa f, PS.sound f⟩

/-! ### A feasibly-provable lower bound is a natural proof -/

/-- **Provability is useful (proved).**  A verifiable proof certifies genuine hardness — the proof-verifier
is a sound distinguisher (the usefulness / lower-bound-implying half of a natural property). -/
theorem provable_lb_is_useful (PS : ProofSystem Func Cert) :
    ∀ f, HasProof PS f → PS.Hard f :=
  PS.sound

/-- **Provability is large (proved).**  Completeness makes `Hard ⊆ HasProof`; since hardness is a large
property (most functions are hard — the `HardSlice` counting), so is provability.  `Large` and its
monotonicity are the abstract Razborov–Rudich largeness data. -/
theorem provable_lb_is_large (PS : ProofSystem Func Cert)
    (Large : (Func → Prop) → Prop)
    (large_mono : ∀ P Q : Func → Prop, (∀ f, P f → Q f) → Large P → Large Q)
    (hard_large : Large PS.Hard) (hpa : ProvesAllHardness PS) :
    Large (HasProof PS) :=
  large_mono PS.Hard (HasProof PS) hpa hard_large

/-- **Razborov's program barrier (proved).**  Under Razborov–Rudich — a property that is useful (implies a
lower bound) and large, checked by a poly-time verifier, breaks one-way functions — no feasible proof system
proves all circuit-hardness statements.  A feasible proof of a lower bound would *be* a natural proof. -/
theorem razborov_program_barrier (PS : ProofSystem Func Cert)
    (Large : (Func → Prop) → Prop)
    (large_mono : ∀ P Q : Func → Prop, (∀ f, P f → Q f) → Large P → Large Q)
    (hard_large : Large PS.Hard)
    (rr : (∀ f, HasProof PS f → PS.Hard f) ∧ Large (HasProof PS) → False)
    (hpa : ProvesAllHardness PS) : False :=
  rr ⟨provable_lb_is_useful PS, provable_lb_is_large PS Large large_mono hard_large hpa⟩

end PallLean.Paper93.DeepMath.PathB.ProofComplexityLB

#print axioms PallLean.Paper93.DeepMath.PathB.ProofComplexityLB.sound_complete_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ProofComplexityLB.provable_lb_is_useful
#print axioms PallLean.Paper93.DeepMath.PathB.ProofComplexityLB.provable_lb_is_large
#print axioms PallLean.Paper93.DeepMath.PathB.ProofComplexityLB.razborov_program_barrier
