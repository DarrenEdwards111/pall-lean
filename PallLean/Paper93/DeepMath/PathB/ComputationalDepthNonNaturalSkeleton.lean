/-!
# The non-natural certificate skeleton: three slots, and which one is open

This is the object we are looking for, as an explicit interface.  A Razborov–Rudich circuit lower
bound works by exhibiting a **property** `P` of Boolean functions with three features.  Here they are
as three slots, so it is exactly visible which one is filled and which is the wall.

* **Slot 1 — `useful`** : `P f → hard f`.  Having `P` implies a circuit lower bound.  *Structural*:
  you define `P` so this holds (e.g. `P = "no small circuit"` makes it definitional).
* **Slot 3 — `rare`** : `¬ P rnd`.  A *random* function does NOT have `P`.  This is the non-naturalness
  — it is what dodges the barrier (see below).  *Fillable by self-reference*: a coin-flip function has
  no self-referential structure, so a property keyed to self-reference is automatically rare
  (`rare_of_not_selfref`).
* **Slot 2 — `highOnSAT`** : `P sat`.  SAT itself has `P`.  **THIS IS THE OPEN SLOT** — it is exactly
  `cost_super` / the specific incompressibility of SAT.  Everything reduces to it (`target_is_highOnSAT`).

## Why slot 3 (rare) is mandatory — the Razborov–Rudich barrier

If `P` were **natural** — *large* (a random function has it) *and* constructive — then, given crypto,
it would distinguish random functions from pseudorandom (small-circuit) ones, breaking the PRG
(`non_natural_required`: natural ⟹ breaks crypto; so given crypto, `P` cannot be both large and
constructive).  So a valid certificate MUST be rare (¬large) or non-constructive.  Slot 3 says our `P`
is rare — the random function lacks it — which is exactly `¬ large`.  Hence the certificate is outside
the barrier's reach.

## The diagnosis

`works` proves the skeleton does its job (slots 1+2 ⟹ SAT hard).  `toyCertificate` shows it is
inhabited.  `target_is_highOnSAT` shows that once slots 1 (structural) and 3 (self-reference) are
supplied, the *entire* remaining content is slot 2 — `P sat` — the specific, self-referential
incompressibility of SAT, i.e. `cost_super`.  A genuinely new idea has to fill **slot 2**: a rare,
self-referential property, proved to hold of SAT *by SAT's structure*, not by counting.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonNaturalSkeleton

/-- **The non-natural certificate**, with the three Razborov–Rudich slots.  `sat` is the target, `rnd`
a random function, `hard` the lower-bound predicate. -/
structure NonNaturalCertificate {Func : Type} (sat rnd : Func) (hard : Func → Prop) where
  /-- the property whose value on `sat` we must establish -/
  P : Func → Prop
  /-- **Slot 1 (useful)**: `P` is a lower bound.  Structural. -/
  useful : ∀ f, P f → hard f
  /-- **Slot 3 (rare / not-large)**: a random function lacks `P` — the non-naturalness. -/
  rare : ¬ P rnd
  /-- **Slot 2 (high on SAT)**: SAT has `P`.  THE OPEN SLOT (= `cost_super`). -/
  highOnSAT : P sat

/-- **The certificate does its job (proved).**  Slots 1 + 2 give the lower bound for SAT. -/
theorem works {Func : Type} {sat rnd : Func} {hard : Func → Prop}
    (C : NonNaturalCertificate sat rnd hard) : hard sat :=
  C.useful sat C.highOnSAT

/-- Modeling **largeness**: a property is *large* if the random function has it. -/
def Large {Func : Type} (P : Func → Prop) (rnd : Func) : Prop := P rnd

/-- **The certificate is not large (proved).**  Slot 3 (`rare`) is exactly `¬ Large` — the random
function lacks `P`. -/
theorem certificate_not_large {Func : Type} {sat rnd : Func} {hard : Func → Prop}
    (C : NonNaturalCertificate sat rnd hard) : ¬ Large C.P rnd :=
  C.rare

/-- **The Razborov–Rudich barrier (proved from its socket).**  If a property is *natural* (large ∧
constructive), it breaks crypto.  So, given crypto exists, no valid property is both large and
constructive — the certificate must drop one (here: largeness, via slot 3). -/
theorem non_natural_required (Large Constructive BreaksCrypto : Prop)
    (rr : Large ∧ Constructive → BreaksCrypto) (crypto : ¬ BreaksCrypto) :
    ¬ (Large ∧ Constructive) :=
  fun h => crypto (rr h)

/-- **Self-reference fills slot 3 (proved).**  If `P` is a self-referential property and the random
function is not self-referential, then the random function lacks `P` — the rare slot, for free.  This
is why self-reference is the lever: a coin-flip function definitionally has no self-referential
structure. -/
theorem rare_of_not_selfref {Func : Type} (SelfRef : Func → Prop) (rnd : Func)
    (h : ¬ SelfRef rnd) : ¬ (fun f => SelfRef f) rnd :=
  h

/-- **The target is slot 2 (proved).**  Given slot 1 (`useful`, structural) and slot 3 (`rare`, from
self-reference), the entire remaining content is `P sat → hard sat` — establishing `P sat` is the whole
job.  `P sat` — the specific, self-referential incompressibility of SAT — is `cost_super`. -/
theorem target_is_highOnSAT {Func : Type} (P hard : Func → Prop) (sat rnd : Func)
    (useful : ∀ f, P f → hard f) (rare : ¬ P rnd) :
    P sat → hard sat :=
  fun highOnSAT => useful sat highOnSAT

/-- **The skeleton is inhabited (consistency witness).**  On `Bool`, with `sat = true`, `rnd = false`,
`hard = (· = true)`, the property `P = (· = true)` fills all three slots: useful, rare (`¬ false = true`),
and high on `sat`. -/
def toyCertificate : NonNaturalCertificate (Func := Bool) true false (fun b => b = true) where
  P := fun b => b = true
  useful := fun _ h => h
  rare := fun h => Bool.noConfusion h
  highOnSAT := rfl

end PallLean.Paper93.DeepMath.PathB.NonNaturalSkeleton

#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalSkeleton.works
#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalSkeleton.certificate_not_large
#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalSkeleton.non_natural_required
#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalSkeleton.rare_of_not_selfref
#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalSkeleton.target_is_highOnSAT
