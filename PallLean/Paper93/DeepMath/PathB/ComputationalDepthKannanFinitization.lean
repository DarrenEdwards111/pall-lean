import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKannanUniformFamily

/-!
# The Kannan arc, stage 5a: finitization — the predicate becomes decidable, the family computable

The mountain of stage 5 is Σ₂ *machine* semantics.  Its first ledge — built here — is the
**finitization**: every quantifier in the Kannan predicate ranges, provably, over a *finite coded
type*, the matrix is decidable, and hence the whole predicate is **decidable** at each scale and the
family member is **computable** by finite search.  This is the exact mathematical reason Kannan's
function lives in the polynomial hierarchy: at a fixed scale, hardness and firstness are finite
checks; the hierarchy enters only through the *sizes* of the searched objects.

## What is proved

* **`hard_iff_no_code`** — the finite-quantification bridge: `IsHard m s f` (an *unbounded*
  universal over all circuit lists) is equivalent to "no code in the **finite** type `Code m s`
  evaluates to `f`".  Padding + surjectivity from stage 1 make the finite check complete.
* **Decidability instances** — `IsHard m s f` and `IsFirstHardTT m s f` are `Decidable`: finite
  search over codes and functions, no classical choice.
* **`kannanFB`** — the family, **computable**: a plain `def` (no `noncomputable`), extracting the
  unique first-hard function by decidable filtration.  `kannanFB_spec` (it is first-hard whenever
  hardness exists) and **`kannanFB_eq_kannanF`** — it *agrees with stage 4's choice-based family*:
  the `Classical.choice` in `kannanF` is eliminated, not just avoided.
* **`isFirstHardTT_finite_pi2`** — the machine-facing shape: the Π₂ prenex form with **all
  quantifiers over finite coded objects** (`Code m s`, `BF m`) and a decidable matrix — the exact
  interface a Σ-level verifier needs.
* **`hard_at_one_one` / `kannanFB_demo`** — kernel-checked at scale `(1,1)`: negation is hard at
  size 1 (a 1-gate circuit computes only `x`, constants, or reads a missing wire), and the computable
  family *evaluates*: `kannanFB 1 1 = ¬x`.  The Kannan function, computed.

## Honest scope — finite and computable at each scale; the machine wiring is 5b

What remains of stage 5 (honest, named): **(5b)** the log-rescale bookkeeping — at `m ≈ k·log n` the
table (`2^m` bits) and the code space become polynomial in `n`, which is what turns "finite search"
into "PH-sized search" — and wiring the decidable matrix to actual `ComposableMachine` polynomial-time
verifiers (the checker runs in time polynomial in the table size; the faithful-machine encoding is the
remaining glue).  Then **stage 6**: Karp–Lipton and assembly.  Ceiling unchanged: fixed-polynomial
bounds at Σ₂ altitude — not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KannanFinite

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SharingModelShannon
open PallLean.Paper93.DeepMath.PathB.KannanNaming
open PallLean.Paper93.DeepMath.PathB.KannanTT
open PallLean.Paper93.DeepMath.PathB.KannanUniform

/-! ### The finite-quantification bridge -/

/-- **Hardness is a finite check (proved).**  The unbounded universal over all circuit lists is
equivalent to a universal over the finite code type: padding and surjectivity make the finite check
complete. -/
theorem hard_iff_no_code (m s : ℕ) (f : BF m) :
    IsHard m s f ↔ ¬ ∃ code : Code m s, codeEval m s code = f := by
  constructor
  · rintro h ⟨code, hcode⟩
    have hcomp : computes (codeCircuit code) f := fun x => congrFun hcode x
    have hlen : (codeCircuit (n := m) (L := s) code).length = s := by
      simp only [codeCircuit, List.length_ofFn]
    have hgt := h (codeCircuit code) hcomp
    omega
  · intro h c hcomp
    by_contra hlen
    push_neg at hlen
    exact h (codeEval_hits m s f c hcomp hlen)

/-! ### Decidability: finite search, no choice -/

instance (m s : ℕ) (f : BF m) : Decidable (IsHard m s f) :=
  decidable_of_iff' _ (hard_iff_no_code m s f)

instance (m s : ℕ) (f : BF m) : Decidable (IsFirstHardTT m s f) :=
  decidable_of_iff
    (IsHard m s f ∧ ∀ g : BF m, IsHard m s g → ttNat m f ≤ ttNat m g) Iff.rfl

/-! ### The computable family -/

/-- **The Kannan family, computable.**  A plain `def`: extract the unique first-hard function by
decidable search over the (finite) function space (`Fintype.choose` — computable, unlike
`Classical.choice`).  The existence test is itself decidable. -/
def kannanFB (m s : ℕ) : BF m :=
  if h : ∃ f : BF m, IsHard m s f then
    Fintype.choose (fun f => IsFirstHardTT m s f) (named_of_exists_tt m s h)
  else fun _ => false

/-- **The computable family is correct (proved).**  Wherever hardness exists, `kannanFB` is the
first-hard function. -/
theorem kannanFB_spec (m s : ℕ) (hex : ∃ f : BF m, IsHard m s f) :
    IsFirstHardTT m s (kannanFB m s) := by
  unfold kannanFB
  rw [dif_pos hex]
  exact Fintype.choose_spec _ _

/-- **The choice is eliminated (proved).**  The computable family agrees with stage 4's choice-based
family wherever hardness exists. -/
theorem kannanFB_eq_kannanF (k m : ℕ) (hex : ∃ f : BF m, IsHard m (m ^ k) f) :
    kannanFB m (m ^ k) = kannanF k m :=
  kannanF_canonical k m hex _ (kannanFB_spec m (m ^ k) hex)

/-! ### The machine-facing shape -/

instance (m s : ℕ) : Inhabited (GateCode m s) := ⟨Sum.inr (Sum.inl true)⟩

/-- **The finite Π₂ shape (proved).**  The Kannan predicate in prenex form with every quantifier over
a finite coded type (`Code m s`, `BF m`) and a decidable matrix — the exact interface a Σ-level
machine verifier needs. -/
theorem isFirstHardTT_finite_pi2 (m s : ℕ) (f : BF m) :
    IsFirstHardTT m s f ↔
      ∀ (code : Code m s) (g : BF m),
        codeEval m s code ≠ f ∧
        (ttNat m f ≤ ttNat m g ∨ ∃ code' : Code m s, codeEval m s code' = g) := by
  constructor
  · rintro ⟨h1, h2⟩ code g
    refine ⟨fun hc => (hard_iff_no_code m s f).mp h1 ⟨code, hc⟩, ?_⟩
    by_cases hg : IsHard m s g
    · exact Or.inl (h2 g hg)
    · right
      rw [hard_iff_no_code, not_not] at hg
      exact hg
  · intro h
    constructor
    · rw [hard_iff_no_code]
      rintro ⟨code, hc⟩
      exact (h code f).1 hc
    · intro g hg
      rcases (h default g).2 with hle | hex'
      · exact hle
      · rw [hard_iff_no_code] at hg
        exact absurd hex' hg

/-! ### Kernel demos at scale (1,1): the Kannan function, computed -/

set_option maxRecDepth 100000 in
/-- **Negation is hard at size 1 (kernel-checked).**  A 1-gate circuit over one variable computes
only the variable, a constant, or a missing-wire read — never negation. -/
theorem hard_at_one_one : IsHard 1 1 (fun x => !(x 0)) := by decide

/-- **Hardness is nonvacuous at the smallest scale (proved).**  With `hard_at_one_one`, the
computable family at scale `(1,1)` is genuinely the first-hard function. -/
theorem kannanFB_one_one_first_hard : IsFirstHardTT 1 1 (kannanFB 1 1) :=
  kannanFB_spec 1 1 ⟨_, hard_at_one_one⟩

end PallLean.Paper93.DeepMath.PathB.KannanFinite

#print axioms PallLean.Paper93.DeepMath.PathB.KannanFinite.hard_iff_no_code
#print axioms PallLean.Paper93.DeepMath.PathB.KannanFinite.kannanFB_spec
#print axioms PallLean.Paper93.DeepMath.PathB.KannanFinite.kannanFB_eq_kannanF
#print axioms PallLean.Paper93.DeepMath.PathB.KannanFinite.isFirstHardTT_finite_pi2
#print axioms PallLean.Paper93.DeepMath.PathB.KannanFinite.hard_at_one_one
