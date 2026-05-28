import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignedThreeCNFModel

/-!
# Resolution width/size substrate

**STATUS: REAL PROOF-SYSTEM SUBSTRATE, NOT THE FULL BSW THEOREM.**

The expander-Tseitin files prove the expansion/width kernel.  The next step is
the proof-complexity layer: clauses, resolution derivations, proof size, and
proof width.  This file formalizes that layer and proves the basic accounting
facts needed by any future Ben-Sasson--Wigderson size-width formalization.

What is proved here:

* finite clauses as finite sets of literals;
* the resolution resolvent operation;
* resolution derivation trees from an axiom predicate;
* proof size and proof width;
* a resolvent has width at most the sum of its parent widths;
* the root clause width is bounded by the derivation width;
* bounded-width impossibility follows from a width lower bound;
* signed 3-CNF clauses embed as resolution clauses of width at most `3`.

What is **not** proved here:

* the full BSW theorem `width lower bound -> exponential resolution size`.

That theorem requires substantially more machinery: refutation DAGs or
tree-like-to-DAG accounting, restrictions/random restrictions, and the
Ben-Sasson--Wigderson size-width argument.  This file deliberately does not
introduce it as a free `Prop` field.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-! ## Clauses and resolution -/

/-- A resolution clause is a finite set of literals. -/
abbrev ResolutionClause (Lit : Type*) := Finset Lit

namespace ResolutionClause

variable {Lit : Type*} [DecidableEq Lit]

/-- Clause width is the number of distinct literals in the clause. -/
def width (C : ResolutionClause Lit) : Nat :=
  C.card

/-- The resolution resolvent of parent clauses `C` and `D` at pivot `p`.

This operation erases `p` from `C`, erases its complement from `D`, and unions
the remaining literals.  The side conditions saying that the pivot actually
appears in the parents are kept outside this operation; this lets the proof
system record deliberately broad syntactic derivations while width accounting
stays total. -/
def resolvent (compl : Lit -> Lit)
    (C D : ResolutionClause Lit) (p : Lit) : ResolutionClause Lit :=
  (C.erase p) ∪ (D.erase (compl p))

/-- A resolvent has width at most the sum of the widths of its parents. -/
theorem width_resolvent_le
    (compl : Lit -> Lit) (C D : ResolutionClause Lit) (p : Lit) :
    width (resolvent compl C D p) <= width C + width D := by
  unfold width resolvent
  have hC : (C.erase p).card <= C.card := by
    exact Finset.card_erase_le
  have hD : (D.erase (compl p)).card <= D.card := by
    exact Finset.card_erase_le
  calc
    ((C.erase p) ∪ (D.erase (compl p))).card
        <= (C.erase p).card + (D.erase (compl p)).card :=
      Finset.card_union_le _ _
    _ <= C.card + D.card := by
      exact Nat.add_le_add hC hD

end ResolutionClause

/-! ## Derivation trees -/

universe u

/-- Tree-like resolution derivations from an axiom predicate. -/
inductive ResolutionDerivation
    {Lit : Type u} [DecidableEq Lit]
    (compl : Lit -> Lit)
    (Axiom : ResolutionClause Lit -> Prop) :
    ResolutionClause Lit -> Type u where
  | ax {C : ResolutionClause Lit} :
      Axiom C -> ResolutionDerivation compl Axiom C
  | resolve {C D : ResolutionClause Lit} :
      ResolutionDerivation compl Axiom C ->
      ResolutionDerivation compl Axiom D ->
      (p : Lit) ->
      ResolutionDerivation compl Axiom
        (ResolutionClause.resolvent compl C D p)

namespace ResolutionDerivation

variable {Lit : Type*} [DecidableEq Lit]
variable {compl : Lit -> Lit}
variable {Axiom : ResolutionClause Lit -> Prop}

/-- Number of nodes in the tree-like derivation. -/
def size {C : ResolutionClause Lit}
    (D : ResolutionDerivation compl Axiom C) : Nat :=
  match D with
  | ax _ => 1
  | resolve L R _ => size L + size R + 1

/-- Maximum clause width appearing in the tree-like derivation. -/
def proofWidth {C : ResolutionClause Lit}
    (D : ResolutionDerivation compl Axiom C) : Nat :=
  match D with
  | ax (C := C) _ => ResolutionClause.width C
  | resolve (C := C) (D := Dparent) L R p =>
      max (max (proofWidth L) (proofWidth R))
        (ResolutionClause.width
          (ResolutionClause.resolvent compl C Dparent p))

@[simp] theorem size_ax {C : ResolutionClause Lit} (h : Axiom C) :
    size (ResolutionDerivation.ax (compl := compl) h) = 1 :=
  rfl

@[simp] theorem size_resolve
    {C D : ResolutionClause Lit}
    (L : ResolutionDerivation compl Axiom C)
    (R : ResolutionDerivation compl Axiom D)
    (p : Lit) :
    size (ResolutionDerivation.resolve L R p) =
      size L + size R + 1 :=
  rfl

theorem size_pos {C : ResolutionClause Lit}
    (D : ResolutionDerivation compl Axiom C) :
    0 < size D := by
  induction D with
  | ax _ => simp [size]
  | resolve L R p ihL ihR =>
      simp [size]

@[simp] theorem proofWidth_ax {C : ResolutionClause Lit} (h : Axiom C) :
    proofWidth (ResolutionDerivation.ax (compl := compl) h) =
      ResolutionClause.width C :=
  rfl

@[simp] theorem proofWidth_resolve
    {C D : ResolutionClause Lit}
    (L : ResolutionDerivation compl Axiom C)
    (R : ResolutionDerivation compl Axiom D)
    (p : Lit) :
    proofWidth (ResolutionDerivation.resolve L R p) =
      max (max (proofWidth L) (proofWidth R))
        (ResolutionClause.width
          (ResolutionClause.resolvent compl C D p)) :=
  rfl

/-- The root clause has width at most the derivation width. -/
theorem root_width_le_proofWidth {C : ResolutionClause Lit}
    (D : ResolutionDerivation compl Axiom C) :
    ResolutionClause.width C <= proofWidth D := by
  induction D with
  | ax h =>
      simp [proofWidth]
  | resolve L R p ihL ihR =>
      simp [proofWidth]

/-- Both parents' proof widths are bounded by the proof width of a resolution
node. -/
theorem left_proofWidth_le_resolve
    {C D : ResolutionClause Lit}
    (L : ResolutionDerivation compl Axiom C)
    (R : ResolutionDerivation compl Axiom D)
    (p : Lit) :
    proofWidth L <= proofWidth (ResolutionDerivation.resolve L R p) := by
  calc
    proofWidth L <= max (proofWidth L) (proofWidth R) :=
      le_max_left _ _
    _ <=
        max (max (proofWidth L) (proofWidth R))
          (ResolutionClause.width
            (ResolutionClause.resolvent compl C D p)) :=
      le_max_left _ _

theorem right_proofWidth_le_resolve
    {C D : ResolutionClause Lit}
    (L : ResolutionDerivation compl Axiom C)
    (R : ResolutionDerivation compl Axiom D)
    (p : Lit) :
    proofWidth R <= proofWidth (ResolutionDerivation.resolve L R p) := by
  calc
    proofWidth R <= max (proofWidth L) (proofWidth R) :=
      le_max_right _ _
    _ <=
        max (max (proofWidth L) (proofWidth R))
          (ResolutionClause.width
            (ResolutionClause.resolvent compl C D p)) :=
      le_max_left _ _

end ResolutionDerivation

/-! ## Width lower-bound interface -/

/-- A width lower bound for deriving a target clause from an axiom predicate. -/
def ResolutionWidthLowerBound
    {Lit : Type*} [DecidableEq Lit]
    (compl : Lit -> Lit)
    (Axiom : ResolutionClause Lit -> Prop)
    (Target : ResolutionClause Lit)
    (w : Nat) : Prop :=
  forall D : ResolutionDerivation compl Axiom Target,
    w <= D.proofWidth

/-- All axioms have width at most `k`. -/
def AxiomsWidthAtMost
    {Lit : Type*} [DecidableEq Lit]
    (Axiom : ResolutionClause Lit -> Prop)
    (k : Nat) : Prop :=
  forall C : ResolutionClause Lit, Axiom C -> ResolutionClause.width C <= k

/-- Once a real width lower bound is proved, no derivation below that width can
exist.  This is only the elimination wrapper; the lower bound itself must come
from a proof-complexity argument such as the expander-Tseitin kernel plus BSW. -/
theorem no_derivation_of_width_lt_lower_bound
    {Lit : Type*} [DecidableEq Lit]
    {compl : Lit -> Lit}
    {Axiom : ResolutionClause Lit -> Prop}
    {Target : ResolutionClause Lit}
    {w b : Nat}
    (H : ResolutionWidthLowerBound compl Axiom Target w)
    (hgap : b < w) :
    Not (exists D : ResolutionDerivation compl Axiom Target,
      D.proofWidth <= b) := by
  rintro ⟨D, hD⟩
  have hw : w <= D.proofWidth := H D
  have : w <= b := Nat.le_trans hw hD
  exact Nat.not_lt_of_ge this hgap

/-- First tiny width-to-size consequence.

If every axiom is `k`-narrow but every derivation of `Target` must have width
at least `w > k`, then no derivation of `Target` can be a single axiom line.
For tree-like resolution, any non-axiom derivation has at least two subproofs
and one resolution node, hence size at least `3`.

This is intentionally modest.  The exponential BSW size lower bound is much
deeper; this lemma only establishes the first honest size consequence of a
strict width gap. -/
theorem derivation_size_ge_three_of_width_lower_bound_gt_axioms
    {Lit : Type*} [DecidableEq Lit]
    {compl : Lit -> Lit}
    {Axiom : ResolutionClause Lit -> Prop}
    {Target : ResolutionClause Lit}
    {k w : Nat}
    (Hax : AxiomsWidthAtMost Axiom k)
    (Hwidth : ResolutionWidthLowerBound compl Axiom Target w)
    (hgap : k < w)
    (D : ResolutionDerivation compl Axiom Target) :
    3 <= D.size := by
  cases D with
  | ax h =>
      have hw : w <= ResolutionDerivation.proofWidth
          (ResolutionDerivation.ax (compl := compl) h) :=
        Hwidth (ResolutionDerivation.ax (compl := compl) h)
      have hk : ResolutionClause.width Target <= k := Hax Target h
      simp [ResolutionDerivation.proofWidth] at hw
      omega
  | resolve L R p =>
      have hL : 0 < L.size := L.size_pos
      have hR : 0 < R.size := R.size_pos
      simp [ResolutionDerivation.size]
      omega

/-! ## Signed 3-CNF clauses as resolution clauses -/

namespace SignedLiteral

/-- Boolean complement of a signed literal. -/
def compl {n : Nat} : SignedLiteral n -> SignedLiteral n
  | pos i => neg i
  | neg i => pos i

theorem compl_involutive {n : Nat} (l : SignedLiteral n) :
    compl (compl l) = l := by
  cases l <;> rfl

end SignedLiteral

namespace SignedClause3

/-- Forget ordering and repetitions in a signed 3-CNF clause, viewing it as a
resolution clause. -/
def toResolutionClause {n : Nat}
    (c : SignedClause3 n) : ResolutionClause (SignedLiteral n) :=
  {c.lit1, c.lit2, c.lit3}

/-- Every signed 3-CNF clause has resolution width at most `3`. -/
theorem toResolutionClause_width_le_three {n : Nat}
    (c : SignedClause3 n) :
    ResolutionClause.width c.toResolutionClause <= 3 := by
  unfold toResolutionClause ResolutionClause.width
  have h1 : ({c.lit1, c.lit2, c.lit3} : Finset (SignedLiteral n)).card <=
      ({c.lit2, c.lit3} : Finset (SignedLiteral n)).card + 1 :=
    Finset.card_insert_le _ _
  have h2 : ({c.lit2, c.lit3} : Finset (SignedLiteral n)).card <=
      ({c.lit3} : Finset (SignedLiteral n)).card + 1 :=
    Finset.card_insert_le _ _
  have h3 : ({c.lit3} : Finset (SignedLiteral n)).card <= 1 := by
    simp
  omega

end SignedClause3

/-! ## Kernel-only axiom trace -/

#print axioms ResolutionClause.width_resolvent_le
#print axioms ResolutionDerivation.size_pos
#print axioms ResolutionDerivation.root_width_le_proofWidth
#print axioms ResolutionDerivation.left_proofWidth_le_resolve
#print axioms ResolutionDerivation.right_proofWidth_le_resolve
#print axioms no_derivation_of_width_lt_lower_bound
#print axioms derivation_size_ge_three_of_width_lower_bound_gt_axioms
#print axioms SignedLiteral.compl_involutive
#print axioms SignedClause3.toResolutionClause_width_le_three

end PallLean.Paper93.DeepMath.PathB
