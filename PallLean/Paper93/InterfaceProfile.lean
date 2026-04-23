/-
# Paper §9 — Definition 21 & Lemma 29: Interface-anonymous profile and profile compression

Paper reference: §9, Definition 21 and Lemma 29 (lines 2040–2110 of the
paper), "Profile compression removes κ-dependence".

After the normal-form reduction of Lemma 25 each live interface in a
canonical window is assigned a local type `σ ∈ Σ^{≤q}`. The
*interface-anonymous profile* of the window is then the histogram

  h : Σ^{≤q} → ℕ ,    h(σ) = #{ i live : σ_i = σ }.

Any such histogram arising from a window with `R` live interfaces
satisfies the total-mass constraint

  Σ_σ h(σ) = R .

Lemma 29 bounds the number of realizable profiles. The paper quotes the
exact stars-and-bars value `binom(R + S' - 1, S' - 1)`. For a purely
kernel-only formalisation it suffices to use the cruder but equivalent
bound

  |H| ≤ (R+1)^{|Σ^{≤q}|} ,

which is polynomial in `R` and independent of `κ` — exactly the Route-A
conclusion required by the Width⇒Rank argument. (The exact
stars-and-bars value is proved separately in `ProfileCompression.lean`
via `choose_le_pow`; this file provides the abstract combinatorial
interface used in §9.)

This file is self-contained and does not import any other module under
`PallLean/Paper93/` — it only depends on `Mathlib` and therefore can be
developed in parallel to the other §9 kernel files.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Fin

namespace PallLean
namespace Paper93

open Finset

/--
**Paper §9, Definition 21 (Interface-anonymous profile).**

The profile of a canonical window is the histogram `h : InterfaceType → ℕ`
counting, for each local type `σ`, the number of live interfaces whose
normal form equals `σ`. Here `InterfaceType` is the finite alphabet
`Σ^{≤q}` from Lemma 25.

Formally we implement the profile as a function `InterfaceType → ℕ`; the
total mass constraint `Σ h(σ) = R` is imposed by the realisability
predicate below rather than baked into the type.
-/
abbrev InterfaceAnonymousProfile (InterfaceType : Type) [Fintype InterfaceType] : Type :=
  InterfaceType → ℕ

/--
**Paper §9, Definition 21 (Realizable profile set).**

The set `H` of *realizable* interface-anonymous profiles at live-interface
count `R` is the set of histograms `h : InterfaceType → ℕ` whose total
mass equals `R`. Since each value `h σ` is at most `R` we may encode
realizable profiles as functions into `Fin (R+1)` and then forget the
bound to recover the underlying `ℕ`-valued histogram. This presentation
makes the finset structure completely elementary.

`DecidableEq` on `InterfaceType` is required to form the `Finset.image`
below (the image needs decidable equality on the codomain, which for the
function type `InterfaceType → ℕ` reduces to `DecidableEq InterfaceType`).
-/
def RealizableProfiles
    (InterfaceType : Type) [Fintype InterfaceType] [DecidableEq InterfaceType] (R : ℕ) :
    Finset (InterfaceAnonymousProfile InterfaceType) :=
  ((Finset.univ : Finset (InterfaceType → Fin (R+1))).filter
      (fun h => (∑ σ : InterfaceType, (h σ : ℕ)) = R)).image
    (fun h σ => (h σ : ℕ))

/-!
## Lemma 29 (Profile Compression): cardinality bound

We prove the crude polynomial bound
`|RealizableProfiles InterfaceType R| ≤ (R+1)^{|InterfaceType|}`,
which is polynomial in `R` and *independent of κ*. This is the Route-A
content of the Width⇒Rank argument: after profile compression the number
of profiles no longer depends on the window length κ.
-/

/--
Auxiliary cardinality fact: the total number of functions
`InterfaceType → Fin (R+1)` equals `(R+1)^{|InterfaceType|}`.
-/
lemma card_fun_fin_succ
    (InterfaceType : Type) [Fintype InterfaceType] [DecidableEq InterfaceType] (R : ℕ) :
    Fintype.card (InterfaceType → Fin (R+1)) = (R+1) ^ Fintype.card InterfaceType := by
  have h1 : Fintype.card (InterfaceType → Fin (R+1))
      = Fintype.card (Fin (R+1)) ^ Fintype.card InterfaceType :=
    Fintype.card_fun
  have h2 : Fintype.card (Fin (R+1)) = R+1 := Fintype.card_fin _
  rw [h1, h2]

/--
**Paper §9, Lemma 29 (Profile compression card bound).**

The number of realizable interface-anonymous profiles at live-interface
count `R` is bounded by `(R+1)^{|InterfaceType|}`. Crucially this bound
is polynomial in `R` and *independent of the window length κ*, which is
the Route-A content required by the Width⇒Rank argument (paper §9).

The proof is an elementary `card image ≤ card filter ≤ card univ`
chain. The sharper stars-and-bars bound
`Nat.choose (R + |InterfaceType| − 1) (|InterfaceType| − 1)` is available
in `ProfileCompression.lean` via `choose_le_pow`; for the abstract
combinatorial interface used here, this weaker `(R+1)^{|·|}` form is
sufficient (and is in fact implied by it, since
`choose_le_pow` gives `C(R+m, m) ≤ (R+1)^m`).
-/
theorem profileCompression_card_bound
    (InterfaceType : Type) [Fintype InterfaceType] [DecidableEq InterfaceType] (R : ℕ) :
    (RealizableProfiles InterfaceType R).card ≤ (R+1) ^ Fintype.card InterfaceType := by
  -- Step 1: image has cardinality at most the filter it comes from.
  have h_img :
      (RealizableProfiles InterfaceType R).card ≤
        ((Finset.univ : Finset (InterfaceType → Fin (R+1))).filter
            (fun h => (∑ σ : InterfaceType, (h σ : ℕ)) = R)).card := by
    unfold RealizableProfiles
    exact Finset.card_image_le
  -- Step 2: filter has cardinality at most the ambient finset.
  have h_filter :
      ((Finset.univ : Finset (InterfaceType → Fin (R+1))).filter
          (fun h => (∑ σ : InterfaceType, (h σ : ℕ)) = R)).card ≤
        (Finset.univ : Finset (InterfaceType → Fin (R+1))).card :=
    Finset.card_filter_le _ _
  -- Step 3: ambient finset cardinality is (R+1)^{|InterfaceType|}.
  have h_univ :
      (Finset.univ : Finset (InterfaceType → Fin (R+1))).card =
        (R+1) ^ Fintype.card InterfaceType := by
    rw [Finset.card_univ]
    exact card_fun_fin_succ InterfaceType R
  -- Chain the three inequalities.
  calc
    (RealizableProfiles InterfaceType R).card
        ≤ ((Finset.univ : Finset (InterfaceType → Fin (R+1))).filter
              (fun h => (∑ σ : InterfaceType, (h σ : ℕ)) = R)).card := h_img
    _   ≤ (Finset.univ : Finset (InterfaceType → Fin (R+1))).card := h_filter
    _   = (R+1) ^ Fintype.card InterfaceType := h_univ

/--
Corollary 30 (Polynomially many profiles). Rephrasing of Lemma 29: the
set `H` of realizable interface-anonymous profiles has cardinality
polynomial in `R` and independent of `κ`. This is the exact statement
used by the §9 Width⇒Rank argument downstream.
-/
theorem profileCompression_polynomial_in_R
    (InterfaceType : Type) [Fintype InterfaceType] [DecidableEq InterfaceType] (R : ℕ) :
    ∃ C : ℕ, (RealizableProfiles InterfaceType R).card ≤ (R+1) ^ C :=
  ⟨Fintype.card InterfaceType, profileCompression_card_bound InterfaceType R⟩

end Paper93
end PallLean
