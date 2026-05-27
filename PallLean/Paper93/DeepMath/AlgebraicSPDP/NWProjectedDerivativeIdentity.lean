import PallLean.Paper93.DeepMath.AlgebraicSPDP.NWSupportIndependence
import PallLean.IterDerivHelpers
import PallLean.ProductDeriv
import PallLean.SymmetricPower
import Mathlib.Data.Finset.Dedup

/-!
# NW Projected Derivative Identity

This file attacks the remaining polynomial-calculus payload from
`NWSupportIndependence`: the projected derivative row identity for the concrete
Nisan-Wigderson polynomial.

The core is deliberately elementary.  We reduce the coefficient row of a
single NW monomial to the usual squarefree-product rule: differentiating a
product of distinct variables by a contained derivative set strips those
variables; differentiating by a missing variable gives zero.
-/

namespace PallLean.Paper93.DeepMath.AlgebraicSPDP

open scoped BigOperators
open MvPolynomial
open SPDP

section GraphDesign

variable {Label Point Value : Type*}
variable [Fintype Point] [DecidableEq Point] [DecidableEq Value]

/-- Encoded graph support for a codeword over a point window. -/
noncomputable def nwEncodedGraphOn
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) (a : Label) :
    Finset (Fin numVars) :=
  D.image fun x => enc (x, code a x)

/-- Encoded residual graph support for a codeword outside a point window. -/
noncomputable def nwEncodedGraphOff
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) (a : Label) :
    Finset (Fin numVars) :=
  (Finset.univ.filter fun x : Point => x ∉ D).image fun x =>
    enc (x, code a x)

/-- The squarefree monomial attached to a finite variable support. -/
noncomputable abbrev finSupportMonomial {numVars : Nat}
    (S : Finset (Fin numVars)) : Fin numVars →₀ Nat :=
  SymmetricPower.tagMonomial S

/-- Product of variables over a finite support is the corresponding
squarefree monomial. -/
theorem prod_X_eq_monomial_finSupport {numVars : Nat}
    (S : Finset (Fin numVars)) :
    S.prod (fun i => (X i : MvPolynomial (Fin numVars) ℚ)) =
      monomial (finSupportMonomial S) (1 : ℚ) := by
  rw [finSupportMonomial, SymmetricPower.tagMonomial,
    MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X]

/-- Coefficients of a pure squarefree product are Kronecker in the support. -/
theorem coeff_finSupport_prod_X {numVars : Nat}
    (S T : Finset (Fin numVars)) :
    coeff (finSupportMonomial S)
        (T.prod (fun i => (X i : MvPolynomial (Fin numVars) ℚ))) =
      if S = T then (1 : ℚ) else 0 := by
  rw [prod_X_eq_monomial_finSupport]
  rw [MvPolynomial.coeff_monomial]
  by_cases hST : S = T
  · subst hST
    simp
  · have hmono : finSupportMonomial T ≠ finSupportMonomial S := by
      intro h
      exact hST (SymmetricPower.tagMonomial_injective h.symm)
    simp [hST, hmono]

/-- Coefficient projection through an injective encoding is Kronecker in the
original graph support. -/
theorem coeff_squarefreeSupport_prod_encoded
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (henc : Function.Injective enc)
    (m S : Finset (Point × Value)) :
    coeff (squarefreeSupportExponent enc m)
        ((S.image enc).prod fun i => (X i : MvPolynomial (Fin numVars) ℚ)) =
      if m = S then (1 : ℚ) else 0 := by
  classical
  have hm :
      squarefreeSupportExponent enc m = finSupportMonomial (m.image enc) := by
    unfold squarefreeSupportExponent finSupportMonomial SymmetricPower.tagMonomial
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact henc hxy
  rw [hm, coeff_finSupport_prod_X]
  by_cases h : m = S
  · subst h
    simp
  · have himage : m.image enc ≠ S.image enc := by
      intro him
      exact h ((Finset.image_inj henc).mp him)
    simp [h, himage]

/-- The direct point-indexed NW monomial is the product over the encoded graph
support. -/
theorem nwMvMonomial_eq_encodedGraph_prod
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (a : Label)
    (henc : Function.Injective enc) :
    nwMvMonomial enc code a =
      (nwEncodedGraphOn enc code Finset.univ a).prod
        fun i => (X i : MvPolynomial (Fin numVars) ℚ) := by
  classical
  unfold nwMvMonomial nwEncodedGraphOn
  rw [Finset.prod_image]
  intro x _ y _ hxy
  exact congrArg Prod.fst (henc hxy)

/-- Differentiating a squarefree variable product by a contained variable
erases that factor. -/
theorem pderiv_prod_X_of_mem {numVars : Nat}
    (base : Finset (Fin numVars)) {i : Fin numVars}
    (hi : i ∈ base) :
    pderiv i (base.prod fun j => (X j : MvPolynomial (Fin numVars) ℚ)) =
      (base.erase i).prod fun j => (X j : MvPolynomial (Fin numVars) ℚ) := by
  rw [ProductDeriv.pderiv_prod_single (s := base)
    (f := fun j => (X j : MvPolynomial (Fin numVars) ℚ)) (i := i) (k := i) hi]
  · simp
  · intro j _ hj
    exact MvPolynomial.pderiv_X_of_ne hj

/-- Differentiating a squarefree variable product by a missing variable gives
zero. -/
theorem pderiv_prod_X_of_notMem {numVars : Nat}
    (base : Finset (Fin numVars)) {i : Fin numVars}
    (hi : i ∉ base) :
    pderiv i (base.prod fun j => (X j : MvPolynomial (Fin numVars) ℚ)) = 0 := by
  classical
  revert hi
  refine Finset.induction_on base ?_ ?_
  · intro _
    simp
  · intro a s has ih
    intro hi
    have hia : i ≠ a := by
      intro h
      exact hi (by simp [h])
    have his : i ∉ s := by
      intro hs
      exact hi (Finset.mem_insert_of_mem hs)
    rw [Finset.prod_insert has, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X_of_ne hia.symm, ih his]
    simp

/-- Iterated differentiation by a duplicate-free list contained in a
squarefree product support strips exactly those variables. -/
theorem iterDerivList_prod_X_of_list_subset {numVars : Nat}
    (L : List (Fin numVars)) (hL : L.Nodup) :
    ∀ base : Finset (Fin numVars), L.toFinset ⊆ base ->
      iterDerivList L (base.prod fun i => (X i : MvPolynomial (Fin numVars) ℚ)) =
        ((base \ L.toFinset).prod fun i => (X i : MvPolynomial (Fin numVars) ℚ)) := by
  classical
  induction L with
  | nil =>
      intro base _
      simp [iterDerivList]
  | cons a rest ih =>
      intro base hsub
      simp only [List.nodup_cons] at hL
      have ha_not : a ∉ rest := hL.1
      have hrest_nodup : rest.Nodup := hL.2
      rw [IterDerivHelpers.iterDerivList_cons]
      have ha_base : a ∈ base := hsub (by simp)
      rw [pderiv_prod_X_of_mem base ha_base]
      have hsub_erase : rest.toFinset ⊆ base.erase a := by
        intro x hx
        exact Finset.mem_erase.mpr
          ⟨fun hxa => ha_not (hxa ▸ (List.mem_toFinset.mp hx)),
            hsub (by simp [hx])⟩
      rw [ih hrest_nodup (base.erase a) hsub_erase]
      have hset : base.erase a \ rest.toFinset = base \ (a :: rest).toFinset := by
        ext x
        by_cases hxa : x = a
        · subst hxa
          simp
        · simp [Finset.mem_sdiff, hxa]
      rw [hset]

/-- If an iterated derivative list asks for a variable outside a squarefree
product support, the whole iterated derivative is zero. -/
theorem iterDerivList_prod_X_eq_zero_of_not_subset {numVars : Nat}
    (L : List (Fin numVars)) (base : Finset (Fin numVars))
    (hmiss : ¬ L.toFinset ⊆ base) :
    iterDerivList L (base.prod fun i => (X i : MvPolynomial (Fin numVars) ℚ)) = 0 := by
  classical
  rw [Finset.not_subset] at hmiss
  rcases hmiss with ⟨i, hiL, hibase⟩
  exact IterDerivHelpers.iterDerivList_eq_zero_of_mem_and_pderiv_zero
    L i (base.prod fun j => (X j : MvPolynomial (Fin numVars) ℚ))
    (List.mem_toFinset.mp hiL)
    (pderiv_prod_X_of_notMem base hibase)

omit [Fintype Point] [DecidableEq Value] in
/-- The concrete derivative list has exactly the encoded graph support of its
window. -/
theorem nwDerivativeWindowList_toFinset
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) (a : Label) :
    (nwDerivativeWindowList enc code D a).toFinset =
      nwEncodedGraphOn enc code D a := by
  classical
  unfold nwDerivativeWindowList nwEncodedGraphOn
  ext i
  rw [List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hi
    rcases List.mem_map.mp hi with ⟨x, hx, hxi⟩
    exact ⟨x, Finset.mem_toList.mp hx, hxi⟩
  · intro hi
    rcases hi with ⟨x, hx, hxi⟩
    exact List.mem_map.mpr ⟨x, Finset.mem_toList.mpr hx, hxi⟩

/-- Encoding the residual graph commutes with taking the residual graph in the
encoded variable set. -/
theorem nwEncodedGraphOff_eq_image
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) (a : Label) :
    nwEncodedGraphOff enc code D a = (nwGraphOff code D a).image enc := by
  classical
  simp [nwEncodedGraphOff, nwGraphOff, Finset.image_image, Function.comp_def]

/-- If label `a` and label `b` agree on the derivative window, then the
derivative support for `a` is contained in the full monomial support for `b`. -/
theorem nwDerivativeWindowList_subset_full_of_agrees
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) (a b : Label)
    (hagrees : ∀ x ∈ D, code a x = code b x) :
    (nwDerivativeWindowList enc code D a).toFinset ⊆
      nwEncodedGraphOn enc code Finset.univ b := by
  classical
  rw [nwDerivativeWindowList_toFinset]
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨x, hxD, rfl⟩
  exact Finset.mem_image.mpr ⟨x, by simp, by simp [hagrees x hxD]⟩

/-- Conversely, containment of the derivative support in a full encoded
codeword support forces agreement on the derivative window. -/
theorem agrees_of_nwDerivativeWindowList_subset_full
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) (a b : Label)
    (henc : Function.Injective enc)
    (hsub :
      (nwDerivativeWindowList enc code D a).toFinset ⊆
        nwEncodedGraphOn enc code Finset.univ b) :
    ∀ x ∈ D, code a x = code b x := by
  classical
  intro x hxD
  have hx :
      enc (x, code a x) ∈
        (nwDerivativeWindowList enc code D a).toFinset := by
    rw [nwDerivativeWindowList_toFinset]
    exact Finset.mem_image.mpr ⟨x, hxD, rfl⟩
  have hxfull := hsub hx
  rcases Finset.mem_image.mp hxfull with ⟨y, _hy, hy⟩
  have hprod : (x, code a x) = (y, code b y) := henc hy.symm
  have hxy : x = y := congrArg Prod.fst hprod
  have hval : code a x = code b y := congrArg Prod.snd hprod
  simpa [hxy] using hval

/-- The full encoded graph of `b`, after removing an agreeing derivative
window, is exactly the encoded residual graph of `b`. -/
theorem nwEncodedGraph_full_sdiff_window_of_agrees
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) (a b : Label)
    (henc : Function.Injective enc)
    (hagrees : ∀ x ∈ D, code a x = code b x) :
    nwEncodedGraphOn enc code Finset.univ b \
        (nwDerivativeWindowList enc code D a).toFinset =
      nwEncodedGraphOff enc code D b := by
  classical
  rw [nwDerivativeWindowList_toFinset]
  ext i
  constructor
  · intro hi
    rcases Finset.mem_sdiff.mp hi with ⟨hfull, hnotwin⟩
    rcases Finset.mem_image.mp hfull with ⟨x, _hx, hix⟩
    have hxnotD : x ∉ D := by
      intro hxD
      apply hnotwin
      exact Finset.mem_image.mpr
        ⟨x, hxD, by simpa [hagrees x hxD] using hix⟩
    exact Finset.mem_image.mpr
      ⟨x, by simp [hxnotD], hix⟩
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨x, hxoff, hix⟩
    have hxnotD : x ∉ D := (Finset.mem_filter.mp hxoff).2
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, by simp, hix⟩
    · intro hwin
      rcases Finset.mem_image.mp hwin with ⟨y, hyD, hyi⟩
      have hvars : (y, code a y) = (x, code b x) := by
        apply henc
        exact hyi.trans hix.symm
      have hyx : y = x := congrArg Prod.fst hvars
      exact hxnotD (hyx ▸ hyD)

/-- Coefficient row of one NW monomial after differentiating by a derivative
window.

If the monomial's label agrees with the derivative label on `D`, the derivative
strips exactly those variables and the coefficient projection sees the residual
graph.  Otherwise one requested derivative variable is missing, so the whole
iterated derivative vanishes. -/
theorem nwMvMonomial_projected_derivative_coeff
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point)
    (henc : Function.Injective enc)
    (a b : Label) (m : Finset (Point × Value)) :
    MvPolynomial.coeff (squarefreeSupportExponent enc m)
      (SPDP.iterDerivList (nwDerivativeWindowList enc code D a)
        (nwMvMonomial enc code b)) =
      if (∀ x ∈ D, code a x = code b x) ∧
          m = nwGraphOff code D b then (1 : ℚ) else 0 := by
  classical
  have hmono := nwMvMonomial_eq_encodedGraph_prod enc code b henc
  by_cases hagree : ∀ x ∈ D, code a x = code b x
  · rw [hmono]
    have hsub :=
      nwDerivativeWindowList_subset_full_of_agrees enc code D a b hagree
    have hnodup := nwDerivativeWindowList_nodup enc code D a henc
    rw [iterDerivList_prod_X_of_list_subset
      (nwDerivativeWindowList enc code D a) hnodup
      (nwEncodedGraphOn enc code Finset.univ b) hsub]
    rw [nwEncodedGraph_full_sdiff_window_of_agrees enc code D a b henc hagree]
    rw [nwEncodedGraphOff_eq_image]
    rw [coeff_squarefreeSupport_prod_encoded enc henc m (nwGraphOff code D b)]
    by_cases hm : m = nwGraphOff code D b
    · have hcond :
          (∀ x ∈ D, code a x = code b x) ∧
            m = nwGraphOff code D b := ⟨hagree, hm⟩
      rw [if_pos hm, if_pos hcond]
    · have hcond :
          ¬ ((∀ x ∈ D, code a x = code b x) ∧
              m = nwGraphOff code D b) := by
        intro h
        exact hm h.2
      rw [if_neg hm, if_neg hcond]
  · rw [hmono]
    have hmiss :
        ¬ (nwDerivativeWindowList enc code D a).toFinset ⊆
          nwEncodedGraphOn enc code Finset.univ b := by
      intro hsub
      exact hagree
        (agrees_of_nwDerivativeWindowList_subset_full enc code D a b henc hsub)
    rw [iterDerivList_prod_X_eq_zero_of_not_subset
      (nwDerivativeWindowList enc code D a)
      (nwEncodedGraphOn enc code Finset.univ b) hmiss]
    have hif :
        ¬ ((∀ x ∈ D, code a x = code b x) ∧
            m = nwGraphOff code D b) := by
      intro h
      exact hagree h.1
    simp [hif]

/-- The concrete NW projected derivative identity follows from injectivity of
the ambient variable encoding and injectivity of the codeword map. -/
theorem NWProjectedDerivativeRowIdentity.ofInjectiveEncodingAndCode
    [Fintype Label] [Fintype Value]
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point)
    (henc : Function.Injective enc)
    (hcode : Function.Injective code) :
    NWProjectedDerivativeRowIdentity enc code D :=
  NWProjectedDerivativeRowIdentity.ofMonomialCoefficientRows
    enc code D henc hcode
    (nwMvMonomial_projected_derivative_coeff enc code D henc)

/-- Concrete low-agreement NW certificate for the actual encoded NW polynomial,
with the projected derivative-row identity discharged from injective encoding
and injective codewords.

This closes the modest unshifted/window-row bridge: the only remaining inputs
are the ordinary NW design facts (`hD`, `hOutside`, `hlow`) and the support
count calibration. -/
noncomputable def NWSPDPIndependenceCertificate.ofLowAgreementNWPolynomial_injective
    [Fintype Label] [Fintype Value]
    {numVars degree kappa ell : Nat}
    (support : NWLeadingSupportData)
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound : Nat)
    (support_lower_le_labels : support.lower <= Fintype.card Label)
    (hD : overlapBound < D.card)
    (hOutside :
      overlapBound < (Finset.univ.filter fun x : Point => x ∉ D).card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound)
    (hDcard : D.card = kappa)
    (henc : Function.Injective enc)
    (hcode : Function.Injective code) :
    NWSPDPIndependenceCertificate numVars degree kappa ell :=
  NWSPDPIndependenceCertificate.ofLowAgreementNWPolynomial
    support enc code D overlapBound support_lower_le_labels hD hOutside hlow
    hDcard
    (NWProjectedDerivativeRowIdentity.ofInjectiveEncodingAndCode
      enc code D henc hcode)

/-! ## Axiom audit -/

#print axioms coeff_squarefreeSupport_prod_encoded
#print axioms nwMvMonomial_eq_encodedGraph_prod
#print axioms iterDerivList_prod_X_of_list_subset
#print axioms iterDerivList_prod_X_eq_zero_of_not_subset
#print axioms nwMvMonomial_projected_derivative_coeff
#print axioms NWProjectedDerivativeRowIdentity.ofInjectiveEncodingAndCode
#print axioms NWSPDPIndependenceCertificate.ofLowAgreementNWPolynomial_injective

end GraphDesign

end PallLean.Paper93.DeepMath.AlgebraicSPDP
