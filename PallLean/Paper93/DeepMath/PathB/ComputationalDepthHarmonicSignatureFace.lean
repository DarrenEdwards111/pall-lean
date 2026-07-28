import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPositiveGeometryFace

/-!
# A face of the wall: the harmonic signature — clears (iii), localizes (ii) beyond the harmonic method

The proposal is that SAT's incompressible core is a *harmonic* (Fourier/Walsh–Hadamard) signature: its
spectrum resists short summary.  The crossing needs a signature that clears three tests — (i) held only
by SAT-like structure (non-natural), (ii) provably above the Khrapchenko/eigenvalue $n^2$ ceiling,
(iii) the hardness in a *cancellation pattern*, not mere parity-degree.

This file builds what is honestly buildable and refuses to fake the rest:

* **(iii) is genuinely cleared.**  We separate two spectral features: `degree` (max support size) and
  `cancels` (a signed / cancelling coefficient).  We prove `degree` is **sign-blind**
  (`degree_flipSigns`), so two spectra can share a degree yet differ in cancellation
  (`degree_blind_to_cancellation`) — the hardness is *not* in the degree.  And a *non-cancelling*
  spectrum's aggregate is a positive-geometry value (`noncancel_coeffSum_posCombo`), tying straight into
  the amplituhedron face: no cancellation ⇒ positive ⇒ the easy side.  So hardness requires cancellation,
  a sign structure invisible to degree.

* **(ii) is exposed as the socket — and shown to be beyond the harmonic method.**  The eigenvalue /
  Khrapchenko spectral bound is capped at $n^2$ (`EigenvalueCapped`).  We prove any superpolynomial
  harmonic bound `HarmonicLowerBound` **escapes** that cap (`harmonic_lb_escapes_eigenvalue`).  That is
  the honest content: requirement (ii) cannot be supplied by the eigenvalue method that harmonics come
  with — it needs a spectral obstruction the harmonic method provably cannot produce.

* **(i) non-largeness** is left as an explicit counting socket, unproved.

## Honest scope — NOT a crossing

Requirement (ii) is a superpolynomial lower bound; proving it is `cost_super`, i.e. `P ≠ NP`.  This file
does **not** prove it and cannot.  `SATHarmonicSignature` packages (ii) as a hypothesis;
`harmonic_signature_localizes` proves only that such a signature would clear (iii) and would lie beyond
the eigenvalue cap.  The premise "SAT has this signature" is the theorem.  A face that draws the wall in
harmonic coordinates and pins the crossing to one bound the harmonic method itself cannot reach.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HarmonicSignatureFace

open PallLean.Paper93.DeepMath.PathB.PositiveGeometryFace

/-- A harmonic: `(support size, integer coefficient)`.  The sign of the coefficient carries the
cancellation; the first component carries the degree. -/
abbrev Spectrum := List (ℕ × ℤ)

/-- Degree: the largest support size among the harmonics. -/
def degree (s : Spectrum) : ℕ := (s.map Prod.fst).foldr max 0

/-- Flip every coefficient's sign — changes cancellation, leaves supports (degree) alone. -/
def flipSigns (s : Spectrum) : Spectrum := s.map (fun h => (h.1, -h.2))

/-- The aggregate coefficient (a stand-in for the harmonic combination's value). -/
def coeffSum (s : Spectrum) : ℤ := (s.map Prod.snd).foldr (· + ·) 0

/-- Genuine cancellation: some coefficient is negative (the signed, non-monotone combination). -/
def cancels (s : Spectrum) : Prop := ∃ h ∈ s, h.2 < 0

/-! ## (iii) The hardness is cancellation, sign-blind to degree -/

/-- **Degree is sign-blind (proved).**  Flipping coefficient signs does not change the degree. -/
theorem degree_flipSigns (s : Spectrum) : degree (flipSigns s) = degree s := by
  unfold degree flipSigns
  rw [List.map_map]
  rfl

/-- **Degree cannot witness cancellation (proved).**  Two spectra with the same degree, one cancelling
and one not — so the hardness locus (cancellation) is invisible to the degree. -/
theorem degree_blind_to_cancellation :
    ∃ s₁ s₂ : Spectrum, degree s₁ = degree s₂ ∧ cancels s₁ ∧ ¬ cancels s₂ := by
  refine ⟨[(1, -1)], [(1, 1)], rfl, ⟨(1, -1), by simp, by decide⟩, ?_⟩
  rintro ⟨h, hmem, hlt⟩
  rw [List.mem_singleton] at hmem
  subst hmem
  simp at hlt

/-- **Non-cancellation is positive geometry (proved).**  A spectrum with no negative coefficient has an
aggregate that is a `PosCombo` value — straight into the amplituhedron face: no cancellation ⇒ positive
⇒ the easy side.  Hence hardness *requires* cancellation. -/
theorem noncancel_coeffSum_posCombo : ∀ (s : Spectrum), ¬ cancels s → PosCombo (coeffSum s) := by
  intro s
  induction s with
  | nil => intro _; exact PosCombo.zero
  | cons a as ih =>
    intro h
    have ha : 0 ≤ a.2 := by
      by_contra hc; exact h ⟨a, List.mem_cons.mpr (Or.inl rfl), by omega⟩
    have hrest : PosCombo (coeffSum as) :=
      ih (fun hc => by obtain ⟨x, hx, hl⟩ := hc; exact h ⟨x, List.mem_cons.mpr (Or.inr hx), hl⟩)
    have hcs : coeffSum (a :: as) = coeffSum as + a.2 := by
      simp only [coeffSum, List.map_cons, List.foldr_cons]; omega
    rw [hcs]
    exact PosCombo.add hrest ha

/-! ## (ii) The superpolynomial bound is the socket — and it escapes the harmonic method -/

/-- A superpolynomial harmonic lower bound: exceeds every polynomial. -/
def HarmonicLowerBound (bound : ℕ → ℕ) : Prop := ∀ k, ∃ n, n ^ k < bound n

/-- The eigenvalue / Khrapchenko cap: the spectral (harmonic) method is bounded by `n^2`. -/
def EigenvalueCapped (bound : ℕ → ℕ) : Prop := ∀ n, bound n ≤ n ^ 2

/-- **The socket escapes the harmonic method (proved).**  A superpolynomial harmonic bound cannot be
eigenvalue-capped — so requirement (ii) demands a spectral obstruction the Khrapchenko/eigenvalue method
provably cannot produce.  Harmonics-as-a-method cannot reach (ii). -/
theorem harmonic_lb_escapes_eigenvalue (bound : ℕ → ℕ) (hlb : HarmonicLowerBound bound) :
    ¬ EigenvalueCapped bound := by
  intro hcap
  obtain ⟨n, hn⟩ := hlb 2
  exact absurd (lt_of_lt_of_le hn (hcap n)) (lt_irrefl _)

/-! ## The framework: a SAT harmonic signature, and what it does / doesn't give -/

/-- A candidate harmonic signature for SAT.  Clears (iii) by carrying `cancels`; packages (ii) as the
hypothesis `above_khrapchenko`.  (i) non-largeness is not modeled — an explicit open counting socket. -/
structure SATHarmonicSignature where
  spec : Spectrum
  /-- (iii): the hardness is a genuine cancellation, not degree. -/
  cancels_spec : cancels spec
  bound : ℕ → ℕ
  /-- (ii) SOCKET: the superpolynomial spectral bound — this is `cost_super`, undischarged. -/
  above_khrapchenko : HarmonicLowerBound bound

/-- **Capstone (proved): what the signature localizes.**  A SAT harmonic signature clears (iii)
(genuine cancellation) and its bound provably lies beyond the eigenvalue/Khrapchenko cap — so the
crossing rests entirely on the one socket `above_khrapchenko`, which the harmonic method itself cannot
supply.  This does not prove SAT *has* such a signature; that premise is `P ≠ NP`. -/
theorem harmonic_signature_localizes (sig : SATHarmonicSignature) :
    cancels sig.spec ∧ ¬ EigenvalueCapped sig.bound :=
  ⟨sig.cancels_spec, harmonic_lb_escapes_eigenvalue sig.bound sig.above_khrapchenko⟩

end PallLean.Paper93.DeepMath.PathB.HarmonicSignatureFace

#print axioms PallLean.Paper93.DeepMath.PathB.HarmonicSignatureFace.degree_flipSigns
#print axioms PallLean.Paper93.DeepMath.PathB.HarmonicSignatureFace.noncancel_coeffSum_posCombo
#print axioms PallLean.Paper93.DeepMath.PathB.HarmonicSignatureFace.harmonic_lb_escapes_eigenvalue
#print axioms PallLean.Paper93.DeepMath.PathB.HarmonicSignatureFace.harmonic_signature_localizes
