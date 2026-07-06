import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityEval
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFramePartialRowBound

/-!
# N-Frame: the parity layout — `sat3X⊕` on raw bits

Rung 25 of the arc (… → parity eval → **parity layout**).  The concrete bit geometry of
`sat3X⊕`: blocks are `L`-bit segments on `Fin N` (one selector bit per codebook literal), the
decoded block family realizes the rung-24 semantic family, and rows/probes connect to the
engine's `mixOn` overlay language.

  `xbit` / `xbit_inj` — the position map `(block, selector) ↦ Fin N` and its injectivity.
  `decodeBlock` / `parityFamilyBits` — decoding raw bits to the semantic block family; **the
        concrete family** is the semantic parity of the decode.
  `decodeBlock_congr` / `parityFamilyBits_congr` — **PROVED, the realization**: the family
        depends on the input only through the block grid (junk/remainder bits are
        irrelevant), and equals the rung-24 semantics of its decode by definition.
  `mix_read_probe` / `mix_read_row` — the overlay reads: probe controls `Sᶜ`, row controls
        `S`, positionwise.
  `parity_detect_layout` / `parity_detect_layout_ne` — **PROVED, THE DETECTION TRANSFER**:
        two rows differing at ONE row-side selector position of the target block yield mixes
        whose decodes differ by inserting exactly that literal, so the rung-24 detection
        applies: the family value flips — for BOTH values of the added literal.

## Honest scope

The codebook `code : Fin L → Lit v` is a PARAMETER — the expander-affine instantiation
(singletons + Ramanujan edges + tautology, the kill-cost liveness) is later work, as are the
`hsol`/`heven` discharges (pins + scaffold under an adversarial balanced cut) and the band
assembly.  This rung freezes the geometry: raw bits realize the semantics, and one row-side
bit flip at the target block is exactly one literal insertion at the semantic level.  The
distinctness form is the shape `cut_row_capacity` (f-generic) consumes in the coming rungs.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityLayout

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

/-! ### The position map -/

theorem xbit_lt (hfit : m * L ≤ N) (c : Fin m) (i : Fin L) :
    c.val * L + i.val < N := by
  have hi := i.isLt
  have h1 : c.val * L + i.val < (c.val + 1) * L := by
    rw [Nat.succ_mul]
    omega
  have h2 : (c.val + 1) * L ≤ m * L :=
    Nat.mul_le_mul_right L (by have := c.isLt; omega)
  omega

/-- Selector bit `i` of block `c`. -/
def xbit (hfit : m * L ≤ N) (c : Fin m) (i : Fin L) : Fin N :=
  ⟨c.val * L + i.val, xbit_lt hfit c i⟩

theorem xbit_inj (hfit : m * L ≤ N) {c c' : Fin m} {i i' : Fin L}
    (h : xbit hfit c i = xbit hfit c' i') : c = c' ∧ i = i' := by
  have hval : c.val * L + i.val = c'.val * L + i'.val := congrArg Fin.val h
  have hcc : c.val = c'.val := by
    rcases Nat.lt_trichotomy c.val c'.val with hlt | heq | hgt
    · exfalso
      have h1 : (c.val + 1) * L ≤ c'.val * L := Nat.mul_le_mul_right L (by omega)
      rw [Nat.succ_mul] at h1
      have := i.isLt
      have := i'.isLt
      omega
    · exact heq
    · exfalso
      have h1 : (c'.val + 1) * L ≤ c.val * L := Nat.mul_le_mul_right L (by omega)
      rw [Nat.succ_mul] at h1
      have := i.isLt
      have := i'.isLt
      omega
  refine ⟨Fin.ext hcc, Fin.ext ?_⟩
  rw [hcc] at hval
  omega

/-! ### Decoding and the concrete family -/

/-- The decoded content of block `c`: the codebook image of its ON selector bits. -/
def decodeBlock (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (x : Fin N → Bool) (c : Fin m) : Finset (Lit v) :=
  (Finset.univ.filter (fun i : Fin L => x (xbit hfit c i) = true)).image code

/-- **THE CONCRETE FAMILY**: the semantic parity of the decoded block family. -/
def parityFamilyBits (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (x : Fin N → Bool) : Bool :=
  parityFamily (fun c => decodeBlock code hfit x c)

/-- **The realization (proved)**: decoding depends only on the block's own selector bits. -/
theorem decodeBlock_congr (code : Fin L → Lit v) (hfit : m * L ≤ N)
    {x y : Fin N → Bool} (c : Fin m)
    (h : ∀ i : Fin L, x (xbit hfit c i) = y (xbit hfit c i)) :
    decodeBlock code hfit x c = decodeBlock code hfit y c := by
  unfold decodeBlock
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h i]

/-- **The realization, family level (proved)**: the concrete family depends on the input
only through the block grid — remainder bits are irrelevant. -/
theorem parityFamilyBits_congr (code : Fin L → Lit v) (hfit : m * L ≤ N)
    {x y : Fin N → Bool}
    (h : ∀ (c : Fin m) (i : Fin L), x (xbit hfit c i) = y (xbit hfit c i)) :
    parityFamilyBits code hfit x = parityFamilyBits code hfit y := by
  unfold parityFamilyBits
  congr 1
  funext c
  exact decodeBlock_congr code hfit c (h c)

/-! ### Overlay reads -/

theorem mix_read_probe {S : Finset (Fin N)} (x y : Fin N → Bool) {p : Fin N}
    (hp : p ∈ Sᶜ) : mixOn Sᶜ x y p = x p := by
  show (if p ∈ Sᶜ then x p else y p) = x p
  exact if_pos hp

theorem mix_read_row {S : Finset (Fin N)} (x y : Fin N → Bool) {p : Fin N}
    (hp : p ∉ Sᶜ) : mixOn Sᶜ x y p = y p := by
  show (if p ∈ Sᶜ then x p else y p) = y p
  exact if_neg hp

/-! ### The detection transfer -/

set_option maxHeartbeats 1600000 in
/-- **THE DETECTION TRANSFER (proved)**: rows differing at one row-side selector position of
the target block yield mixes whose decodes differ by inserting exactly that literal; with the
rung-24 package on the decoded mix, the concrete family flips — for BOTH values `b`. -/
theorem parity_detect_layout (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (S : Finset (Fin N)) (x y y' : Fin N → Bool)
    (cstar : Fin m) (istar : Fin L)
    (w a₀ l : Fin v → ZMod 2) (b : ZMod 2)
    (hcode : code istar = (l, b))
    (hlw : dotp l w = 1)
    (hpos : xbit hfit cstar istar ∉ Sᶜ)
    (hy : y (xbit hfit cstar istar) = false)
    (hy' : y' (xbit hfit cstar istar) = true)
    (hagree : ∀ p : Fin N, p ≠ xbit hfit cstar istar → y p = y' p)
    (hsol : ∀ a : Fin v → ZMod 2,
      ((∀ c, c ≠ cstar → blockSat a (decodeBlock code hfit (mixOn Sᶜ x y) c))
        ∧ ∀ ℓ ∈ decodeBlock code hfit (mixOn Sᶜ x y) cstar, ¬ litHolds a ℓ)
      ↔ (a = a₀ ∨ a = a₀ + w))
    (heven : (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
        ∀ c, c ≠ cstar → blockSat a (decodeBlock code hfit (mixOn Sᶜ x y) c))).card
        % 2 = 0) :
    parityFamilyBits code hfit (mixOn Sᶜ x y) = false
    ∧ parityFamilyBits code hfit (mixOn Sᶜ x y') = true := by
  classical
  -- geometry: the primed decode inserts exactly the target literal at cstar
  have hBt : decodeBlock code hfit (mixOn Sᶜ x y') cstar
      = insert (l, b) (decodeBlock code hfit (mixOn Sᶜ x y) cstar) := by
    rw [← hcode]
    unfold decodeBlock
    rw [← Finset.image_insert]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hii : i = istar
    · subst hii
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        rw [mix_read_row x y' hpos]
        exact hy'
    · have hpne : xbit hfit cstar i ≠ xbit hfit cstar istar := by
        intro hc
        exact hii (xbit_inj hfit hc).2
      have hval : mixOn Sᶜ x y' (xbit hfit cstar i)
          = mixOn Sᶜ x y (xbit hfit cstar i) := by
        by_cases hmem : xbit hfit cstar i ∈ Sᶜ
        · rw [mix_read_probe x y' hmem, mix_read_probe x y hmem]
        · rw [mix_read_row x y' hmem, mix_read_row x y hmem]
          exact (hagree _ hpne).symm
      constructor
      · intro h
        refine Or.inr ?_
        rw [← hval]
        exact h
      · rintro (h | h)
        · exact absurd h hii
        · rw [hval]
          exact h
  have hBr : ∀ c, c ≠ cstar →
      decodeBlock code hfit (mixOn Sᶜ x y') c
        = decodeBlock code hfit (mixOn Sᶜ x y) c := by
    intro c hc
    apply decodeBlock_congr
    intro i
    have hpne : xbit hfit c i ≠ xbit hfit cstar istar := by
      intro hcon
      exact hc (xbit_inj hfit hcon).1
    by_cases hmem : xbit hfit c i ∈ Sᶜ
    · rw [mix_read_probe x y' hmem, mix_read_probe x y hmem]
    · rw [mix_read_row x y' hmem, mix_read_row x y hmem]
      exact (hagree _ hpne).symm
  have hdetect := parity_detect
    (fun c => decodeBlock code hfit (mixOn Sᶜ x y) c)
    (fun c => decodeBlock code hfit (mixOn Sᶜ x y') c)
    cstar w a₀ l b hlw hBt hBr hsol heven
  exact ⟨hdetect.1, hdetect.2⟩

/-- The detection transfer, distinctness form — the shape `cut_row_capacity` consumes. -/
theorem parity_detect_layout_ne (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (S : Finset (Fin N)) (x y y' : Fin N → Bool)
    (cstar : Fin m) (istar : Fin L)
    (w a₀ l : Fin v → ZMod 2) (b : ZMod 2)
    (hcode : code istar = (l, b))
    (hlw : dotp l w = 1)
    (hpos : xbit hfit cstar istar ∉ Sᶜ)
    (hy : y (xbit hfit cstar istar) = false)
    (hy' : y' (xbit hfit cstar istar) = true)
    (hagree : ∀ p : Fin N, p ≠ xbit hfit cstar istar → y p = y' p)
    (hsol : ∀ a : Fin v → ZMod 2,
      ((∀ c, c ≠ cstar → blockSat a (decodeBlock code hfit (mixOn Sᶜ x y) c))
        ∧ ∀ ℓ ∈ decodeBlock code hfit (mixOn Sᶜ x y) cstar, ¬ litHolds a ℓ)
      ↔ (a = a₀ ∨ a = a₀ + w))
    (heven : (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
        ∀ c, c ≠ cstar → blockSat a (decodeBlock code hfit (mixOn Sᶜ x y) c))).card
        % 2 = 0) :
    parityFamilyBits code hfit (mixOn Sᶜ x y)
      ≠ parityFamilyBits code hfit (mixOn Sᶜ x y') := by
  obtain ⟨h1, h2⟩ := parity_detect_layout code hfit S x y y' cstar istar
    w a₀ l b hcode hlw hpos hy hy' hagree hsol heven
  rw [h1, h2]
  exact Bool.false_ne_true

end PallLean.Paper93.DeepMath.PathB.NFrameParityLayout

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityLayout.xbit_inj
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityLayout.parityFamilyBits_congr
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityLayout.parity_detect_layout
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityLayout.parity_detect_layout_ne
