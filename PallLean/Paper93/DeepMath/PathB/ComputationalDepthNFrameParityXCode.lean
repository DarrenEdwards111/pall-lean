import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityRouteAssembly

/-!
# N-Frame: the extended codebook — circulant edge columns

Expander-discharge arc, rung E3a (… → route assembly → **extended codebook**).  The
concrete codebook of the circulant route design, `xstdL v dd = 2v + 2·dd·v + 1` indices
per block (`dd` = half-degree, so degree `d = 2·dd`):

    index 0                                   — the tautology;
    index 1 + 2j + b                          — the singleton literal (e_j, b);
    index 1 + 2v + (j·2dd + 2s + b)           — the edge literal (e_j + e_{j+s+1 mod v}, b),

each undirected circulant edge `{j, j ± (s+1)}` enumerated once at its lower endpoint,
both values.  The route layer maps a pinned coordinate to its selector index and its
literal: `direct` uses the singleton column, `edgeLo`/`edgeHi` use the edge column whose
other endpoint is the scaffold-covered companion (`+ (s+1)` resp. `− (s+1)` around the
circulant).

  `xstdCode_taut` / `xstdCode_sIdxX` / `xstdCode_eIdx` — **PROVED**: the enumeration reads.
  `sIdxX_ne_taut` / `eIdx_ne_taut` / `sIdxX_ne_eIdx` / `sIdxX_inj` / `eIdx_inj` —
        **PROVED**: the index discipline (class disjointness + within-class injectivity).
  `PinRoute` / `routeIdx` / `routeLit` / `routeCompanion` — the route layer.
  `xstdCode_routeIdx` — **PROVED, THE ROUTE READ**: every route's selector index decodes
        to its route literal — the single lemma the drag glue consumes per pin.

## Honest scope

Per the ratified framing this is the CRITICAL-PATH codebook: explicit circulant,
elementary counting, no spectral input; Ramanujan remains the flagship upgrade.  The drag
re-glue over this codebook is E3b; the graph layer (companion-compatible independent
sets) is E4; the kill-accounting at real cuts is E5.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityXCode

open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook

/-- The extended codebook length: tautology + two value-columns per coordinate + two
value-columns per circulant edge slot (`dd` slots per coordinate, degree `2·dd`). -/
def xstdL (v dd : ℕ) : ℕ := 2 * v + 2 * dd * v + 1

/-- The tautology index. -/
def tautIdxX (v dd : ℕ) : Fin (xstdL v dd) := ⟨0, by unfold xstdL; omega⟩

theorem sIdxX_lt (v dd : ℕ) (j : Fin v) (b : ZMod 2) :
    1 + 2 * j.val + b.val < xstdL v dd := by
  have hj := j.isLt
  have hb : b.val < 2 := ZMod.val_lt b
  unfold xstdL
  omega

/-- The index of the singleton literal `(e_j, b)`. -/
def sIdxX (v dd : ℕ) (j : Fin v) (b : ZMod 2) : Fin (xstdL v dd) :=
  ⟨1 + 2 * j.val + b.val, sIdxX_lt v dd j b⟩

theorem eIdx_lt (v dd : ℕ) (j : Fin v) (s : Fin dd) (b : ZMod 2) :
    1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) < xstdL v dd := by
  have hj : j.val + 1 ≤ v := j.isLt
  have hs : s.val + 1 ≤ dd := s.isLt
  have hb : b.val < 2 := ZMod.val_lt b
  have h3 : (j.val + 1) * (2 * dd) ≤ v * (2 * dd) :=
    Nat.mul_le_mul_right _ hj
  have h4 : (j.val + 1) * (2 * dd) = j.val * (2 * dd) + 2 * dd := by ring
  have h5 : v * (2 * dd) = 2 * dd * v := by ring
  unfold xstdL
  omega

/-- The index of the edge literal at lower endpoint `j`, slot `s` (companion
`j + s + 1 mod v`), value `b`. -/
def eIdx (v dd : ℕ) (j : Fin v) (s : Fin dd) (b : ZMod 2) : Fin (xstdL v dd) :=
  ⟨1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val), eIdx_lt v dd j s b⟩

/-- Circulant rotation. -/
def rot (v : ℕ) (hv : 0 < v) (j : Fin v) (k : ℕ) : Fin v :=
  ⟨(j.val + k) % v, Nat.mod_lt _ hv⟩

theorem rot_rot_cancel (v : ℕ) (hv : 0 < v) (j : Fin v) (k : ℕ) (hk : k ≤ v) :
    rot v hv (rot v hv j (v - k)) k = j := by
  apply Fin.ext
  show ((j.val + (v - k)) % v + k) % v = j.val
  rw [Nat.mod_add_mod]
  have h1 : j.val + (v - k) + k = j.val + v := by omega
  rw [h1, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt j.isLt

/-! ### The Euclidean decode helpers -/

theorem edq (dd jv r : ℕ) (hr : r < 2 * dd) :
    (jv * (2 * dd) + r) / (2 * dd) = jv := by
  rw [mul_comm jv (2 * dd), Nat.mul_add_div (by omega : 0 < 2 * dd)]
  rw [Nat.div_eq_of_lt hr, add_zero]

theorem emq (dd jv r : ℕ) (hr : r < 2 * dd) :
    (jv * (2 * dd) + r) % (2 * dd) = r := by
  rw [mul_comm jv (2 * dd), Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hr

/-! ### The codebook -/

theorem xstd_sdiv_lt (v dd : ℕ) (i : Fin (xstdL v dd))
    (h0 : ¬ i.val = 0) (h1 : i.val < 1 + 2 * v) : (i.val - 1) / 2 < v := by
  omega

/-- The extended codebook. -/
def xstdCode (v dd : ℕ) (hv : 0 < v) : Fin (xstdL v dd) → Lit v := fun i =>
  if h0 : i.val = 0 then tautLit v
  else if h1 : i.val < 1 + 2 * v then
    (single v ⟨(i.val - 1) / 2, xstd_sdiv_lt v dd i h0 h1⟩,
      (((i.val - 1) % 2 : ℕ) : ZMod 2))
  else
    (single v ⟨(i.val - (1 + 2 * v)) / (2 * dd) % v, Nat.mod_lt _ hv⟩
      + single v (rot v hv
          ⟨(i.val - (1 + 2 * v)) / (2 * dd) % v, Nat.mod_lt _ hv⟩
          ((i.val - (1 + 2 * v)) % (2 * dd) / 2 + 1)),
      (((i.val - (1 + 2 * v)) % 2 : ℕ) : ZMod 2))

/-- **The tautology read (proved)**. -/
theorem xstdCode_taut (v dd : ℕ) (hv : 0 < v) :
    xstdCode v dd hv (tautIdxX v dd) = tautLit v := by
  unfold xstdCode tautIdxX
  rw [dif_pos rfl]

/-- **The singleton read (proved)**: index `1 + 2j + b` codes `(e_j, b)`. -/
theorem xstdCode_sIdxX (v dd : ℕ) (hv : 0 < v) (j : Fin v) (b : ZMod 2) :
    xstdCode v dd hv (sIdxX v dd j b) = (single v j, b) := by
  have hbv : b.val < 2 := ZMod.val_lt b
  have hj := j.isLt
  unfold xstdCode sIdxX
  rw [dif_neg (by omega : ¬ (1 + 2 * j.val + b.val = 0)),
    dif_pos (by omega : 1 + 2 * j.val + b.val < 1 + 2 * v)]
  have h1 : (1 + 2 * j.val + b.val - 1) / 2 = j.val := by omega
  have h2 : (1 + 2 * j.val + b.val - 1) % 2 = b.val := by omega
  have hcast : ∀ x : ZMod 2, ((x.val : ℕ) : ZMod 2) = x := by decide
  congr 1
  · congr 1
    exact Fin.ext h1
  · rw [h2]
    exact hcast b

set_option maxHeartbeats 800000 in
/-- **The edge read (proved)**: the edge index at lower endpoint `j`, slot `s`, value `b`
codes `(e_j + e_{j+s+1 mod v}, b)`. -/
theorem xstdCode_eIdx (v dd : ℕ) (hv : 0 < v) (j : Fin v) (s : Fin dd) (b : ZMod 2) :
    xstdCode v dd hv (eIdx v dd j s b)
      = (single v j + single v (rot v hv j (s.val + 1)), b) := by
  have hbv : b.val < 2 := ZMod.val_lt b
  have hj := j.isLt
  have hs := s.isLt
  unfold xstdCode eIdx
  rw [dif_neg (by omega :
      ¬ (1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) = 0)),
    dif_neg (by omega :
      ¬ (1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) < 1 + 2 * v))]
  have he : 1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) - (1 + 2 * v)
      = j.val * (2 * dd) + 2 * s.val + b.val := by omega
  have hassoc : j.val * (2 * dd) + 2 * s.val + b.val
      = j.val * (2 * dd) + (2 * s.val + b.val) := by omega
  have hr : 2 * s.val + b.val < 2 * dd := by omega
  have hjd : (1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) - (1 + 2 * v))
      / (2 * dd) % v = j.val := by
    rw [he, hassoc, edq dd j.val (2 * s.val + b.val) hr]
    exact Nat.mod_eq_of_lt hj
  have hsd : (1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) - (1 + 2 * v))
      % (2 * dd) / 2 = s.val := by
    rw [he, hassoc, emq dd j.val (2 * s.val + b.val) hr]
    omega
  have hbd : (1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) - (1 + 2 * v))
      % 2 = b.val := by
    rw [he]
    have h2d : j.val * (2 * dd) = 2 * (j.val * dd) := by ring
    omega
  have hcast : ∀ x : ZMod 2, ((x.val : ℕ) : ZMod 2) = x := by decide
  congr 1
  · congr 1
    · congr 1
      exact Fin.ext hjd
    · congr 1
      apply Fin.ext
      show ((1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) - (1 + 2 * v))
            / (2 * dd) % v
          + ((1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) - (1 + 2 * v))
            % (2 * dd) / 2 + 1)) % v
        = (j.val + (s.val + 1)) % v
      rw [hjd, hsd]
  · rw [hbd]
    exact hcast b

/-! ### The index discipline -/

/-- **Singleton indices avoid the tautology (proved)**. -/
theorem sIdxX_ne_taut (v dd : ℕ) (j : Fin v) (b : ZMod 2) :
    sIdxX v dd j b ≠ tautIdxX v dd := by
  intro h
  have h' : 1 + 2 * j.val + b.val = 0 := congrArg Fin.val h
  omega

/-- **Edge indices avoid the tautology (proved)**. -/
theorem eIdx_ne_taut (v dd : ℕ) (j : Fin v) (s : Fin dd) (b : ZMod 2) :
    eIdx v dd j s b ≠ tautIdxX v dd := by
  intro h
  have h' : 1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val) = 0 :=
    congrArg Fin.val h
  omega

/-- **The class disjointness (proved)**: singleton and edge index ranges are disjoint. -/
theorem sIdxX_ne_eIdx (v dd : ℕ) (j j' : Fin v) (s : Fin dd) (b b' : ZMod 2) :
    sIdxX v dd j b ≠ eIdx v dd j' s b' := by
  intro h
  have hj := j.isLt
  have hb : b.val < 2 := ZMod.val_lt b
  have h' : 1 + 2 * j.val + b.val
      = 1 + 2 * v + (j'.val * (2 * dd) + 2 * s.val + b'.val) :=
    congrArg Fin.val h
  omega

/-- **The singleton injectivity (proved)**. -/
theorem sIdxX_inj (v dd : ℕ) {j j' : Fin v} {b b' : ZMod 2}
    (h : sIdxX v dd j b = sIdxX v dd j' b') : j = j' ∧ b = b' := by
  have hval : 1 + 2 * j.val + b.val = 1 + 2 * j'.val + b'.val :=
    congrArg Fin.val h
  have hb : b.val < 2 := ZMod.val_lt b
  have hb' : b'.val < 2 := ZMod.val_lt b'
  have hj : j.val = j'.val := by omega
  have hbv : b.val = b'.val := by omega
  have hcast : ∀ x y : ZMod 2, x.val = y.val → x = y := by decide
  exact ⟨Fin.ext hj, hcast b b' hbv⟩

/-- **The edge injectivity (proved)**: the edge index determines endpoint, slot, and
value. -/
theorem eIdx_inj (v dd : ℕ) {j j' : Fin v} {s s' : Fin dd} {b b' : ZMod 2}
    (h : eIdx v dd j s b = eIdx v dd j' s' b') : j = j' ∧ s = s' ∧ b = b' := by
  have hval : 1 + 2 * v + (j.val * (2 * dd) + 2 * s.val + b.val)
      = 1 + 2 * v + (j'.val * (2 * dd) + 2 * s'.val + b'.val) :=
    congrArg Fin.val h
  have hb : b.val < 2 := ZMod.val_lt b
  have hb' : b'.val < 2 := ZMod.val_lt b'
  have hs := s.isLt
  have hs' := s'.isLt
  have he : j.val * (2 * dd) + (2 * s.val + b.val)
      = j'.val * (2 * dd) + (2 * s'.val + b'.val) := by omega
  have hr : 2 * s.val + b.val < 2 * dd := by omega
  have hr' : 2 * s'.val + b'.val < 2 * dd := by omega
  have hjj : j.val = j'.val := by
    have d1 := edq dd j.val (2 * s.val + b.val) hr
    have d2 := edq dd j'.val (2 * s'.val + b'.val) hr'
    rw [← d1, ← d2, he]
  have hres : 2 * s.val + b.val = 2 * s'.val + b'.val := by
    have m1 := emq dd j.val (2 * s.val + b.val) hr
    have m2 := emq dd j'.val (2 * s'.val + b'.val) hr'
    rw [← m1, ← m2, he]
  have hcast : ∀ x y : ZMod 2, x.val = y.val → x = y := by decide
  exact ⟨Fin.ext hjj, Fin.ext (by omega), hcast b b' (by omega)⟩

/-! ### The route layer -/

/-- A pin route: direct singleton, or the circulant edge whose companion sits `s+1` above
(`edgeLo`) or below (`edgeHi`) the pinned coordinate. -/
inductive PinRoute (dd : ℕ) where
  | direct : PinRoute dd
  | edgeLo (s : Fin dd) : PinRoute dd
  | edgeHi (s : Fin dd) : PinRoute dd

/-- The route's scaffold-covered companion (none for direct routes). -/
def routeCompanion (v : ℕ) {dd : ℕ} (hv : 0 < v) (κc : Fin v) :
    PinRoute dd → Option (Fin v)
  | .direct => none
  | .edgeLo s => some (rot v hv κc (s.val + 1))
  | .edgeHi s => some (rot v hv κc (v - (s.val + 1)))

/-- The route's selector index: the singleton column, or the edge column at the lower
endpoint of the circulant edge. -/
def routeIdx (v dd : ℕ) (hv : 0 < v) (κc : Fin v) (b : ZMod 2) :
    PinRoute dd → Fin (xstdL v dd)
  | .direct => sIdxX v dd κc b
  | .edgeLo s => eIdx v dd κc s b
  | .edgeHi s => eIdx v dd (rot v hv κc (v - (s.val + 1))) s b

/-- The route's literal: the direct complement singleton, or the edge literal with the
scaffold-covered companion. -/
def routeLit (v : ℕ) {dd : ℕ} (hv : 0 < v) (κc : Fin v) (b : ZMod 2)
    (ρ : PinRoute dd) : Lit v :=
  match routeCompanion v hv κc ρ with
  | none => (single v κc, b)
  | some j'' => (single v κc + single v j'', b)

set_option maxHeartbeats 800000 in
/-- **THE ROUTE READ (proved)**: every route's selector index decodes to its route
literal — the single lemma the drag glue consumes per pin. -/
theorem xstdCode_routeIdx (v dd : ℕ) (hv : 0 < v) (hddv : dd ≤ v)
    (κc : Fin v) (b : ZMod 2) (ρ : PinRoute dd) :
    xstdCode v dd hv (routeIdx v dd hv κc b ρ) = routeLit v hv κc b ρ := by
  cases ρ with
  | direct =>
      show xstdCode v dd hv (sIdxX v dd κc b) = (single v κc, b)
      exact xstdCode_sIdxX v dd hv κc b
  | edgeLo s =>
      show xstdCode v dd hv (eIdx v dd κc s b)
        = (single v κc + single v (rot v hv κc (s.val + 1)), b)
      exact xstdCode_eIdx v dd hv κc s b
  | edgeHi s =>
      show xstdCode v dd hv (eIdx v dd (rot v hv κc (v - (s.val + 1))) s b)
        = (single v κc + single v (rot v hv κc (v - (s.val + 1))), b)
      rw [xstdCode_eIdx]
      rw [rot_rot_cancel v hv κc (s.val + 1) (by
        have := s.isLt
        omega)]
      congr 1
      exact add_comm _ _

end PallLean.Paper93.DeepMath.PathB.NFrameParityXCode

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXCode.xstdCode_taut
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXCode.xstdCode_sIdxX
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXCode.xstdCode_eIdx
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXCode.sIdxX_ne_taut
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXCode.eIdx_ne_taut
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXCode.sIdxX_ne_eIdx
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXCode.sIdxX_inj
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXCode.eIdx_inj
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXCode.xstdCode_routeIdx
