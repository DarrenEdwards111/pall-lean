import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEvalMachine

/-!
# Cook–Levin M1 — doubled-encoding infrastructure (detectable boundaries on a Boolean tape)

The single-machine `read a_v` weld failed on **termination/position detection**: a two-symbol tape has no marker
symbol, so shifts and loops can't tell where a region ends.  The standard fix, built here: **double** each data
bit (`b ↦ b b`), so a data pair is always `00` or `11` — the two cells are *equal*.  A **boundary marker** is a
*differing* pair `01`, which can never occur in doubled data.  So "is this cell a boundary?" becomes the local,
decidable test "do the two cells of this pair differ?", giving machines a detectable stopping point.

This file is the reusable infrastructure: `encodeD bs` = the doubled encoding of `bs` terminated by a `01` marker;
lemmas that data pairs read equal, the terminating marker reads `(false, true)`, and hence `firstMarkerD (encodeD
bs) = bs.length` — the boundary is exactly at the end of the data and is detectable.  Machines that use it (the
detectable-termination shift/loop) come next.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinDoubled

/-- The doubled encoding: each bit `b` becomes the equal pair `b b`; a terminating `01` marker ends it. -/
def encodeD : List Bool → List Bool
  | [] => [false, true]
  | b :: bs => b :: b :: encodeD bs

theorem encodeD_length (bs : List Bool) : (encodeD bs).length = 2 * bs.length + 2 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show (b :: b :: encodeD bs).length = 2 * (bs.length + 1) + 2
    rw [List.length_cons, List.length_cons, ih]; ring

/-- The low cell of data pair `i` reads `bs[i]`. -/
theorem encodeD_lo (bs : List Bool) (i : ℕ) (h : i < bs.length) :
    (encodeD bs).getD (2 * i) false = bs.getD i false := by
  induction bs generalizing i with
  | nil => exact absurd h (by simp)
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < bs.length := by simpa using h
      show (b :: b :: encodeD bs).getD (2 * (i + 1)) false = (b :: bs).getD (i + 1) false
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by ring]
      simp only [List.getD_cons_succ]
      exact ih i h'

/-- The high cell of data pair `i` also reads `bs[i]` — so a data pair's cells are equal. -/
theorem encodeD_hi (bs : List Bool) (i : ℕ) (h : i < bs.length) :
    (encodeD bs).getD (2 * i + 1) false = bs.getD i false := by
  induction bs generalizing i with
  | nil => exact absurd h (by simp)
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < bs.length := by simpa using h
      show (b :: b :: encodeD bs).getD (2 * (i + 1) + 1) false = (b :: bs).getD (i + 1) false
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 from by ring]
      simp only [List.getD_cons_succ]
      exact ih i h'

/-- The low cell of the terminating marker reads `false`. -/
theorem encodeD_mark_lo (bs : List Bool) : (encodeD bs).getD (2 * bs.length) false = false := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show (b :: b :: encodeD bs).getD (2 * (bs.length + 1)) false = false
    rw [show 2 * (bs.length + 1) = 2 * bs.length + 1 + 1 from by ring]
    simp only [List.getD_cons_succ]
    exact ih

/-- The high cell of the terminating marker reads `true` — so the marker pair's cells differ. -/
theorem encodeD_mark_hi (bs : List Bool) : (encodeD bs).getD (2 * bs.length + 1) false = true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show (b :: b :: encodeD bs).getD (2 * (bs.length + 1) + 1) false = true
    rw [show 2 * (bs.length + 1) + 1 = 2 * bs.length + 1 + 1 + 1 from by ring]
    simp only [List.getD_cons_succ]
    exact ih

/-- **Data pairs read equal** (the "not a marker" test). -/
theorem encodeD_data_eq (bs : List Bool) (i : ℕ) (h : i < bs.length) :
    (encodeD bs).getD (2 * i) false = (encodeD bs).getD (2 * i + 1) false := by
  rw [encodeD_lo bs i h, encodeD_hi bs i h]

/-- **The terminating pair is a marker** (its cells differ). -/
theorem encodeD_marker (bs : List Bool) :
    (encodeD bs).getD (2 * bs.length) false ≠ (encodeD bs).getD (2 * bs.length + 1) false := by
  rw [encodeD_mark_lo, encodeD_mark_hi]; simp

/-- A marker pair exists in an encoding (the terminator). -/
theorem markerD_exists (bs : List Bool) :
    ∃ j, (encodeD bs).getD (2 * j) false ≠ (encodeD bs).getD (2 * j + 1) false :=
  ⟨bs.length, encodeD_marker bs⟩

/-- The first marker pair index in an encoding. -/
def firstMarkerD (bs : List Bool) : ℕ := Nat.find (markerD_exists bs)

/-- **The detectable boundary is exactly at the end of the data.**  Scanning pairs while cells are equal stops at
pair `bs.length` — the terminating marker. -/
theorem firstMarkerD_eq (bs : List Bool) : firstMarkerD bs = bs.length := by
  rw [firstMarkerD, Nat.find_eq_iff]
  refine ⟨encodeD_marker bs, ?_⟩
  intro i hi
  exact fun hne => hne (encodeD_data_eq bs i hi)

end PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
