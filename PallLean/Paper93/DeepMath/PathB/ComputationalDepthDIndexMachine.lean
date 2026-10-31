import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLangRankKill

/-!
# The doubled-INDEX machine — discharging `DIndexInP`

The two-pointer marking machine deciding `dIndexLang` — M1's "remaining mountain" (data-
dependent lookup via the classic marking construction), built in the morph-arc fabric.

**Control (15 states × answer bit).**  Rounds, each a single rightward pass + reset:
the flagged data-walk `A0f/A1f/A2f` skips marked units `[T,F,d]` and *marks* the first
live unit `[T,T,d]` (write `F` at its middle cell, continuing unflagged `A0/A1/A2`);
crossing `A3/A4` passes the 3-cell terminator; the address walk `B0/B1` skips consumed
units `[T,F]` and *consumes* the first live unit `[T,T]` (write + reset, re-entering the
flagged walk).  When the address block exhausts (`B0` reads `F`), the answer phase
`D0/D1/D2/D3` finds the first unmarked data unit and halts with its payload (`false` at
the terminator/void).  Marks lag consumes by one round, so on exit exactly
`liveCount (postData w)` data units are marked and the first unmarked payload *is*
`dIndexLang w` — on **all** inputs, including garbage (the spec's marked-unit skipping is
exactly the machine's own consumption discipline).

**Proof architecture.**  Clocks are *existential* (`∃ t ≤ bound`): the machine halts, so
`run_stable` lifts any halting time to the polynomial clock — no exact-clock telescoping.
Walk lemmas are inductions over unit lists (`flatU`/`flat2` flattenings); the grand round
induction is on the number of live address units, which each round strictly decreases.
The language-side bookkeeping (`unitsOf`/`dataSuf` decompositions, `markFirst` surgery,
`ansOf` iteration) reduces the machine's answer to `dIndexLang` by pure recursion lemmas.

**Payoff**: `dIndexInP : DIndexInP` — the fence is *discharged* — and
`langRank_kill_unconditional`: every language-level measure dominating subfunction counts
fails `LangGenSound`, with no hypotheses left.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DIndexMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.LangRankKill
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## The machine -/

/-- States: `0`/`1`/`2` unflagged data walk, `3`/`4`/`5` flagged data walk (mark pending),
`6`/`7` terminator crossing, `8`/`9` address walk, `10`–`13` answer phase, `14` halt. -/
def dIndexM : Machine where
  State := Fin 15 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 14)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2), none, 1) else ((6, s.2), none, 1))
    else if s.1 = 1 then ((2, s.2), none, 1)
    else if s.1 = 2 then ((0, s.2), none, 1)
    else if s.1 = 3 then (if b then ((4, s.2), none, 1) else ((6, s.2), none, 1))
    else if s.1 = 4 then (if b then ((2, s.2), some false, 1) else ((5, s.2), none, 1))
    else if s.1 = 5 then ((3, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), none, 1)
    else if s.1 = 7 then ((8, s.2), none, 1)
    else if s.1 = 8 then (if b then ((9, s.2), none, 1) else ((10, s.2), none, 3))
    else if s.1 = 9 then (if b then ((3, s.2), some false, 3) else ((8, s.2), none, 1))
    else if s.1 = 10 then (if b then ((11, s.2), none, 1) else ((14, false), none, 2))
    else if s.1 = 11 then (if b then ((12, s.2), none, 1) else ((13, s.2), none, 1))
    else if s.1 = 12 then ((14, b), none, 2)
    else if s.1 = 13 then ((10, s.2), none, 1)
    else ((14, s.2), none, 2)
  accept := fun s => s.2

/-! ## Unit-structure recursions -/

/-- Flatten data units `(mark?, payload)` to 3-cell blocks. -/
def flatU : List (Bool × Bool) → List Bool
  | [] => []
  | (m, d) :: us => true :: m :: d :: flatU us

/-- Parse the maximal 3-cell data-unit prefix. -/
def unitsOf : List Bool → List (Bool × Bool)
  | true :: m :: d :: r => (m, d) :: unitsOf r
  | _ => []

/-- What follows the data-unit prefix. -/
def dataSuf : List Bool → List Bool
  | true :: _ :: _ :: r => dataSuf r
  | rest => rest

/-- Flatten address units to 2-cell blocks. -/
def flat2 : List Bool → List Bool
  | [] => []
  | a :: as => true :: a :: flat2 as

/-- Parse the maximal 2-cell address-unit prefix. -/
def unitsOf2 : List Bool → List Bool
  | true :: a :: r => a :: unitsOf2 r
  | _ => []

/-- What follows the address-unit prefix. -/
def addrSuf : List Bool → List Bool
  | true :: _ :: r => addrSuf r
  | rest => rest

/-- Mark the first live data unit. -/
def markFirst : List (Bool × Bool) → List (Bool × Bool)
  | (true, d) :: us => (false, d) :: us
  | (false, d) :: us => (false, d) :: markFirst us
  | [] => []

/-- The answer walk: payload of the first live unit, `false` if none. -/
def ansOf : List (Bool × Bool) → Bool
  | (true, d) :: _ => d
  | (false, _) :: us => ansOf us
  | [] => false

/-- Live payloads of a unit list. -/
def liveDataU : List (Bool × Bool) → List Bool
  | (true, d) :: us => d :: liveDataU us
  | (false, _) :: us => liveDataU us
  | [] => []

/-! ## Structure lemmas -/

theorem flatU_length (us : List (Bool × Bool)) : (flatU us).length = 3 * us.length := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    obtain ⟨m, d⟩ := u
    show (true :: m :: d :: flatU us).length = 3 * (us.length + 1)
    simp only [List.length_cons, ih]
    omega

theorem flat2_length (as : List Bool) : (flat2 as).length = 2 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    show (true :: a :: flat2 as).length = 2 * (as.length + 1)
    simp only [List.length_cons, ih]
    omega

theorem flat2_append (as bs : List Bool) : flat2 (as ++ bs) = flat2 as ++ flat2 bs := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    show true :: a :: flat2 (as ++ bs) = true :: a :: (flat2 as ++ flat2 bs)
    rw [ih]

theorem markFirst_length : ∀ us : List (Bool × Bool), (markFirst us).length = us.length
  | [] => rfl
  | (true, _) :: _ => rfl
  | (false, d) :: us => by
    show ((false, d) :: markFirst us).length = ((false, d) :: us).length
    simp [markFirst_length us]

theorem decompU : ∀ w : List Bool, flatU (unitsOf w) ++ dataSuf w = w
  | [] => rfl
  | [true] => rfl
  | [true, _] => rfl
  | false :: _ => rfl
  | true :: m :: d :: r => by
    show true :: m :: d :: (flatU (unitsOf r) ++ dataSuf r) = true :: m :: d :: r
    rw [decompU r]

theorem dataSuf_shape : ∀ w : List Bool,
    dataSuf w = [] ∨ dataSuf w = [true] ∨ (∃ x, dataSuf w = [true, x]) ∨
      ∃ r, dataSuf w = false :: r
  | [] => Or.inl rfl
  | [true] => Or.inr (Or.inl rfl)
  | [true, x] => Or.inr (Or.inr (Or.inl ⟨x, rfl⟩))
  | false :: r => Or.inr (Or.inr (Or.inr ⟨r, rfl⟩))
  | true :: _ :: _ :: r => dataSuf_shape r

theorem decomp2 : ∀ a : List Bool, flat2 (unitsOf2 a) ++ addrSuf a = a
  | [] => rfl
  | [true] => rfl
  | false :: _ => rfl
  | true :: x :: r => by
    show true :: x :: (flat2 (unitsOf2 r) ++ addrSuf r) = true :: x :: r
    rw [decomp2 r]

theorem addrSuf_shape : ∀ a : List Bool,
    addrSuf a = [] ∨ addrSuf a = [true] ∨ ∃ r, addrSuf a = false :: r
  | [] => Or.inl rfl
  | [true] => Or.inr (Or.inl rfl)
  | false :: r => Or.inr (Or.inr ⟨r, rfl⟩)
  | true :: _ :: r => addrSuf_shape r

theorem postData_flatU (us : List (Bool × Bool)) : ∀ suf : List Bool,
    (suf = [] ∨ suf = [true] ∨ (∃ x, suf = [true, x]) ∨ ∃ r, suf = false :: r) →
    postData (flatU us ++ suf) = suf.drop 3 := by
  induction us with
  | nil =>
    intro suf hsuf
    rcases hsuf with rfl | rfl | ⟨x, rfl⟩ | ⟨r, rfl⟩ <;> rfl
  | cons u us ih =>
    intro suf hsuf
    obtain ⟨m, d⟩ := u
    show postData (true :: m :: d :: (flatU us ++ suf)) = suf.drop 3
    exact ih suf hsuf

theorem liveData_eq : ∀ w : List Bool, liveData w = liveDataU (unitsOf w)
  | [] => rfl
  | [true] => rfl
  | [true, _] => rfl
  | false :: _ => rfl
  | true :: m :: d :: r => by
    cases m
    · show liveData (true :: false :: d :: r) = liveDataU ((false, d) :: unitsOf r)
      rw [show liveData (true :: false :: d :: r) = liveData r from rfl]
      exact liveData_eq r
    · show liveData (true :: true :: d :: r) = liveDataU ((true, d) :: unitsOf r)
      rw [show liveData (true :: true :: d :: r) = d :: liveData r from rfl]
      show d :: liveData r = d :: liveDataU (unitsOf r)
      rw [liveData_eq r]

theorem liveCount_eq : ∀ a : List Bool, liveCount a = (unitsOf2 a).count true
  | [] => rfl
  | [true] => rfl
  | false :: _ => rfl
  | true :: true :: r => by
    show 1 + liveCount r = (true :: unitsOf2 r).count true
    rw [liveCount_eq r, List.count_cons_self]
    omega
  | true :: false :: r => by
    show 0 + liveCount r = (false :: unitsOf2 r).count true
    rw [liveCount_eq r, List.count_cons_of_ne (by decide)]
    omega

theorem ansOf_getD : ∀ us : List (Bool × Bool), ansOf us = (liveDataU us).getD 0 false
  | [] => rfl
  | (true, _) :: _ => rfl
  | (false, _) :: us => ansOf_getD us

theorem liveDataU_markFirst : ∀ us : List (Bool × Bool),
    liveDataU (markFirst us) = (liveDataU us).drop 1
  | [] => rfl
  | (true, _) :: _ => rfl
  | (false, d) :: us => by
    show liveDataU ((false, d) :: markFirst us) = (liveDataU ((false, d) :: us)).drop 1
    rw [show liveDataU ((false, d) :: markFirst us) = liveDataU (markFirst us) from rfl]
    exact liveDataU_markFirst us

theorem ansOf_iter (j : ℕ) : ∀ us : List (Bool × Bool),
    ansOf (markFirst^[j] us) = (liveDataU us).getD j false := by
  induction j with
  | zero => intro us; exact ansOf_getD us
  | succ j ih =>
    intro us
    rw [Function.iterate_succ_apply, ih (markFirst us), liveDataU_markFirst]
    cases h : liveDataU us with
    | nil => simp
    | cons a l => simp

theorem exists_first_true : ∀ as : List Bool, 0 < as.count true →
    ∃ fs rest, as = fs ++ true :: rest ∧ (∀ b ∈ fs, b = false)
  | [], h => by simp at h
  | true :: as, _ => ⟨[], as, rfl, by simp⟩
  | false :: as, h => by
    have h' : 0 < as.count true := by simpa [List.count_cons] using h
    obtain ⟨fs, rest, rfl, hfs⟩ := exists_first_true as h'
    exact ⟨false :: fs, rest, rfl, by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rfl
      · exact hfs b hb⟩

theorem all_false_of_count_zero {as : List Bool} (h : as.count true = 0) :
    ∀ b ∈ as, b = false := by
  intro b hb
  cases b
  · rfl
  · exact absurd (List.count_eq_zero.mp h) (fun hn => hn hb)

/-! ## Read/write helpers -/

theorem getD_at (P : List Bool) (y : Bool) (Z : List Bool) :
    (P ++ y :: Z).getD P.length false = y := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem getD_beyond (x : List Bool) (p : ℕ) (h : x.length ≤ p) :
    x.getD p false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem writeAt_boundary (P : List Bool) (b w : Bool) (R : List Bool) :
    writeAt (P ++ b :: R) P.length w = P ++ w :: R := by
  unfold writeAt
  have h0 : P.length + 1 - (P ++ b :: R).length = 0 := by
    simp
  rw [h0]
  show ((P ++ b :: R) ++ []).set P.length w = P ++ w :: R
  rw [List.append_nil, List.set_append_right _ _ (Nat.le_refl _)]
  simp

/-! ## Run helpers -/

theorem run_one (M : Machine) (c : Cfg M) : run M 1 c = step M c := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero]

theorem run_two (M : Machine) (c : Cfg M) : run M 2 c = step M (step M c) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ, run_one]

theorem run_three (M : Machine) (c : Cfg M) : run M 3 c = step M (step M (step M c)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, run_succ, run_two]

theorem run_four (M : Machine) (c : Cfg M) :
    run M 4 c = step M (step M (step M (step M c))) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, run_succ, run_three]

/-! ## Step lemmas -/

theorem step_A0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dIndexM ⟨(0, ans), p, x⟩ = ⟨(1, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_A0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dIndexM ⟨(0, ans), p, x⟩ = ⟨(6, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_A1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step dIndexM ⟨(1, ans), p, x⟩ = ⟨(2, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, moveHead]; rfl

theorem step_A2 {ans : Bool} {p : ℕ} {x : List Bool} :
    step dIndexM ⟨(2, ans), p, x⟩ = ⟨(0, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, moveHead]; rfl

theorem step_A0f_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dIndexM ⟨(3, ans), p, x⟩ = ⟨(4, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_A0f_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dIndexM ⟨(3, ans), p, x⟩ = ⟨(6, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_A1f_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dIndexM ⟨(4, ans), p, x⟩ = ⟨(2, ans), p + 1, writeAt x p false⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_A1f_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dIndexM ⟨(4, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_A2f {ans : Bool} {p : ℕ} {x : List Bool} :
    step dIndexM ⟨(5, ans), p, x⟩ = ⟨(3, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, moveHead]; rfl

theorem step_A3 {ans : Bool} {p : ℕ} {x : List Bool} :
    step dIndexM ⟨(6, ans), p, x⟩ = ⟨(7, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, moveHead]; rfl

theorem step_A4 {ans : Bool} {p : ℕ} {x : List Bool} :
    step dIndexM ⟨(7, ans), p, x⟩ = ⟨(8, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, moveHead]; rfl

theorem step_B0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dIndexM ⟨(8, ans), p, x⟩ = ⟨(9, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_B0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dIndexM ⟨(8, ans), p, x⟩ = ⟨(10, ans), 0, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_B1_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dIndexM ⟨(9, ans), p, x⟩ = ⟨(3, ans), 0, writeAt x p false⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_B1_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dIndexM ⟨(9, ans), p, x⟩ = ⟨(8, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_D0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dIndexM ⟨(10, ans), p, x⟩ = ⟨(11, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_D0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dIndexM ⟨(10, ans), p, x⟩ = ⟨(14, false), p, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_D1_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dIndexM ⟨(11, ans), p, x⟩ = ⟨(12, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_D1_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dIndexM ⟨(11, ans), p, x⟩ = ⟨(13, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, h, moveHead]; rfl

theorem step_D2 {ans : Bool} {p : ℕ} {x : List Bool} :
    step dIndexM ⟨(12, ans), p, x⟩ = ⟨(14, x.getD p false), p, x⟩ := by
  simp only [step, dIndexM, moveHead]; rfl

theorem step_D3 {ans : Bool} {p : ℕ} {x : List Bool} :
    step dIndexM ⟨(13, ans), p, x⟩ = ⟨(10, ans), p + 1, x⟩ := by
  simp only [step, dIndexM, moveHead]; rfl

theorem unitsOf_flatU (us : List (Bool × Bool)) : ∀ suf : List Bool,
    (suf = [] ∨ suf = [true] ∨ (∃ x, suf = [true, x]) ∨ ∃ r, suf = false :: r) →
    unitsOf (flatU us ++ suf) = us := by
  induction us with
  | nil =>
    intro suf hsuf
    rcases hsuf with rfl | rfl | ⟨x, rfl⟩ | ⟨r, rfl⟩ <;> rfl
  | cons u us ih =>
    intro suf hsuf
    obtain ⟨m, d⟩ := u
    show (m, d) :: unitsOf (flatU us ++ suf) = (m, d) :: us
    rw [ih suf hsuf]

/-! ## Walk lemmas -/

/-- Unflagged data walk: traverse the units, tape unchanged. -/
theorem walkA (us : List (Bool × Bool)) : ∀ (P suf : List Bool) (ans : Bool),
    run dIndexM (3 * us.length) ⟨(0, ans), P.length, P ++ (flatU us ++ suf)⟩
      = ⟨(0, ans), P.length + 3 * us.length, P ++ (flatU us ++ suf)⟩ := by
  induction us with
  | nil =>
    intro P suf ans
    simp [flatU, run_zero]
  | cons u us ih =>
    intro P suf ans
    obtain ⟨m, d⟩ := u
    show run dIndexM (3 * (us.length + 1))
        ⟨(0, ans), P.length, P ++ (true :: m :: d :: (flatU us ++ suf))⟩
      = ⟨(0, ans), P.length + 3 * (us.length + 1),
          P ++ (true :: m :: d :: (flatU us ++ suf))⟩
    rw [show P.length + 3 * (us.length + 1) = (P ++ [true, m, d]).length + 3 * us.length from by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega]
    rw [show 3 * (us.length + 1) = 3 + 3 * us.length from by omega, run_add, run_three,
      step_A0_T (getD_at P true _), step_A1, step_A2]
    have htape : P ++ (true :: m :: d :: (flatU us ++ suf))
        = (P ++ [true, m, d]) ++ (flatU us ++ suf) := by simp
    have hlen : P.length + 1 + 1 + 1 = (P ++ [true, m, d]).length := by simp
    rw [htape, hlen, ih (P ++ [true, m, d]) suf ans]

/-- Flagged data walk: traverse the units, marking the first live one; exits unflagged
if it marked, flagged if there was nothing to mark. -/
theorem walkAf (us : List (Bool × Bool)) : ∀ (P suf : List Bool) (ans : Bool),
    ∃ s : Fin 15, (s = 0 ∨ s = 3) ∧
      run dIndexM (3 * us.length) ⟨(3, ans), P.length, P ++ (flatU us ++ suf)⟩
        = ⟨(s, ans), P.length + 3 * us.length, P ++ (flatU (markFirst us) ++ suf)⟩ := by
  induction us with
  | nil =>
    intro P suf ans
    exact ⟨3, Or.inr rfl, by simp [flatU, markFirst, run_zero]⟩
  | cons u us ih =>
    intro P suf ans
    obtain ⟨m, d⟩ := u
    cases m
    · -- already marked: skip, keep the flag
      obtain ⟨s, hs, hrun⟩ := ih (P ++ [true, false, d]) suf ans
      refine ⟨s, hs, ?_⟩
      show run dIndexM (3 * (us.length + 1))
          ⟨(3, ans), P.length, P ++ (true :: false :: d :: (flatU us ++ suf))⟩
        = ⟨(s, ans), P.length + 3 * (us.length + 1),
            P ++ (true :: false :: d :: (flatU (markFirst us) ++ suf))⟩
      rw [show P.length + 3 * (us.length + 1)
            = (P ++ [true, false, d]).length + 3 * us.length from by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega,
        show P ++ (true :: false :: d :: (flatU (markFirst us) ++ suf))
          = (P ++ [true, false, d]) ++ (flatU (markFirst us) ++ suf) from by simp]
      rw [show 3 * (us.length + 1) = 3 + 3 * us.length from by omega, run_add, run_three,
        step_A0f_T (getD_at P true _),
        show P.length + 1 = (P ++ [true]).length from by simp,
        show P ++ (true :: false :: d :: (flatU us ++ suf))
          = (P ++ [true]) ++ false :: (d :: (flatU us ++ suf)) from by simp,
        step_A1f_F (getD_at (P ++ [true]) false _), step_A2f]
      have htape : (P ++ [true]) ++ false :: (d :: (flatU us ++ suf))
          = (P ++ [true, false, d]) ++ (flatU us ++ suf) := by simp
      have hlen : (P ++ [true]).length + 1 + 1 = (P ++ [true, false, d]).length := by simp
      rw [htape, hlen, hrun]
    · -- live: mark it, drop the flag, finish unflagged
      refine ⟨0, Or.inl rfl, ?_⟩
      show run dIndexM (3 * (us.length + 1))
          ⟨(3, ans), P.length, P ++ (true :: true :: d :: (flatU us ++ suf))⟩
        = ⟨(0, ans), P.length + 3 * (us.length + 1),
            P ++ (true :: false :: d :: (flatU us ++ suf))⟩
      rw [show P.length + 3 * (us.length + 1)
            = (P ++ [true, false, d]).length + 3 * us.length from by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega,
        show P ++ (true :: false :: d :: (flatU us ++ suf))
          = (P ++ [true, false, d]) ++ (flatU us ++ suf) from by simp]
      rw [show 3 * (us.length + 1) = 3 + 3 * us.length from by omega, run_add, run_three,
        step_A0f_T (getD_at P true _),
        show P.length + 1 = (P ++ [true]).length from by simp,
        show P ++ (true :: true :: d :: (flatU us ++ suf))
          = (P ++ [true]) ++ true :: (d :: (flatU us ++ suf)) from by simp,
        step_A1f_T (getD_at (P ++ [true]) true _), writeAt_boundary]
      rw [step_A2]
      have htape : (P ++ [true]) ++ false :: (d :: (flatU us ++ suf))
          = (P ++ [true, false, d]) ++ (flatU us ++ suf) := by simp
      have hlen : (P ++ [true]).length + 1 + 1 = (P ++ [true, false, d]).length := by simp
      rw [htape, hlen, walkA us (P ++ [true, false, d]) suf ans]

/-- Terminator crossing (from either data-walk exit state), driven by a `false` read. -/
theorem crossAt {s : Fin 15} (hs : s = 0 ∨ s = 3) (p : ℕ) (x : List Bool) (ans : Bool)
    (h : x.getD p false = false) :
    run dIndexM 3 ⟨(s, ans), p, x⟩ = ⟨(8, ans), p + 3, x⟩ := by
  rw [show p + 3 = p + 1 + 1 + 1 from by omega]
  rcases hs with rfl | rfl
  · rw [run_three, step_A0_F h, step_A3, step_A4]
  · rw [run_three, step_A0f_F h, step_A3, step_A4]

/-- Address walk over consumed units. -/
theorem walkB (as : List Bool) : ∀ (P suf : List Bool) (ans : Bool),
    (∀ b ∈ as, b = false) →
    run dIndexM (2 * as.length) ⟨(8, ans), P.length, P ++ (flat2 as ++ suf)⟩
      = ⟨(8, ans), P.length + 2 * as.length, P ++ (flat2 as ++ suf)⟩ := by
  induction as with
  | nil =>
    intro P suf ans _
    simp [flat2, run_zero]
  | cons a as ih =>
    intro P suf ans hall
    have ha : a = false := hall a (List.mem_cons_self ..)
    subst ha
    show run dIndexM (2 * (as.length + 1))
        ⟨(8, ans), P.length, P ++ (true :: false :: (flat2 as ++ suf))⟩
      = ⟨(8, ans), P.length + 2 * (as.length + 1),
          P ++ (true :: false :: (flat2 as ++ suf))⟩
    rw [show P.length + 2 * (as.length + 1) = (P ++ [true, false]).length + 2 * as.length from by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega]
    rw [show 2 * (as.length + 1) = 2 + 2 * as.length from by omega, run_add, run_two,
      step_B0_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 as ++ suf))
        = (P ++ [true]) ++ false :: (flat2 as ++ suf) from by simp,
      step_B1_F (getD_at (P ++ [true]) false _)]
    have htape : (P ++ [true]) ++ false :: (flat2 as ++ suf)
        = (P ++ [true, false]) ++ (flat2 as ++ suf) := by simp
    have hlen : (P ++ [true]).length + 1 = (P ++ [true, false]).length := by simp
    rw [htape, hlen, ih (P ++ [true, false]) suf ans (fun b hb => hall b (List.mem_cons_of_mem _ hb))]

/-- Consume a live address unit: write, set the round flag, reset. -/
theorem consumeB (P rest : List Bool) (ans : Bool) :
    run dIndexM 2 ⟨(8, ans), P.length, P ++ (true :: true :: rest)⟩
      = ⟨(3, ans), 0, P ++ (true :: false :: rest)⟩ := by
  rw [show P ++ (true :: false :: rest) = (P ++ [true]) ++ false :: rest from by simp,
    run_two, step_B0_T (getD_at P true _),
    show P.length + 1 = (P ++ [true]).length from by simp,
    show P ++ (true :: true :: rest) = (P ++ [true]) ++ true :: rest from by simp,
    step_B1_T (getD_at (P ++ [true]) true _), writeAt_boundary]

/-- The exhausted-address phase: cross the consumed units, then reset into the answer
phase at the block's end (empty, phantom, or `false`-headed). -/
theorem bPhase (as : List Bool) (P asuf : List Bool) (ans : Bool)
    (hall : ∀ b ∈ as, b = false)
    (hasuf : asuf = [] ∨ asuf = [true] ∨ ∃ r, asuf = false :: r) :
    ∃ t ≤ 2 * as.length + 5,
      run dIndexM t ⟨(8, ans), P.length, P ++ (flat2 as ++ asuf)⟩
        = ⟨(10, ans), 0, P ++ (flat2 as ++ asuf)⟩ := by
  have hw := walkB as P asuf ans hall
  have htape : P ++ (flat2 as ++ asuf) = (P ++ flat2 as) ++ asuf := by simp
  have hlen : P.length + 2 * as.length = (P ++ flat2 as).length := by
    simp [flat2_length]
  rcases hasuf with rfl | rfl | ⟨r, rfl⟩
  · refine ⟨2 * as.length + 1, by omega, ?_⟩
    rw [run_add, hw, run_one, htape, hlen,
      step_B0_F (getD_beyond _ _ (by simp))]
  · refine ⟨2 * as.length + 3, by omega, ?_⟩
    rw [run_add, hw, run_three, htape, hlen,
      step_B0_T (getD_at (P ++ flat2 as) true []),
      step_B1_F (getD_beyond _ _ (by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega)),
      step_B0_F (getD_beyond _ _ (by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega))]
  · refine ⟨2 * as.length + 1, by omega, ?_⟩
    rw [run_add, hw, run_one, htape, hlen,
      step_B0_F (getD_at (P ++ flat2 as) false r)]

/-- The answer phase: skip marked units, halt with the first live payload (`false` at
the terminator, a phantom, or the void). -/
theorem dPhase (us : List (Bool × Bool)) : ∀ (P suf : List Bool) (ans : Bool),
    (suf = [] ∨ suf = [true] ∨ (∃ x, suf = [true, x]) ∨ ∃ r, suf = false :: r) →
    ∃ t ≤ 3 * us.length + 10, ∃ p x',
      run dIndexM t ⟨(10, ans), P.length, P ++ (flatU us ++ suf)⟩
        = ⟨(14, ansOf us), p, x'⟩ := by
  induction us with
  | nil =>
    intro P suf ans hsuf
    rcases hsuf with rfl | rfl | ⟨x, rfl⟩ | ⟨r, rfl⟩
    · refine ⟨1, by omega, P.length, P ++ ([] ++ []), ?_⟩
      rw [run_one, step_D0_F (getD_beyond _ _ (by simp [flatU]))]
      rfl
    · refine ⟨4, by omega, P.length + 1 + 1 + 1, P ++ ([] ++ [true]), ?_⟩
      rw [run_four,
        show P ++ (flatU [] ++ [true]) = P ++ true :: [] from by simp [flatU],
        step_D0_T (getD_at P true []),
        step_D1_F (getD_beyond _ _ (by simp)), step_D3,
        step_D0_F (getD_beyond _ _ (by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega))]
      rfl
    · cases x
      · refine ⟨4, by omega, P.length + 1 + 1 + 1, P ++ ([] ++ [true, false]), ?_⟩
        rw [run_four,
          show P ++ (flatU [] ++ [true, false]) = P ++ true :: [false] from by simp [flatU],
          step_D0_T (getD_at P true [false]),
          show P.length + 1 = (P ++ [true]).length from by simp,
          show P ++ true :: [false] = (P ++ [true]) ++ false :: [] from by simp,
          step_D1_F (getD_at (P ++ [true]) false []), step_D3,
          step_D0_F (getD_beyond _ _ (by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega))]
        simp [ansOf]
      · refine ⟨3, by omega, (P ++ [true]).length + 1, P ++ ([] ++ [true, true]), ?_⟩
        rw [run_three,
          show P ++ (flatU [] ++ [true, true]) = P ++ true :: [true] from by simp [flatU],
          step_D0_T (getD_at P true [true]),
          show P.length + 1 = (P ++ [true]).length from by simp,
          show P ++ true :: [true] = (P ++ [true]) ++ true :: [] from by simp,
          step_D1_T (getD_at (P ++ [true]) true []), step_D2,
          getD_beyond _ _ (by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
        simp [ansOf]
    · refine ⟨1, by omega, P.length, P ++ ([] ++ false :: r), ?_⟩
      rw [run_one,
        show P ++ (flatU [] ++ false :: r) = P ++ false :: r from by simp [flatU],
        step_D0_F (getD_at P false r)]
      rfl
  | cons u us ih =>
    intro P suf ans hsuf
    obtain ⟨m, d⟩ := u
    cases m
    · -- marked: 3 steps, then recurse
      obtain ⟨t, ht, p, x', hrun⟩ := ih (P ++ [true, false, d]) suf ans hsuf
      refine ⟨3 + t, by
        have := markFirst_length us
        simp only [List.length_cons]
        omega, p, x', ?_⟩
      show run dIndexM (3 + t)
          ⟨(10, ans), P.length, P ++ (true :: false :: d :: (flatU us ++ suf))⟩
        = ⟨(14, ansOf ((false, d) :: us)), p, x'⟩
      rw [run_add, run_three, step_D0_T (getD_at P true _),
        show P.length + 1 = (P ++ [true]).length from by simp,
        show P ++ (true :: false :: d :: (flatU us ++ suf))
          = (P ++ [true]) ++ false :: (d :: (flatU us ++ suf)) from by simp,
        step_D1_F (getD_at (P ++ [true]) false _), step_D3]
      have htape : (P ++ [true]) ++ false :: (d :: (flatU us ++ suf))
          = (P ++ [true, false, d]) ++ (flatU us ++ suf) := by simp
      have hlen : (P ++ [true]).length + 1 + 1 = (P ++ [true, false, d]).length := by simp
      rw [htape, hlen, hrun]
      rfl
    · -- live: read the payload and halt
      refine ⟨3, by omega, (P ++ [true, true]).length, P ++ (true :: true :: d :: (flatU us ++ suf)), ?_⟩
      show run dIndexM 3
          ⟨(10, ans), P.length, P ++ (true :: true :: d :: (flatU us ++ suf))⟩
        = ⟨(14, ansOf ((true, d) :: us)), (P ++ [true, true]).length,
            P ++ (true :: true :: d :: (flatU us ++ suf))⟩
      rw [run_three, step_D0_T (getD_at P true _),
        show P.length + 1 = (P ++ [true]).length from by simp,
        show P ++ (true :: true :: d :: (flatU us ++ suf))
          = (P ++ [true]) ++ true :: (d :: (flatU us ++ suf)) from by simp,
        step_D1_T (getD_at (P ++ [true]) true _), step_D2,
        show (P ++ [true]).length + 1 = (P ++ [true, true]).length from by simp,
        show (P ++ [true]) ++ true :: (d :: (flatU us ++ suf))
          = (P ++ [true, true]) ++ d :: (flatU us ++ suf) from by simp,
        getD_at (P ++ [true, true]) d _]
      rfl

/-! ## The grand round induction -/

/-- The flagged-round iteration: each round marks one data unit and consumes one live
address unit; when none remain, the answer phase reads out.  Induction on the live count. -/
theorem grand : ∀ (n : ℕ) (aus : List Bool), aus.count true = n →
    ∀ (dus : List (Bool × Bool)) (a b : Bool) (asuf : List Bool),
    (asuf = [] ∨ asuf = [true] ∨ ∃ r, asuf = false :: r) →
    ∀ ans : Bool,
    ∃ t ≤ (n + 1) * (3 * dus.length + 2 * aus.length + 20) + 3 * dus.length + 10,
      ∃ p x', run dIndexM t
        ⟨(3, ans), 0, flatU dus ++ false :: a :: b :: (flat2 aus ++ asuf)⟩
        = ⟨(14, ansOf (markFirst^[n + 1] dus)), p, x'⟩ := by
  intro n
  induction n with
  | zero =>
    intro aus h0 dus a b asuf hasuf ans
    obtain ⟨s, hs, hAf⟩ := walkAf dus [] (false :: a :: b :: (flat2 aus ++ asuf)) ans
    simp only [List.length_nil, List.nil_append, Nat.zero_add] at hAf
    have hread : (flatU (markFirst dus) ++ false :: a :: b :: (flat2 aus ++ asuf)).getD
        (3 * dus.length) false = false := by
      rw [show 3 * dus.length = (flatU (markFirst dus)).length from by
        rw [flatU_length, markFirst_length]]
      exact getD_at _ false _
    have hCr := crossAt hs (3 * dus.length)
      (flatU (markFirst dus) ++ false :: a :: b :: (flat2 aus ++ asuf)) ans hread
    obtain ⟨tb, htb, hB⟩ := bPhase aus (flatU (markFirst dus) ++ [false, a, b]) asuf ans
      (all_false_of_count_zero h0) hasuf
    obtain ⟨td, htd, p, x', hD⟩ := dPhase (markFirst dus) []
      (false :: a :: b :: (flat2 aus ++ asuf)) ans (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
    simp only [List.length_nil, List.nil_append] at hD
    refine ⟨3 * dus.length + 3 + tb + td, by
      have hM := markFirst_length dus
      omega, p, x', ?_⟩
    rw [run_add, run_add, run_add, hAf, hCr,
      show flatU (markFirst dus) ++ false :: a :: b :: (flat2 aus ++ asuf)
        = (flatU (markFirst dus) ++ [false, a, b]) ++ (flat2 aus ++ asuf) from by simp,
      show 3 * dus.length + 3 = (flatU (markFirst dus) ++ [false, a, b]).length from by
        simp [flatU_length, markFirst_length],
      hB,
      show (flatU (markFirst dus) ++ [false, a, b]) ++ (flat2 aus ++ asuf)
        = flatU (markFirst dus) ++ (false :: a :: b :: (flat2 aus ++ asuf)) from by simp,
      hD, show (0 : ℕ) + 1 = 1 from rfl, Function.iterate_one]
  | succ n ihn =>
    intro aus h0 dus a b asuf hasuf ans
    obtain ⟨fs, rest, rfl, hfs⟩ := exists_first_true aus (by omega)
    have hfs0 : fs.count true = 0 := List.count_eq_zero.mpr (fun hmem => by
      have := hfs true hmem
      simp at this)
    obtain ⟨s, hs, hAf⟩ := walkAf dus []
      (false :: a :: b :: (flat2 (fs ++ true :: rest) ++ asuf)) ans
    simp only [List.length_nil, List.nil_append, Nat.zero_add] at hAf
    have hread : (flatU (markFirst dus)
        ++ false :: a :: b :: (flat2 (fs ++ true :: rest) ++ asuf)).getD
        (3 * dus.length) false = false := by
      rw [show 3 * dus.length = (flatU (markFirst dus)).length from by
        rw [flatU_length, markFirst_length]]
      exact getD_at _ false _
    have hCr := crossAt hs (3 * dus.length)
      (flatU (markFirst dus) ++ false :: a :: b :: (flat2 (fs ++ true :: rest) ++ asuf))
      ans hread
    have hWB := walkB fs (flatU (markFirst dus) ++ [false, a, b])
      (true :: true :: (flat2 rest ++ asuf)) ans hfs
    have hCons := consumeB ((flatU (markFirst dus) ++ [false, a, b]) ++ flat2 fs)
      (flat2 rest ++ asuf) ans
    have h0' : (fs ++ false :: rest).count true = n := by
      rw [List.count_append, List.count_cons_self, hfs0] at h0
      rw [List.count_append, List.count_cons_of_ne (by decide), hfs0]
      omega
    obtain ⟨t', ht', p, x', hIH⟩ := ihn (fs ++ false :: rest) h0' (markFirst dus) a b
      asuf hasuf ans
    refine ⟨3 * dus.length + 3 + 2 * fs.length + 2 + t', by
      have hM := markFirst_length dus
      rw [hM] at ht'
      have hA1 : (fs ++ false :: rest).length = (fs ++ true :: rest).length := by simp
      rw [hA1] at ht'
      have hexp : (n + 1 + 1) * (3 * dus.length + 2 * (fs ++ true :: rest).length + 20)
          = (n + 1) * (3 * dus.length + 2 * (fs ++ true :: rest).length + 20)
            + (3 * dus.length + 2 * (fs ++ true :: rest).length + 20) := by ring
      have hfsle : fs.length ≤ (fs ++ true :: rest).length := by
        simp only [List.length_append, List.length_cons]
        omega
      omega, p, x', ?_⟩
    rw [run_add, run_add, run_add, run_add, hAf, hCr,
      show flatU (markFirst dus) ++ false :: a :: b :: (flat2 (fs ++ true :: rest) ++ asuf)
        = (flatU (markFirst dus) ++ [false, a, b])
            ++ (flat2 fs ++ (true :: true :: (flat2 rest ++ asuf))) from by
        simp [flat2_append, flat2],
      show 3 * dus.length + 3 = (flatU (markFirst dus) ++ [false, a, b]).length from by
        simp [flatU_length, markFirst_length],
      hWB,
      show (flatU (markFirst dus) ++ [false, a, b])
          ++ (flat2 fs ++ (true :: true :: (flat2 rest ++ asuf)))
        = ((flatU (markFirst dus) ++ [false, a, b]) ++ flat2 fs)
            ++ (true :: true :: (flat2 rest ++ asuf)) from by simp,
      show (flatU (markFirst dus) ++ [false, a, b]).length + 2 * fs.length
        = ((flatU (markFirst dus) ++ [false, a, b]) ++ flat2 fs).length from by
        simp only [List.length_append, List.length_cons, List.length_nil, flat2_length]
        try omega,
      hCons,
      show ((flatU (markFirst dus) ++ [false, a, b]) ++ flat2 fs)
          ++ true :: false :: (flat2 rest ++ asuf)
        = flatU (markFirst dus)
            ++ (false :: a :: b :: (flat2 (fs ++ false :: rest) ++ asuf)) from by
        simp [flat2_append, flat2],
      hIH, show markFirst^[n + 1] (markFirst dus) = markFirst^[n + 1 + 1] dus from
        (Function.iterate_succ_apply markFirst (n + 1) dus).symm]

/-! ## Assembly: total halting with the spec's answer -/

theorem dIndexM_halts (w : List Bool) :
    ∃ t ≤ (w.length + 3) * (3 * w.length + 60), ∃ p x',
      run dIndexM t (init dIndexM w) = ⟨(14, dIndexLang w), p, x'⟩ := by
  have hdec := decompU w
  have hDlen : 3 * (unitsOf w).length ≤ w.length := by
    conv_rhs => rw [← hdec]
    simp [flatU_length]
  have hA := walkA (unitsOf w) [] (dataSuf w) false
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hA
  have hinit : init dIndexM w = ⟨(0, false), 0, flatU (unitsOf w) ++ dataSuf w⟩ := by
    rw [hdec]
    rfl
  have hspec : dIndexLang w
      = (liveDataU (unitsOf w)).getD (liveCount (postData w)) false := by
    show (liveData w).getD (liveCount (postData w)) false = _
    rw [liveData_eq]
  have hpost : postData w = (dataSuf w).drop 3 := by
    conv_lhs => rw [← hdec]
    exact postData_flatU (unitsOf w) (dataSuf w) (dataSuf_shape w)
  rcases hshape : dataSuf w with _ | ⟨c, r⟩
  · -- dataSuf = []
    obtain ⟨td, htd, p, x', hD⟩ := dPhase (unitsOf w) [] [] false (Or.inl rfl)
    simp only [List.length_nil, List.nil_append] at hD
    rw [hshape] at hA
    refine ⟨3 * (unitsOf w).length + 3 + 1 + td, by
      have hexp : (w.length + 3) * (3 * w.length + 60)
          = 3 * (w.length * w.length) + 69 * w.length + 180 := by ring
      omega, p, x', ?_⟩
    rw [hinit, hshape, run_add, run_add, run_add, hA,
      crossAt (Or.inl rfl) _ _ _ (getD_beyond _ _ (by simp [flatU_length])),
      run_one, step_B0_F (getD_beyond _ _ (by simp [flatU_length]; try omega)), hD,
      hspec, hpost, hshape]
    rw [show liveCount (([] : List Bool).drop 3) = 0 from rfl, ← ansOf_getD]
  · rcases hshape2 : c with _ | _
    case false =>
      -- dataSuf = false :: r : cross, then split on the address block
      subst hshape2
      have hreadF : (flatU (unitsOf w) ++ false :: r).getD
          (3 * (unitsOf w).length) false = false := by
        rw [show 3 * (unitsOf w).length = (flatU (unitsOf w)).length from
          (flatU_length _).symm]
        exact getD_at _ false _
      rcases hr : r with _ | ⟨a', r2⟩
      · -- r = []
        obtain ⟨td, htd, p, x', hD⟩ := dPhase (unitsOf w) [] (false :: []) false
          (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
        simp only [List.length_nil, List.nil_append] at hD
        rw [hshape, hr] at hA
        refine ⟨3 * (unitsOf w).length + 3 + 1 + td, by
          have hexp : (w.length + 3) * (3 * w.length + 60)
              = 3 * (w.length * w.length) + 69 * w.length + 180 := by ring
          omega, p, x', ?_⟩
        rw [hinit, hshape, hr, run_add, run_add, run_add, hA,
          crossAt (Or.inl rfl) _ _ _ (by rw [hr] at hreadF; exact hreadF),
          run_one, step_B0_F (getD_beyond _ _ (by simp [flatU_length]; try omega)), hD,
          hspec, hpost, hshape, hr]
        rw [show liveCount ((false :: [] : List Bool).drop 3) = 0 from rfl, ← ansOf_getD]
      · rcases hr2 : r2 with _ | ⟨b', apart⟩
        · -- r = [a']
          obtain ⟨td, htd, p, x', hD⟩ := dPhase (unitsOf w) [] (false :: [a']) false
            (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
          simp only [List.length_nil, List.nil_append] at hD
          rw [hshape, hr, hr2] at hA
          refine ⟨3 * (unitsOf w).length + 3 + 1 + td, by
            have hexp : (w.length + 3) * (3 * w.length + 60)
                = 3 * (w.length * w.length) + 69 * w.length + 180 := by ring
            omega, p, x', ?_⟩
          rw [hinit, hshape, hr, hr2, run_add, run_add, run_add, hA,
            crossAt (Or.inl rfl) _ _ _ (by rw [hr, hr2] at hreadF; exact hreadF),
            run_one, step_B0_F (getD_beyond _ _ (by simp [flatU_length]; try omega)), hD,
            hspec, hpost, hshape, hr, hr2]
          rw [show liveCount ((false :: [a'] : List Bool).drop 3) = 0 from rfl,
            ← ansOf_getD]
        · -- r = a' :: b' :: apart : the real address block
          have hdec2 := decomp2 apart
          have hAlen : 2 * (unitsOf2 apart).length ≤ w.length := by
            have h1 : (flat2 (unitsOf2 apart)).length ≤ apart.length := by
              conv_rhs => rw [← hdec2]
              simp
            rw [flat2_length] at h1
            have h2 : apart.length ≤ w.length := by
              conv_rhs => rw [← hdec]
              rw [hshape, hr, hr2]
              simp
              omega
            omega
          have hcount : liveCount (postData w) = (unitsOf2 apart).count true := by
            rw [hpost, hshape, hr, hr2]
            show liveCount apart = _
            exact liveCount_eq apart
          rcases Nat.eq_zero_or_pos ((unitsOf2 apart).count true) with hz | hpos
          · -- no live address units: answer is index 0
            obtain ⟨tb, htb, hB⟩ := bPhase (unitsOf2 apart)
              (flatU (unitsOf w) ++ [false, a', b']) (addrSuf apart) false
              (all_false_of_count_zero hz) (addrSuf_shape apart)
            obtain ⟨td, htd, p, x', hD⟩ := dPhase (unitsOf w) []
              (false :: a' :: b' :: apart) false (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
            simp only [List.length_nil, List.nil_append] at hD
            rw [hshape, hr, hr2] at hA
            refine ⟨3 * (unitsOf w).length + 3 + tb + td, by
              have hexp : (w.length + 3) * (3 * w.length + 60)
                  = 3 * (w.length * w.length) + 69 * w.length + 180 := by ring
              omega, p, x', ?_⟩
            rw [hinit, hshape, hr, hr2, run_add, run_add, run_add, hA,
              crossAt (Or.inl rfl) _ _ _ (by rw [hr, hr2] at hreadF; exact hreadF),
              show flatU (unitsOf w) ++ false :: a' :: b' :: apart
                = (flatU (unitsOf w) ++ [false, a', b'])
                    ++ (flat2 (unitsOf2 apart) ++ addrSuf apart) from by
                rw [hdec2]
                simp,
              show 3 * (unitsOf w).length + 3
                = (flatU (unitsOf w) ++ [false, a', b']).length from by
                simp [flatU_length],
              hB,
              show (flatU (unitsOf w) ++ [false, a', b'])
                  ++ (flat2 (unitsOf2 apart) ++ addrSuf apart)
                = flatU (unitsOf w) ++ (false :: a' :: b' :: apart) from by
                rw [hdec2]
                simp,
              hD, hspec, hcount, hz, ← ansOf_getD]
          · -- live address units: round one consumes the first, then `grand`
            obtain ⟨fs, rest, hsplit, hfs⟩ := exists_first_true (unitsOf2 apart) hpos
            have hfs0 : fs.count true = 0 := List.count_eq_zero.mpr (fun hmem => by
              have := hfs true hmem
              simp at this)
            have hrest : rest.count true = (unitsOf2 apart).count true - 1 := by
              rw [hsplit, List.count_append, List.count_cons_self, hfs0]
              omega
            have hWB := walkB fs (flatU (unitsOf w) ++ [false, a', b'])
              (true :: true :: (flat2 rest ++ addrSuf apart)) false hfs
            have hCons := consumeB ((flatU (unitsOf w) ++ [false, a', b']) ++ flat2 fs)
              (flat2 rest ++ addrSuf apart) false
            obtain ⟨t', ht', p, x', hG⟩ := grand ((unitsOf2 apart).count true - 1)
              (fs ++ false :: rest) (by
                rw [List.count_append, List.count_cons_of_ne (by decide), hfs0]
                omega)
              (unitsOf w) a' b' (addrSuf apart) (addrSuf_shape apart) false
            rw [hshape, hr, hr2] at hA
            refine ⟨3 * (unitsOf w).length + 3 + 2 * fs.length + 2 + t', by
              have hfsle : fs.length ≤ (unitsOf2 apart).length := by
                rw [hsplit]
                simp only [List.length_append, List.length_cons]
                omega
              have hcle : (unitsOf2 apart).count true ≤ (unitsOf2 apart).length :=
                List.count_le_length
              have hA1 : (fs ++ false :: rest).length = (unitsOf2 apart).length := by
                rw [hsplit]
                simp
              rw [hA1] at ht'
              have hexp : ((unitsOf2 apart).count true - 1 + 1)
                    * (3 * (unitsOf w).length + 2 * (unitsOf2 apart).length + 20)
                  ≤ (unitsOf2 apart).count true
                    * (3 * (unitsOf w).length + 2 * (unitsOf2 apart).length + 20) := by
                exact Nat.mul_le_mul_right _ (by omega)
              have hexp2 : (unitsOf2 apart).count true
                    * (3 * (unitsOf w).length + 2 * (unitsOf2 apart).length + 20)
                  ≤ (unitsOf2 apart).length
                    * (3 * (unitsOf w).length + 2 * (unitsOf2 apart).length + 20) :=
                Nat.mul_le_mul_right _ hcle
              have hbig : (unitsOf2 apart).length
                    * (3 * (unitsOf w).length + 2 * (unitsOf2 apart).length + 20)
                  ≤ w.length * (3 * w.length + 60) := by
                have h1 : (unitsOf2 apart).length ≤ w.length := by omega
                have h2 : 3 * (unitsOf w).length + 2 * (unitsOf2 apart).length + 20
                    ≤ 3 * w.length + 60 := by omega
                exact Nat.mul_le_mul h1 h2
              have hfin : w.length * (3 * w.length + 60) + 3 * w.length + 60
                  ≤ (w.length + 3) * (3 * w.length + 60) := by
                have : (w.length + 3) * (3 * w.length + 60)
                    = w.length * (3 * w.length + 60) + 3 * (3 * w.length + 60) := by ring
                omega
              omega, p, x', ?_⟩
            rw [hinit, hshape, hr, hr2, run_add, run_add, run_add, run_add, hA,
              crossAt (Or.inl rfl) _ _ _ (by rw [hr, hr2] at hreadF; exact hreadF),
              show flatU (unitsOf w) ++ false :: a' :: b' :: apart
                = (flatU (unitsOf w) ++ [false, a', b'])
                    ++ (flat2 fs ++ (true :: true :: (flat2 rest ++ addrSuf apart)))
                  from by
                conv_lhs => rw [← hdec2, hsplit]
                simp [flat2_append, flat2],
              show 3 * (unitsOf w).length + 3
                = (flatU (unitsOf w) ++ [false, a', b']).length from by
                simp [flatU_length],
              hWB,
              show (flatU (unitsOf w) ++ [false, a', b'])
                  ++ (flat2 fs ++ (true :: true :: (flat2 rest ++ addrSuf apart)))
                = ((flatU (unitsOf w) ++ [false, a', b']) ++ flat2 fs)
                    ++ (true :: true :: (flat2 rest ++ addrSuf apart)) from by simp,
              show (flatU (unitsOf w) ++ [false, a', b']).length + 2 * fs.length
                = ((flatU (unitsOf w) ++ [false, a', b']) ++ flat2 fs).length from by
                simp only [List.length_append, List.length_cons, List.length_nil,
                  flat2_length]
                try omega,
              hCons,
              show ((flatU (unitsOf w) ++ [false, a', b']) ++ flat2 fs)
                  ++ true :: false :: (flat2 rest ++ addrSuf apart)
                = flatU (unitsOf w)
                    ++ (false :: a' :: b' :: (flat2 (fs ++ false :: rest)
                        ++ addrSuf apart)) from by
                simp [flat2_append, flat2],
              hG, hspec, hcount,
              show (unitsOf2 apart).count true - 1 + 1 = (unitsOf2 apart).count true from by
                omega,
              ansOf_iter]
    case true =>
      -- dataSuf = true :: r (phantom): r = [] or [x]
      subst hshape2
      have hphantom : ∀ tail : List Bool, tail = [] ∨ (∃ x, tail = [x]) →
          dataSuf w = true :: tail →
          ∃ t ≤ (w.length + 3) * (3 * w.length + 60), ∃ p x',
            run dIndexM t (init dIndexM w) = ⟨(14, dIndexLang w), p, x'⟩ := by
        intro tail htail hds
        obtain ⟨td, htd, p, x', hD⟩ := dPhase (unitsOf w) [] (true :: tail) false
          (by rcases htail with rfl | ⟨x, rfl⟩
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr (Or.inl ⟨x, rfl⟩)))
        simp only [List.length_nil, List.nil_append] at hD
        have hlentail : (flatU (unitsOf w) ++ true :: tail).length
            ≤ 3 * (unitsOf w).length + 2 := by
          rcases htail with rfl | ⟨x, rfl⟩ <;> simp [flatU_length]
        have hreadT : (flatU (unitsOf w) ++ true :: tail).getD
            (3 * (unitsOf w).length) false = true := by
          rw [show 3 * (unitsOf w).length = (flatU (unitsOf w)).length from
            (flatU_length _).symm]
          exact getD_at _ true _
        rw [hds] at hA
        have hph : run dIndexM 3 ⟨(0, false), 3 * (unitsOf w).length,
              flatU (unitsOf w) ++ true :: tail⟩
            = ⟨(0, false), 3 * (unitsOf w).length + 3,
                flatU (unitsOf w) ++ true :: tail⟩ := by
          rw [show 3 * (unitsOf w).length + 3
              = 3 * (unitsOf w).length + 1 + 1 + 1 from by omega,
            run_three, step_A0_T hreadT, step_A1, step_A2]
        refine ⟨3 * (unitsOf w).length + 3 + 3 + 1 + td, by
          have hexp : (w.length + 3) * (3 * w.length + 60)
              = 3 * (w.length * w.length) + 69 * w.length + 180 := by ring
          omega, p, x', ?_⟩
        rw [hinit, hds, run_add, run_add, run_add, run_add, hA, hph,
          crossAt (Or.inl rfl) _ _ _ (getD_beyond _ _ (by omega)),
          run_one, step_B0_F (getD_beyond _ _ (by omega)), hD,
          hspec, hpost, hds]
        rcases htail with rfl | ⟨x, rfl⟩
        · rw [show liveCount ((true :: [] : List Bool).drop 3) = 0 from rfl, ← ansOf_getD]
        · rw [show liveCount ((true :: [x] : List Bool).drop 3) = 0 from rfl, ← ansOf_getD]
      rcases hr : r with _ | ⟨x, r2⟩
      · exact hphantom [] (Or.inl rfl) (by rw [hshape, hr])
      · rcases hr2 : r2 with _ | ⟨y, r3⟩
        · exact hphantom [x] (Or.inr ⟨x, rfl⟩) (by rw [hshape, hr, hr2])
        · -- dataSuf can never be a full 3-cell unit: it is the recursion's stop shape
          exfalso
          rcases dataSuf_shape w with h | h | ⟨z, h⟩ | ⟨r', h⟩ <;>
            rw [hshape, hr, hr2] at h <;> simp at h

/-! ## The fence, discharged -/

/-- **The machine decides the doubled-INDEX language** within the polynomial clock. -/
theorem dIndexM_decides :
    Decides dIndexM dIndexLang (fun n => (n + 3) * (3 * n + 60)) := by
  intro x
  obtain ⟨t, ht, p, x', hrun⟩ := dIndexM_halts x
  have hhalt : dIndexM.halt (run dIndexM t (init dIndexM x)).st = true := by
    rw [hrun]
    rfl
  have hstable : run dIndexM ((x.length + 3) * (3 * x.length + 60)) (init dIndexM x)
      = run dIndexM t (init dIndexM x) := run_stable dIndexM x ht hhalt
  constructor
  · show dIndexM.halt (run dIndexM _ (init dIndexM x)).st = true
    rw [hstable, hrun]
    rfl
  · show dIndexM.accept (run dIndexM _ (init dIndexM x)).st = dIndexLang x
    rw [hstable, hrun]
    rfl

/-- The clock is polynomially bounded. -/
theorem dIndexM_clock_poly : PolyBounded (fun n => (n + 3) * (3 * n + 60)) := by
  refine ⟨249, 2, fun n => ?_⟩
  show (n + 3) * (3 * n + 60) ≤ 249 * (n + 1) ^ 2
  have e1 : (n + 3) * (3 * n + 60) = 3 * (n * n) + 69 * n + 180 := by ring
  have e2 : 249 * (n + 1) ^ 2 = 249 * (n * n) + 498 * n + 249 := by ring
  omega

/-- **`DIndexInP`, discharged**: the doubled-INDEX language is in the faithful P. -/
theorem dIndexInP : DIndexInP :=
  ⟨dIndexM, fun n => (n + 3) * (3 * n + 60), dIndexM_clock_poly, dIndexM_decides⟩

/-- **The language-level kill, unconditional.**  Every language-level measure dominating
subfunction counts fails generic soundness — no hypotheses remain. -/
theorem langRank_kill_unconditional (μ : LangMeasure)
    (hdom : ∀ L n, subfunProfile L n ≤ μ L n) : ¬ LangGenSound μ :=
  langRank_kill μ hdom dIndexInP

end PallLean.Paper93.DeepMath.PathB.DIndexMachine
