import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDIndexMachine

/-!
# Restoring marked-store lookup on the actual local machine

The data/address frame uses DIndexMachine's marked triple/double cells.
Lookup temporarily changes mark cells, then restores them while retaining the
answer in finite control. No stored program compiler or full evaluator clock
is asserted here.
-/

namespace GodMoveMarkedReadMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine
open PallLean.Paper93.DeepMath.PathB.LangRankKill

private theorem answer_step (c : Cfg dIndexM) (h : 10 ≤ c.st.1.val) :
    (step dIndexM c).tp = c.tp ∧ 10 ≤ (step dIndexM c).st.1.val := by
  rcases c with ⟨⟨st, ans⟩, p, x⟩
  cases hb : x.getD p false <;> fin_cases st <;> simp_all [step, dIndexM, moveHead]

private theorem answer_run (t : ℕ) (c : Cfg dIndexM) (h : 10 ≤ c.st.1.val) :
    (run dIndexM t c).tp = c.tp ∧ 10 ≤ (run dIndexM t c).st.1.val := by
  induction t with
  | zero => exact ⟨rfl, h⟩
  | succ t ih =>
      have hs := answer_step (run dIndexM t c) ih.2
      rw [run_succ]
      exact ⟨hs.1.trans ih.1, hs.2⟩

/-- The existing answer walk does not alter even its workspace suffix. -/
theorem dPhase_tape (us : List (Bool × Bool)) (P suf : List Bool) (ans : Bool)
    (hsuf : suf = [] ∨ suf = [true] ∨ (∃ x, suf = [true, x]) ∨ ∃ r, suf = false :: r) :
    ∃ t ≤ 3 * us.length + 10, ∃ p,
      run dIndexM t ⟨(10, ans), P.length, P ++ (flatU us ++ suf)⟩ =
        ⟨(14, ansOf us), p, P ++ (flatU us ++ suf)⟩ := by
  obtain ⟨t, ht, p, x', hr⟩ := dPhase us P suf ans hsuf
  have hx := (answer_run t ⟨(10, ans), P.length, P ++ (flatU us ++ suf)⟩
    (show 10 ≤ 10 from by decide)).1
  rw [hr] at hx
  change x' = P ++ (flatU us ++ suf) at hx
  subst x'
  exact ⟨t, ht, p, hr⟩

theorem grand_tape : ∀ (n : ℕ) (aus : List Bool), aus.count true = n →
    ∀ (dus : List (Bool × Bool)) (a b : Bool) (asuf : List Bool),
    (asuf = [] ∨ asuf = [true] ∨ ∃ r, asuf = false :: r) →
    ∀ ans : Bool,
    ∃ t ≤ (n + 1) * (3 * dus.length + 2 * aus.length + 20) + 3 * dus.length + 10,
      ∃ p, run dIndexM t
        ⟨(3, ans), 0, flatU dus ++ false :: a :: b :: (flat2 aus ++ asuf)⟩
        = ⟨(14, ansOf (markFirst^[n + 1] dus)), p,
          flatU (markFirst^[n + 1] dus) ++ false :: a :: b ::
            (flat2 (List.replicate aus.length false) ++ asuf)⟩ := by
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
    obtain ⟨td, htd, p, hD⟩ := dPhase_tape (markFirst dus) []
      (false :: a :: b :: (flat2 aus ++ asuf)) ans (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
    simp only [List.length_nil, List.nil_append] at hD
    refine ⟨3 * dus.length + 3 + tb + td, by
      have hM := markFirst_length dus
      omega, p, ?_⟩
    rw [run_add, run_add, run_add, hAf, hCr,
      show flatU (markFirst dus) ++ false :: a :: b :: (flat2 aus ++ asuf)
        = (flatU (markFirst dus) ++ [false, a, b]) ++ (flat2 aus ++ asuf) from by simp,
      show 3 * dus.length + 3 = (flatU (markFirst dus) ++ [false, a, b]).length from by
        simp [flatU_length, markFirst_length],
      hB,
      show (flatU (markFirst dus) ++ [false, a, b]) ++ (flat2 aus ++ asuf)
        = flatU (markFirst dus) ++ (false :: a :: b :: (flat2 aus ++ asuf)) from by simp,
      hD, show (0 : ℕ) + 1 = 1 from rfl, Function.iterate_one]
    rw [← List.eq_replicate_length.mpr (all_false_of_count_zero h0)]
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
    obtain ⟨t', ht', p, hIH⟩ := ihn (fs ++ false :: rest) h0' (markFirst dus) a b
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
      omega, p, ?_⟩
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
    simp only [List.length_append, List.length_cons]


/-- Exact tape left by the uniform lookup, including the unchanged suffix. -/
theorem lookup_tape (dus : List (Bool × Bool)) (aus : List Bool)
    (a b : Bool) (suffix : List Bool) :
    ∃ t ≤ (aus.length + 2) * (3 * dus.length + 2 * aus.length + 20) + 3 * dus.length + 10,
      ∃ p, run dIndexM t
        (init dIndexM (flatU dus ++ false :: a :: b :: (flat2 aus ++ false :: suffix))) =
        ⟨(14, ansOf (markFirst^[aus.count true] dus)), p,
          flatU (markFirst^[aus.count true] dus) ++ false :: a :: b ::
            (flat2 (List.replicate aus.length false) ++ false :: suffix)⟩ := by
  have first (aus : List Bool) :
      run dIndexM (3 * dus.length + 3)
        (init dIndexM (flatU dus ++ false :: a :: b :: (flat2 aus ++ false :: suffix))) =
        ⟨(8, false), (flatU dus ++ [false, a, b]).length,
          (flatU dus ++ [false, a, b]) ++ (flat2 aus ++ false :: suffix)⟩ := by
    have hw := walkA dus [] (false :: a :: b :: (flat2 aus ++ false :: suffix)) false
    simp only [List.length_nil, List.nil_append, Nat.zero_add] at hw
    change run dIndexM (3 * dus.length + 3)
      ⟨(0, false), 0, flatU dus ++ false :: a :: b :: (flat2 aus ++ false :: suffix)⟩ = _
    rw [run_add, hw, crossAt (Or.inl rfl) _ _ false (by
      rw [← flatU_length dus]
      exact getD_at _ false _)]
    simp only [List.length_append, List.length_cons, List.length_nil, flatU_length,
      List.append_assoc, List.cons_append, List.nil_append]
  cases hcount : aus.count true with
  | zero =>
      have hall := all_false_of_count_zero hcount
      obtain ⟨tb, htb, hb⟩ := bPhase aus (flatU dus ++ [false, a, b])
        (false :: suffix) false hall (Or.inr (Or.inr ⟨suffix, rfl⟩))
      obtain ⟨td, htd, p, hd⟩ := dPhase_tape dus []
        (false :: a :: b :: (flat2 aus ++ false :: suffix)) false
        (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
      refine ⟨3 * dus.length + 3 + tb + td, by nlinarith, p, ?_⟩
      rw [run_add, run_add, first, hb]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_nil] at hd ⊢
      rw [hd, Function.iterate_zero_apply]
      rw [← List.eq_replicate_length.mpr hall]
  | succ n =>
      obtain ⟨fs, rest, rfl, hfs⟩ := exists_first_true aus (by omega)
      have hfs0 : fs.count true = 0 := List.count_eq_zero.mpr (fun hmem => by
        have := hfs true hmem
        simp at this)
      have hc : (fs ++ false :: rest).count true = n := by
        simp only [List.count_append, List.count_cons_self, hfs0] at hcount
        simp only [List.count_append, List.count_cons_of_ne (show false ≠ true by decide), hfs0]
        omega
      obtain ⟨tg, htg, p, hg⟩ := grand_tape n (fs ++ false :: rest) hc dus a b
        (false :: suffix) (Or.inr (Or.inr ⟨suffix, rfl⟩)) false
      have hw := walkB fs (flatU dus ++ [false, a, b])
        (true :: true :: (flat2 rest ++ false :: suffix)) false hfs
      have hcons := consumeB ((flatU dus ++ [false, a, b]) ++ flat2 fs)
        (flat2 rest ++ false :: suffix) false
      refine ⟨3 * dus.length + 3 + 2 * fs.length + 2 + tg, ?_, p, ?_⟩
      · have hn := List.count_le_length (l := fs ++ true :: rest) (a := true)
        rw [hcount] at hn
        simp only [List.length_append, List.length_cons] at htg hn ⊢
        nlinarith
      · rw [run_add, run_add, run_add, first]
        rw [show (flatU dus ++ [false, a, b]) ++
          (flat2 (fs ++ true :: rest) ++ false :: suffix) =
          (flatU dus ++ [false, a, b]) ++
            (flat2 fs ++ true :: true :: (flat2 rest ++ false :: suffix)) by
          simp [flat2_append, flat2]]
        rw [hw]
        rw [show (flatU dus ++ [false, a, b]).length + 2 * fs.length =
          ((flatU dus ++ [false, a, b]) ++ flat2 fs).length by
            simp only [List.length_append, List.length_cons, List.length_nil, flat2_length]]
        rw [show (flatU dus ++ [false, a, b]) ++
          (flat2 fs ++ true :: true :: (flat2 rest ++ false :: suffix)) =
          ((flatU dus ++ [false, a, b]) ++ flat2 fs) ++
            true :: true :: (flat2 rest ++ false :: suffix) by simp]
        rw [hcons]
        rw [show ((flatU dus ++ [false, a, b]) ++ flat2 fs) ++
          true :: false :: (flat2 rest ++ false :: suffix) =
          flatU dus ++ false :: a :: b :: (flat2 (fs ++ false :: rest) ++ false :: suffix) by
            simp [flat2_append, flat2]]
        rw [hg]
        simp only [List.length_append, List.length_cons]

/-- Restore only bookkeeping cells and return the head to zero. -/
def restoreM : Machine where
  State := Fin 8 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun st => decide (st.1 = 7)
  δ := fun st bit =>
    if st.1 = 0 then (if bit then ((1, st.2), none, 1) else ((3, st.2), none, 1))
    else if st.1 = 1 then ((2, st.2), some true, 1)
    else if st.1 = 2 then ((0, st.2), none, 1)
    else if st.1 = 3 then ((4, st.2), none, 1)
    else if st.1 = 4 then ((5, st.2), none, 1)
    else if st.1 = 5 then (if bit then ((6, st.2), none, 1) else ((7, st.2), none, 3))
    else if st.1 = 6 then ((5, st.2), some true, 1)
    else ((7, st.2), none, 2)
  accept := fun st => st.2

private theorem restore_step0_T {ans : Bool} {p : ℕ} {x : List Bool}
    (h : x.getD p false = true) :
    step restoreM ⟨(0, ans), p, x⟩ = ⟨(1, ans), p + 1, x⟩ := by
  simp only [step, restoreM, h, moveHead]; rfl
private theorem restore_step0_F {ans : Bool} {p : ℕ} {x : List Bool}
    (h : x.getD p false = false) :
    step restoreM ⟨(0, ans), p, x⟩ = ⟨(3, ans), p + 1, x⟩ := by
  simp only [step, restoreM, h, moveHead]; rfl
private theorem restore_step1 (ans : Bool) (p : ℕ) (x : List Bool) :
    step restoreM ⟨(1, ans), p, x⟩ = ⟨(2, ans), p + 1, writeAt x p true⟩ := by
  simp only [step, restoreM, moveHead]; rfl
private theorem restore_step2 (ans : Bool) (p : ℕ) (x : List Bool) :
    step restoreM ⟨(2, ans), p, x⟩ = ⟨(0, ans), p + 1, x⟩ := by
  simp only [step, restoreM, moveHead]; rfl
private theorem restore_step3 (ans : Bool) (p : ℕ) (x : List Bool) :
    step restoreM ⟨(3, ans), p, x⟩ = ⟨(4, ans), p + 1, x⟩ := by
  simp only [step, restoreM, moveHead]; rfl
private theorem restore_step4 (ans : Bool) (p : ℕ) (x : List Bool) :
    step restoreM ⟨(4, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, restoreM, moveHead]; rfl
private theorem restore_step5_T {ans : Bool} {p : ℕ} {x : List Bool}
    (h : x.getD p false = true) :
    step restoreM ⟨(5, ans), p, x⟩ = ⟨(6, ans), p + 1, x⟩ := by
  simp only [step, restoreM, h, moveHead]; rfl
private theorem restore_step5_F {ans : Bool} {p : ℕ} {x : List Bool}
    (h : x.getD p false = false) :
    step restoreM ⟨(5, ans), p, x⟩ = ⟨(7, ans), 0, x⟩ := by
  simp only [step, restoreM, h, moveHead]; rfl
private theorem restore_step6 (ans : Bool) (p : ℕ) (x : List Bool) :
    step restoreM ⟨(6, ans), p, x⟩ = ⟨(5, ans), p + 1, writeAt x p true⟩ := by
  simp only [step, restoreM, moveHead]; rfl

def unmark (us : List (Bool × Bool)) : List (Bool × Bool) :=
  us.map fun u => (true, u.2)

@[simp] theorem unmark_length (us : List (Bool × Bool)) : (unmark us).length = us.length := by
  simp [unmark]

/-- Restore the data markers without changing payloads or any surrounding bits. -/
theorem restore_data (us : List (Bool × Bool)) (pre suf : List Bool) (ans : Bool) :
    run restoreM (3 * us.length) ⟨(0, ans), pre.length, pre ++ (flatU us ++ suf)⟩ =
      ⟨(0, ans), pre.length + 3 * us.length, pre ++ (flatU (unmark us) ++ suf)⟩ := by
  induction us generalizing pre with
  | nil => simp [flatU, unmark]
  | cons u us ih =>
      obtain ⟨m, d⟩ := u
      change run restoreM (3 * (us.length + 1))
        ⟨(0, ans), pre.length, pre ++ (true :: m :: d :: (flatU us ++ suf))⟩ =
        ⟨(0, ans), pre.length + 3 * (us.length + 1),
          pre ++ (true :: true :: d :: (flatU (unmark us) ++ suf))⟩
      rw [show 3 * (us.length + 1) = 3 + 3 * us.length by omega,
        run_add, run_three, restore_step0_T (getD_at pre true _)]
      rw [show pre.length + 1 = (pre ++ [true]).length by simp,
        show pre ++ (true :: m :: d :: (flatU us ++ suf)) =
          (pre ++ [true]) ++ m :: d :: (flatU us ++ suf) by simp,
        restore_step1, writeAt_boundary, restore_step2]
      rw [show (pre ++ [true]).length + 1 + 1 = (pre ++ [true, true, d]).length by simp,
        show (pre ++ [true]) ++ true :: d :: (flatU us ++ suf) =
          (pre ++ [true, true, d]) ++ (flatU us ++ suf) by simp,
        ih]
      simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
        List.cons_append, List.nil_append]
      congr 1
      omega

/-- Restore unary address markers; the terminator and suffix are untouched. -/
theorem restore_address (aus : List Bool) (pre suf : List Bool) (ans : Bool) :
    run restoreM (2 * aus.length) ⟨(5, ans), pre.length, pre ++ (flat2 aus ++ suf)⟩ =
      ⟨(5, ans), pre.length + 2 * aus.length,
        pre ++ (flat2 (List.replicate aus.length true) ++ suf)⟩ := by
  induction aus generalizing pre with
  | nil => simp [flat2]
  | cons bit aus ih =>
      change run restoreM (2 * (aus.length + 1))
        ⟨(5, ans), pre.length, pre ++ (true :: bit :: (flat2 aus ++ suf))⟩ =
        ⟨(5, ans), pre.length + 2 * (aus.length + 1),
          pre ++ (flat2 (List.replicate (aus.length + 1) true) ++ suf)⟩
      rw [show 2 * (aus.length + 1) = 2 + 2 * aus.length by omega,
        run_add, run_two, restore_step5_T (getD_at pre true _),
        show pre.length + 1 = (pre ++ [true]).length by simp,
        show pre ++ (true :: bit :: (flat2 aus ++ suf)) =
          (pre ++ [true]) ++ bit :: (flat2 aus ++ suf) by simp,
        restore_step6, writeAt_boundary]
      rw [show (pre ++ [true]).length + 1 = (pre ++ [true, true]).length by simp,
        show (pre ++ [true]) ++ true :: (flat2 aus ++ suf) =
          (pre ++ [true, true]) ++ (flat2 aus ++ suf) by simp,
        ih]
      simp only [List.replicate_succ, flat2, List.length_append, List.length_cons,
        List.length_nil, List.append_assoc, List.cons_append, List.nil_append]
      congr 1
      omega

/-- One complete restoration pass preserves its answer bit and all workspace. -/
theorem restore_frame (us : List (Bool × Bool)) (aus : List Bool)
    (a b : Bool) (suffix : List Bool) (ans : Bool) :
    run restoreM (3 * us.length + 3 + 2 * aus.length + 1)
      ⟨(0, ans), 0, flatU us ++ false :: a :: b :: (flat2 aus ++ false :: suffix)⟩ =
      ⟨(7, ans), 0,
        flatU (unmark us) ++ false :: a :: b ::
          (flat2 (List.replicate aus.length true) ++ false :: suffix)⟩ := by
  have hd := restore_data us [] (false :: a :: b :: (flat2 aus ++ false :: suffix)) ans
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hd
  rw [run_add, run_add, run_add, hd, run_three]
  rw [show 3 * us.length = (flatU (unmark us)).length by simp [flatU_length],
    restore_step0_F (getD_at _ false _), restore_step3, restore_step4]
  rw [show (flatU (unmark us)).length + 1 + 1 + 1 =
      (flatU (unmark us) ++ [false, a, b]).length by simp,
    show flatU (unmark us) ++ false :: a :: b :: (flat2 aus ++ false :: suffix) =
      (flatU (unmark us) ++ [false, a, b]) ++ (flat2 aus ++ false :: suffix) by simp,
    restore_address]
  rw [show (flatU (unmark us) ++ [false, a, b]).length + 2 * aus.length =
      ((flatU (unmark us) ++ [false, a, b]) ++
        flat2 (List.replicate aus.length true)).length by
        simp only [List.length_append, List.length_cons, List.length_nil, flat2_length,
          List.length_replicate],
    show (flatU (unmark us) ++ [false, a, b]) ++
      (flat2 (List.replicate aus.length true) ++ false :: suffix) =
      ((flatU (unmark us) ++ [false, a, b]) ++ flat2 (List.replicate aus.length true)) ++
        false :: suffix by simp,
    run_one, restore_step5_F (getD_at _ false _)]
  simp

/-- A single fixed finite-control machine: lookup, retain its answer, reset,
restore both frames, and halt at the origin. -/
def readM : Machine where
  State := dIndexM.State ⊕ restoreM.State
  fin := inferInstance
  dec := inferInstance
  start := .inl dIndexM.start
  halt := fun st => match st with | .inl _ => false | .inr st => restoreM.halt st
  δ := fun st bit => match st with
    | .inl st =>
        if dIndexM.halt st then (.inr (0, st.2), none, 3)
        else let next := dIndexM.δ st bit; (.inl next.1, next.2.1, next.2.2)
    | .inr st =>
        let next := restoreM.δ st bit
        (.inr next.1, next.2.1, next.2.2)
  accept := fun st => match st with | .inl _ => false | .inr st => st.2

theorem readM_state_card : Fintype.card readM.State = 46 := by
  change Fintype.card ((Fin 15 × Bool) ⊕ (Fin 8 × Bool)) = 46
  simp

def embedLookup (c : Cfg dIndexM) : Cfg readM := ⟨.inl c.st, c.hd, c.tp⟩
def embedRestore (c : Cfg restoreM) : Cfg readM := ⟨.inr c.st, c.hd, c.tp⟩

private theorem lookup_step (c : Cfg dIndexM) (h : dIndexM.halt c.st = false) :
    step readM (embedLookup c) = embedLookup (step dIndexM c) := by
  simp only [step, readM, embedLookup, h, Bool.false_eq_true, ↓reduceIte]

private theorem lookup_phase (word : List Bool) (t : ℕ)
    (hmin : ∀ u < t, dIndexM.halt (run dIndexM u (init dIndexM word)).st = false) :
    run readM t (init readM word) = embedLookup (run dIndexM t (init dIndexM word)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun u hu => hmin u (by omega)),
        lookup_step _ (hmin t (by omega)), ← run_succ]

private theorem lookup_switch (ans : Bool) (p : ℕ) (word : List Bool) :
    step readM (embedLookup ⟨(14, ans), p, word⟩) =
      embedRestore ⟨(0, ans), 0, word⟩ := by
  simp only [step, readM, embedLookup, embedRestore, dIndexM, moveHead]
  rfl

private theorem restore_step (c : Cfg restoreM) :
    step readM (embedRestore c) = embedRestore (step restoreM c) := by
  simp only [step, readM, embedRestore]
  by_cases h : restoreM.halt c.st = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h]

private theorem restore_phase (c : Cfg restoreM) (t : ℕ) :
    run readM t (embedRestore c) = embedRestore (run restoreM t c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, restore_step, ← run_succ]

def dataUnits (bits : List Bool) : List (Bool × Bool) := bits.map fun bit => (true, bit)

/-- Data triples, a three-bit separator, a unary address, then an explicit
terminator. Everything after that terminator is preserved workspace. -/
def frame (bits : List Bool) (address : ℕ) (suffix : List Bool) : List Bool :=
  flatU (dataUnits bits) ++ false :: false :: false ::
    (flat2 (List.replicate address true) ++ false :: suffix)

theorem frame_length (bits : List Bool) (address : ℕ) (suffix : List Bool) :
    (frame bits address suffix).length = 3 * bits.length + 2 * address + 4 + suffix.length := by
  simp only [frame, List.length_append, flatU_length, dataUnits, List.length_map,
    List.length_cons, flat2_length, List.length_replicate]
  omega

@[simp] theorem unmark_markFirst (us : List (Bool × Bool)) :
    unmark (markFirst us) = unmark us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      rcases u with ⟨m, d⟩
      cases m <;> simp [markFirst, unmark] at ih ⊢
      exact ih

@[simp] theorem unmark_iter (j : ℕ) (us : List (Bool × Bool)) :
    unmark (markFirst^[j] us) = unmark us := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', unmark_markFirst, ih]

@[simp] theorem markFirst_iter_length (j : ℕ) (us : List (Bool × Bool)) :
    (markFirst^[j] us).length = us.length := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', markFirst_length, ih]

@[simp] theorem unmark_dataUnits (bits : List Bool) : unmark (dataUnits bits) = dataUnits bits := by
  simp [unmark, dataUnits, List.map_map, Function.comp_def]

@[simp] theorem liveDataU_dataUnits (bits : List Bool) : liveDataU (dataUnits bits) = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp only [dataUnits, List.map_cons, liveDataU] at ih ⊢; rw [ih]

/-- This bound is on genuine local-machine transitions, including every
lookup pass, mark write, reset and restoring pass. -/
def readBound (N j : ℕ) : ℕ :=
  (j + 2) * (3 * N + 2 * j + 20) + 6 * N + 2 * j + 15

theorem readM_halts_exact (bits : List Bool) (address : ℕ) (suffix : List Bool) :
    ∃ t ≤ readBound bits.length address,
      run readM t (init readM (frame bits address suffix)) =
        ⟨.inr (7, bits.getD address false), 0, frame bits address suffix⟩ := by
  let word := frame bits address suffix
  let marked := flatU (markFirst^[address] (dataUnits bits)) ++ false :: false :: false ::
    (flat2 (List.replicate address false) ++ false :: suffix)
  obtain ⟨t, ht, p, hlook⟩ := lookup_tape (dataUnits bits)
    (List.replicate address true) false false suffix
  simp only [List.length_replicate, List.count_replicate_self, ansOf_iter,
    liveDataU_dataUnits] at hlook
  change run dIndexM t (init dIndexM word) = ⟨(14, bits.getD address false), p, marked⟩ at hlook
  have hhalt : dIndexM.halt (run dIndexM t (init dIndexM word)).st = true := by
    rw [hlook]
    rfl
  have hex : ∃ u, dIndexM.halt (run dIndexM u (init dIndexM word)).st = true := ⟨t, hhalt⟩
  let t₀ := Nat.find hex
  have ht₀ : t₀ ≤ t := Nat.find_le hhalt
  have halt₀ : dIndexM.halt (run dIndexM t₀ (init dIndexM word)).st = true := Nat.find_spec hex
  have hmin : ∀ u < t₀, dIndexM.halt (run dIndexM u (init dIndexM word)).st = false :=
    fun u hu => by simpa only [Bool.not_eq_true] using Nat.find_min hex hu
  have hlook₀ : run dIndexM t₀ (init dIndexM word) =
      ⟨(14, bits.getD address false), p, marked⟩ :=
    (run_stable dIndexM word ht₀ halt₀).symm.trans hlook
  have hswitch : run readM (t₀ + 1) (init readM word) =
      embedRestore ⟨(0, bits.getD address false), 0, marked⟩ := by
    rw [run_succ, lookup_phase word t₀ hmin, hlook₀, lookup_switch]
  have hrestore := restore_frame (markFirst^[address] (dataUnits bits))
    (List.replicate address false) false false suffix (bits.getD address false)
  simp only [markFirst_iter_length, List.length_replicate,
    unmark_iter, unmark_dataUnits] at hrestore
  simp only [dataUnits, List.length_map] at hrestore
  have hrestore' : run restoreM (3 * bits.length + 3 + 2 * address + 1)
      ⟨(0, bits.getD address false), 0, marked⟩ =
      ⟨(7, bits.getD address false), 0, word⟩ := by
    simpa only [word, frame, marked, dataUnits] using hrestore
  refine ⟨t₀ + 1 + (3 * bits.length + 3 + 2 * address + 1), ?_, ?_⟩
  · simp only [dataUnits, List.length_map, List.length_replicate] at ht
    unfold readBound
    omega
  · rw [run_add, hswitch, restore_phase, hrestore']
    rfl

/-- A polynomial clock in the actual physical framed input length. -/
def readClock (L : ℕ) : ℕ := 100 * (L + 1) ^ 2

theorem readBound_le_readClock (bits : List Bool) (address : ℕ) (suffix : List Bool) :
    readBound bits.length address ≤ readClock (frame bits address suffix).length := by
  let L := (frame bits address suffix).length
  have hL : L = 3 * bits.length + 2 * address + 4 + suffix.length := frame_length _ _ _
  have hN : bits.length ≤ L := by omega
  have hj : address ≤ L := by omega
  have hp : (address + 2) * (3 * bits.length + 2 * address + 20) ≤
      40 * (L + 1) ^ 2 := by
    calc
      _ ≤ (2 * (L + 1)) * (20 * (L + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hs : L + 1 ≤ (L + 1) ^ 2 := by nlinarith [Nat.zero_le (L * L)]
  have ht : 6 * bits.length + 2 * address + 15 ≤ 15 * (L + 1) ^ 2 := by omega
  change (address + 2) * (3 * bits.length + 2 * address + 20) +
    6 * bits.length + 2 * address + 15 ≤ 100 * (L + 1) ^ 2
  omega

theorem readClock_poly :
    PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant.PolyBounded readClock :=
  ⟨100, 2, fun _ => le_rfl⟩

/-- Exact preserved tape and reset head at the polynomial clock; an
out-of-range address returns false, as the wire-store evaluator requires. -/
theorem readM_run (bits : List Bool) (address : ℕ) (suffix : List Bool) :
    run readM (readClock (frame bits address suffix).length)
      (init readM (frame bits address suffix)) =
      ⟨.inr (7, bits.getD address false), 0, frame bits address suffix⟩ := by
  obtain ⟨t, ht, hr⟩ := readM_halts_exact bits address suffix
  have hhalt : readM.halt (run readM t (init readM (frame bits address suffix))).st = true := by
    rw [hr]
    rfl
  rw [run_stable readM _ (ht.trans (readBound_le_readClock _ _ _)) hhalt, hr]

/-- The input's data, unary address, framing bits and arbitrary suffix all
survive lookup. The answer is carried in finite control for a caller branch. -/
theorem readM_correct (bits : List Bool) (address : ℕ) (suffix : List Bool) :
    HaltsBy readM (frame bits address suffix) (readClock (frame bits address suffix).length) ∧
    decideOut readM (frame bits address suffix) (readClock (frame bits address suffix).length) =
      bits.getD address false ∧
    transOut readM (frame bits address suffix) (readClock (frame bits address suffix).length) =
      frame bits address suffix ∧
    (run readM (readClock (frame bits address suffix).length)
      (init readM (frame bits address suffix))).hd = 0 := by
  unfold HaltsBy decideOut transOut
  rw [readM_run]
  exact ⟨rfl, rfl, rfl, rfl⟩

end GodMoveMarkedReadMachine

#print axioms GodMoveMarkedReadMachine.grand_tape
#print axioms GodMoveMarkedReadMachine.lookup_tape
#print axioms GodMoveMarkedReadMachine.restore_frame
#print axioms GodMoveMarkedReadMachine.readM_state_card
#print axioms GodMoveMarkedReadMachine.readM_halts_exact
#print axioms GodMoveMarkedReadMachine.readBound_le_readClock
#print axioms GodMoveMarkedReadMachine.readClock_poly
#print axioms GodMoveMarkedReadMachine.readM_run
#print axioms GodMoveMarkedReadMachine.readM_correct
