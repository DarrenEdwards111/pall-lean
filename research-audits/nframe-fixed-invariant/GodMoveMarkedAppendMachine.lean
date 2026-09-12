import GodMoveMarkedReadMachine

/-!
# Appending to the restoring lookup's actual store codec

A fixed finite-control machine appends one bit to the DIndex data frame by
shifting its self-delimited unary address through a three-bit carry. It consumes
three reserved cells after the address terminator and preserves all subsequent
workspace at its original physical positions. No end-of-unmarked-tape test or
space-allocation certificate is assumed. Repeated use requires a supplied pool
of reserved cells; allocating or growing that pool is a separate operation.
-/

namespace GodMoveMarkedAppendMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine
open GodMoveMarkedReadMachine

abbrev AppendState := Fin 11 × Bool × Bool × Bool

/-- The bit parameter selects two fixed transition tables, independent of all
input lengths and addresses. -/
def appendM (bit : Bool) : Machine where
  State := AppendState
  fin := inferInstance
  dec := inferInstance
  start := (0, false, false, false)
  halt := fun st => decide (st.1 = 10)
  δ := fun st old =>
    if st.1 = 0 then
      (if old then ((1, st.2.1, st.2.2.1, st.2.2.2), none, 1)
       else ((3, false, false, false), some true, 1))
    else if st.1 = 1 then ((2, st.2.1, st.2.2.1, st.2.2.2), none, 1)
    else if st.1 = 2 then ((0, st.2.1, st.2.2.1, st.2.2.2), none, 1)
    else if st.1 = 3 then ((4, false, false, false), some true, 1)
    else if st.1 = 4 then ((5, false, false, false), some bit, 1)
    else if st.1 = 5 then
      (if old then ((6, st.2.2.1, st.2.2.2, true), some st.2.1, 1)
       else ((7, st.2.2.1, st.2.2.2, false), some st.2.1, 1))
    else if st.1 = 6 then ((5, st.2.2.1, st.2.2.2, old), some st.2.1, 1)
    else if st.1 = 7 then ((8, st.2.1, st.2.2.1, st.2.2.2), some st.2.1, 1)
    else if st.1 = 8 then ((9, st.2.1, st.2.2.1, st.2.2.2), some st.2.2.1, 1)
    else if st.1 = 9 then ((10, false, false, false), some st.2.2.2, 3)
    else ((10, false, false, false), none, 2)
  accept := fun _ => bit

theorem appendM_state_card (bit : Bool) : Fintype.card (appendM bit).State = 88 := by
  change Fintype.card (Fin 11 × Bool × Bool × Bool) = 88
  simp

private theorem step_scan0 (bit a b c : Bool) (p : ℕ) (x : List Bool)
    (h : x.getD p false = true) :
    step (appendM bit) ⟨(0,a,b,c),p,x⟩ = ⟨(1,a,b,c),p+1,x⟩ := by
  simp only [step, appendM, h, moveHead]; rfl
private theorem step_scan1 (bit a b c : Bool) (p : ℕ) (x : List Bool) :
    step (appendM bit) ⟨(1,a,b,c),p,x⟩ = ⟨(2,a,b,c),p+1,x⟩ := by
  simp only [step, appendM, moveHead]; rfl
private theorem step_scan2 (bit a b c : Bool) (p : ℕ) (x : List Bool) :
    step (appendM bit) ⟨(2,a,b,c),p,x⟩ = ⟨(0,a,b,c),p+1,x⟩ := by
  simp only [step, appendM, moveHead]; rfl
private theorem step_begin (bit a b c : Bool) (p : ℕ) (x : List Bool)
    (h : x.getD p false = false) :
    step (appendM bit) ⟨(0,a,b,c),p,x⟩ =
      ⟨(3,false,false,false),p+1,writeAt x p true⟩ := by
  simp only [step, appendM, h, moveHead]; rfl
private theorem step_newmark (bit : Bool) (p : ℕ) (x : List Bool) :
    step (appendM bit) ⟨(3,false,false,false),p,x⟩ =
      ⟨(4,false,false,false),p+1,writeAt x p true⟩ := by
  simp only [step, appendM, moveHead]; rfl
private theorem step_newbit (bit : Bool) (p : ℕ) (x : List Bool) :
    step (appendM bit) ⟨(4,false,false,false),p,x⟩ =
      ⟨(5,false,false,false),p+1,writeAt x p bit⟩ := by
  simp only [step, appendM, moveHead]; rfl
private theorem step_addr0_T (bit a b c : Bool) (p : ℕ) (x : List Bool)
    (h : x.getD p false = true) :
    step (appendM bit) ⟨(5,a,b,c),p,x⟩ = ⟨(6,b,c,true),p+1,writeAt x p a⟩ := by
  simp only [step, appendM, h, moveHead]; rfl
private theorem step_addr0_F (bit a b c : Bool) (p : ℕ) (x : List Bool)
    (h : x.getD p false = false) :
    step (appendM bit) ⟨(5,a,b,c),p,x⟩ = ⟨(7,b,c,false),p+1,writeAt x p a⟩ := by
  simp only [step, appendM, h, moveHead]; rfl
private theorem step_addr1_T (bit a b c : Bool) (p : ℕ) (x : List Bool)
    (h : x.getD p false = true) :
    step (appendM bit) ⟨(6,a,b,c),p,x⟩ = ⟨(5,b,c,true),p+1,writeAt x p a⟩ := by
  simp only [step, appendM, h, moveHead]; rfl
private theorem step_flush0 (bit a b c : Bool) (p : ℕ) (x : List Bool) :
    step (appendM bit) ⟨(7,a,b,c),p,x⟩ = ⟨(8,a,b,c),p+1,writeAt x p a⟩ := by
  simp only [step, appendM, moveHead]; rfl
private theorem step_flush1 (bit a b c : Bool) (p : ℕ) (x : List Bool) :
    step (appendM bit) ⟨(8,a,b,c),p,x⟩ = ⟨(9,a,b,c),p+1,writeAt x p b⟩ := by
  simp only [step, appendM, moveHead]; rfl
private theorem step_flush2 (bit a b c : Bool) (p : ℕ) (x : List Bool) :
    step (appendM bit) ⟨(9,a,b,c),p,x⟩ = ⟨(10,false,false,false),0,writeAt x p c⟩ := by
  simp only [step, appendM, moveHead]; rfl

/-- Traverse data units without modifying any cell. -/
theorem scan_data (bit : Bool) (us : List (Bool × Bool)) (pre suf : List Bool) :
    run (appendM bit) (3 * us.length)
      ⟨(0,false,false,false),pre.length,pre ++ (flatU us ++ suf)⟩ =
      ⟨(0,false,false,false),pre.length + 3 * us.length,pre ++ (flatU us ++ suf)⟩ := by
  induction us generalizing pre with
  | nil => simp [flatU]
  | cons u us ih =>
      rcases u with ⟨m,d⟩
      change run (appendM bit) (3 * (us.length + 1))
        ⟨(0,false,false,false),pre.length,pre ++ true :: m :: d :: (flatU us ++ suf)⟩ =
        ⟨(0,false,false,false),pre.length + 3 * (us.length + 1),
          pre ++ true :: m :: d :: (flatU us ++ suf)⟩
      rw [show 3 * (us.length + 1) = 3 + 3 * us.length by omega,
        run_add, run_three, step_scan0 _ _ _ _ _ _ (getD_at pre true _), step_scan1, step_scan2]
      rw [show pre.length + 1 + 1 + 1 = (pre ++ [true,m,d]).length by simp,
        show pre ++ true :: m :: d :: (flatU us ++ suf) =
          (pre ++ [true,m,d]) ++ (flatU us ++ suf) by simp,
        ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      congr 1
      omega

/-- The old three-bit separator becomes the appended data unit. Its zeros
are retained as the shift's initial carry. -/
theorem begin_append (bit : Bool) (pre rest : List Bool) :
    run (appendM bit) 3
      ⟨(0,false,false,false),pre.length,pre ++ false :: false :: false :: rest⟩ =
      ⟨(5,false,false,false),(pre ++ [true,true,bit]).length,
        (pre ++ [true,true,bit]) ++ rest⟩ := by
  rw [run_three, step_begin _ _ _ _ _ _ (getD_at pre false _), writeAt_boundary]
  rw [show pre.length + 1 = (pre ++ [true]).length by simp,
    show pre ++ true :: false :: false :: rest = (pre ++ [true]) ++ false :: false :: rest by simp,
    step_newmark, writeAt_boundary]
  rw [show (pre ++ [true]).length + 1 = (pre ++ [true,true]).length by simp,
    show (pre ++ [true]) ++ true :: false :: rest =
      (pre ++ [true,true]) ++ false :: rest by simp,
    step_newbit, writeAt_boundary]
  simp

/-- Flush the three carried bits into the explicitly reserved cells. -/
theorem flush_carry (bit a b c p₀ p₁ p₂ : Bool) (pre suffix : List Bool) :
    run (appendM bit) 3 ⟨(7,a,b,c),pre.length,pre ++ p₀ :: p₁ :: p₂ :: suffix⟩ =
      ⟨(10,false,false,false),0,pre ++ a :: b :: c :: suffix⟩ := by
  rw [run_three, step_flush0, writeAt_boundary]
  rw [show pre.length + 1 = (pre ++ [a]).length by simp,
    show pre ++ a :: p₁ :: p₂ :: suffix = (pre ++ [a]) ++ p₁ :: p₂ :: suffix by simp,
    step_flush1, writeAt_boundary]
  rw [show (pre ++ [a]).length + 1 = (pre ++ [a,b]).length by simp,
    show (pre ++ [a]) ++ b :: p₂ :: suffix = (pre ++ [a,b]) ++ p₂ :: suffix by simp,
    step_flush2, writeAt_boundary]
  simp

/-- Shift the complete unary address and its terminator through a finite
three-bit carry. The workspace suffix is never inspected or overwritten. -/
theorem shift_address (bit : Bool) (j : ℕ) (a b c p₀ p₁ p₂ : Bool)
    (pre suffix : List Bool) :
    run (appendM bit) (2 * j + 4)
      ⟨(5,a,b,c),pre.length,
        pre ++ (flat2 (List.replicate j true) ++ false :: p₀ :: p₁ :: p₂ :: suffix)⟩ =
      ⟨(10,false,false,false),0,
        pre ++ a :: b :: c :: (flat2 (List.replicate j true) ++ false :: suffix)⟩ := by
  induction j generalizing a b c pre with
  | zero =>
      change run (appendM bit) 4 ⟨(5,a,b,c),pre.length,pre ++ false :: p₀ :: p₁ :: p₂ :: suffix⟩ =
        ⟨(10,false,false,false),0,pre ++ a :: b :: c :: false :: suffix⟩
      rw [show (4 : ℕ) = 1 + 3 by rfl, run_add, run_one,
        step_addr0_F _ _ _ _ _ _ (getD_at pre false _), writeAt_boundary]
      rw [show pre.length + 1 = (pre ++ [a]).length by simp,
        show pre ++ a :: p₀ :: p₁ :: p₂ :: suffix =
          (pre ++ [a]) ++ p₀ :: p₁ :: p₂ :: suffix by simp,
        flush_carry]
      simp
  | succ j ih =>
      change run (appendM bit) (2 * (j + 1) + 4)
        ⟨(5,a,b,c),pre.length,
          pre ++ true :: true :: (flat2 (List.replicate j true) ++ false :: p₀ :: p₁ :: p₂ :: suffix)⟩ =
        ⟨(10,false,false,false),0,
          pre ++ a :: b :: c :: true :: true :: (flat2 (List.replicate j true) ++ false :: suffix)⟩
      rw [show 2 * (j + 1) + 4 = 2 + (2 * j + 4) by omega,
        run_add, run_two, step_addr0_T _ _ _ _ _ _ (getD_at pre true _), writeAt_boundary]
      rw [show pre.length + 1 = (pre ++ [a]).length by simp,
        show pre ++ a :: true :: (flat2 (List.replicate j true) ++ false :: p₀ :: p₁ :: p₂ :: suffix) =
          (pre ++ [a]) ++ true :: (flat2 (List.replicate j true) ++ false :: p₀ :: p₁ :: p₂ :: suffix) by simp,
        step_addr1_T _ _ _ _ _ _ (getD_at (pre ++ [a]) true _), writeAt_boundary]
      rw [show (pre ++ [a]).length + 1 = (pre ++ [a,b]).length by simp,
        show (pre ++ [a]) ++ b :: (flat2 (List.replicate j true) ++ false :: p₀ :: p₁ :: p₂ :: suffix) =
          (pre ++ [a,b]) ++ (flat2 (List.replicate j true) ++ false :: p₀ :: p₁ :: p₂ :: suffix) by simp,
        ih]
      simp

private theorem flatU_append (us vs : List (Bool × Bool)) :
    flatU (us ++ vs) = flatU us ++ flatU vs := by
  induction us with
  | nil => rfl
  | cons u us ih => rcases u with ⟨m,d⟩; simp [flatU, ih]

/-- Exact append on the same frame accepted by the restoring reader. The
three reserved cells may contain any bits; their contents are discarded. -/
theorem appendM_run (bit : Bool) (bits : List Bool) (address : ℕ)
    (p₀ p₁ p₂ : Bool) (suffix : List Bool) :
    run (appendM bit) (3 * bits.length + 2 * address + 7)
      (init (appendM bit) (frame bits address (p₀ :: p₁ :: p₂ :: suffix))) =
      ⟨(10,false,false,false),0,frame (bits ++ [bit]) address suffix⟩ := by
  have hs := scan_data bit (dataUnits bits) []
    (false :: false :: false ::
      (flat2 (List.replicate address true) ++ false :: p₀ :: p₁ :: p₂ :: suffix))
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hs
  rw [show 3 * bits.length + 2 * address + 7 =
      3 * (dataUnits bits).length + 3 + (2 * address + 4) by
        simp only [dataUnits, List.length_map]; omega,
    run_add (appendM bit) (3 * (dataUnits bits).length + 3) (2 * address + 4),
    run_add (appendM bit) (3 * (dataUnits bits).length) 3]
  change run (appendM bit) (2 * address + 4)
    (run (appendM bit) 3
      (run (appendM bit) (3 * (dataUnits bits).length)
        ⟨(0,false,false,false),0,
          flatU (dataUnits bits) ++ false :: false :: false ::
            (flat2 (List.replicate address true) ++ false :: p₀ :: p₁ :: p₂ :: suffix)⟩)) = _
  rw [hs, show 3 * (dataUnits bits).length = (flatU (dataUnits bits)).length from
    (flatU_length _).symm, begin_append, shift_address]
  simp only [frame, dataUnits, List.map_append, List.map_cons, List.map_nil, flatU_append,
    flatU, List.append_assoc, List.cons_append, List.nil_append]

/-- The local operation takes no more steps than the physical input length;
it never traverses the arbitrary workspace suffix. -/
theorem appendM_at_input_length (bit : Bool) (bits : List Bool) (address : ℕ)
    (p₀ p₁ p₂ : Bool) (suffix : List Bool) :
    run (appendM bit) (frame bits address (p₀ :: p₁ :: p₂ :: suffix)).length
      (init (appendM bit) (frame bits address (p₀ :: p₁ :: p₂ :: suffix))) =
      ⟨(10,false,false,false),0,frame (bits ++ [bit]) address suffix⟩ := by
  have hr := appendM_run bit bits address p₀ p₁ p₂ suffix
  have hhalt : (appendM bit).halt
      (run (appendM bit) (3 * bits.length + 2 * address + 7)
        (init (appendM bit) (frame bits address (p₀ :: p₁ :: p₂ :: suffix)))).st = true := by
    rw [hr]
    rfl
  rw [run_stable (appendM bit) _ (show 3 * bits.length + 2 * address + 7 ≤
    (frame bits address (p₀ :: p₁ :: p₂ :: suffix)).length by
      rw [frame_length]
      simp only [List.length_cons]
      omega) hhalt, hr]

/-- A reserved zero pool supplies successive append operations. The remaining
pool and workspace form the suffix already allowed by `readM`. -/
theorem appendM_reserved_pool (bit : Bool) (bits : List Bool) (address capacity : ℕ)
    (suffix : List Bool) :
    run (appendM bit) (3 * bits.length + 2 * address + 7)
      (init (appendM bit)
        (frame bits address (List.replicate (3 * (capacity + 1)) false ++ suffix))) =
      ⟨(10,false,false,false),0,
        frame (bits ++ [bit]) address (List.replicate (3 * capacity) false ++ suffix)⟩ := by
  have hp : List.replicate (3 * (capacity + 1)) false ++ suffix =
      false :: false :: false :: (List.replicate (3 * capacity) false ++ suffix) := by
    rw [show 3 * (capacity + 1) = 3 * capacity + 1 + 1 + 1 by omega]
    simp only [List.replicate_succ, List.cons_append]
  rw [hp]
  exact appendM_run bit bits address false false false _

/-- Preservation here is an exact finite-tape statement, not only agreement
of nonblank observations. -/
theorem appendM_correct (bit : Bool) (bits : List Bool) (address : ℕ)
    (p₀ p₁ p₂ : Bool) (suffix : List Bool) :
    HaltsBy (appendM bit) (frame bits address (p₀ :: p₁ :: p₂ :: suffix))
      (frame bits address (p₀ :: p₁ :: p₂ :: suffix)).length ∧
    transOut (appendM bit) (frame bits address (p₀ :: p₁ :: p₂ :: suffix))
      (frame bits address (p₀ :: p₁ :: p₂ :: suffix)).length = frame (bits ++ [bit]) address suffix ∧
    (run (appendM bit) (frame bits address (p₀ :: p₁ :: p₂ :: suffix)).length
      (init (appendM bit) (frame bits address (p₀ :: p₁ :: p₂ :: suffix)))).hd = 0 := by
  unfold HaltsBy transOut
  rw [appendM_at_input_length]
  exact ⟨rfl,rfl,rfl⟩

/-- A single uniform machine reads the selected data bit, restores the frame,
then dispatches in finite control to the corresponding append table. -/
def copyM : Machine where
  State := readM.State ⊕ (Bool × AppendState)
  fin := inferInstance
  dec := inferInstance
  start := .inl readM.start
  halt := fun st => match st with
    | .inl _ => false
    | .inr (bit,st) => (appendM bit).halt st
  δ := fun st old => match st with
    | .inl st =>
        if readM.halt st then
          (.inr (readM.accept st, (appendM (readM.accept st)).start), none, 3)
        else let tr := readM.δ st old; (.inl tr.1, tr.2.1, tr.2.2)
    | .inr (bit,st) =>
        let tr := (appendM bit).δ st old
        (.inr (bit,tr.1), tr.2.1, tr.2.2)
  accept := fun st => match st with | .inl _ => false | .inr (bit,_) => bit

theorem copyM_state_card : Fintype.card copyM.State = 222 := by
  change Fintype.card (readM.State ⊕ (Bool × AppendState)) = 222
  simp [readM_state_card, AppendState]

def embedRead (c : Cfg readM) : Cfg copyM := ⟨.inl c.st,c.hd,c.tp⟩
def embedAppend (bit : Bool) (c : Cfg (appendM bit)) : Cfg copyM :=
  ⟨.inr (bit,c.st),c.hd,c.tp⟩

private theorem copy_step_read (c : Cfg readM) (h : readM.halt c.st = false) :
    step copyM (embedRead c) = embedRead (step readM c) := by
  simp only [step, copyM, embedRead, h, Bool.false_eq_true, ↓reduceIte]

private theorem copy_phase_read (word : List Bool) (t : ℕ)
    (hmin : ∀ u < t, readM.halt (run readM u (init readM word)).st = false) :
    run copyM t (init copyM word) = embedRead (run readM t (init readM word)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun u hu => hmin u (by omega)),
        copy_step_read _ (hmin t (by omega)), ← run_succ]

private theorem copy_switch (bit : Bool) (word : List Bool) :
    step copyM (embedRead ⟨.inr (7,bit),0,word⟩) =
      embedAppend bit (init (appendM bit) word) := by
  rfl

private theorem copy_step_append (bit : Bool) (c : Cfg (appendM bit)) :
    step copyM (embedAppend bit c) = embedAppend bit (step (appendM bit) c) := by
  simp only [step, copyM, embedAppend]
  by_cases h : (appendM bit).halt c.st = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h]

private theorem copy_phase_append (bit : Bool) (c : Cfg (appendM bit)) (t : ℕ) :
    run copyM t (embedAppend bit c) = embedAppend bit (run (appendM bit) t c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, copy_step_append, ← run_succ]

/-- The restoring read bound, one dispatch step, and the linear append bound. -/
def copyClock (L : ℕ) : ℕ := readClock L + L + 1

theorem copyClock_poly :
    PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant.PolyBounded copyClock := by
  refine ⟨101,2,fun L => ?_⟩
  unfold copyClock readClock
  nlinarith [Nat.zero_le (L * L)]

/-- The chosen bit comes from the actual preceding read, not from an externally
supplied denotation. Three reserved cells are consumed and all later workspace
is preserved exactly. -/
theorem copyM_halts_exact (bits : List Bool) (address : ℕ)
    (p₀ p₁ p₂ : Bool) (suffix : List Bool) :
    ∃ t ≤ copyClock (frame bits address (p₀ :: p₁ :: p₂ :: suffix)).length,
      run copyM t (init copyM (frame bits address (p₀ :: p₁ :: p₂ :: suffix))) =
        ⟨.inr (bits.getD address false,(10,false,false,false)),0,
          frame (bits ++ [bits.getD address false]) address suffix⟩ := by
  let word := frame bits address (p₀ :: p₁ :: p₂ :: suffix)
  have hr := readM_run bits address (p₀ :: p₁ :: p₂ :: suffix)
  change run readM (readClock word.length) (init readM word) =
    ⟨.inr (7,bits.getD address false),0,word⟩ at hr
  have hh : readM.halt (run readM (readClock word.length) (init readM word)).st = true := by
    rw [hr]
    rfl
  have hex : ∃ t, readM.halt (run readM t (init readM word)).st = true := ⟨_,hh⟩
  let t₀ := Nat.find hex
  have ht₀ : t₀ ≤ readClock word.length := Nat.find_le hh
  have halt₀ : readM.halt (run readM t₀ (init readM word)).st = true := Nat.find_spec hex
  have hmin : ∀ u < t₀, readM.halt (run readM u (init readM word)).st = false :=
    fun u hu => by simpa only [Bool.not_eq_true] using Nat.find_min hex hu
  have hr₀ : run readM t₀ (init readM word) =
      ⟨.inr (7,bits.getD address false),0,word⟩ :=
    (run_stable readM word ht₀ halt₀).symm.trans hr
  have hswitch : run copyM (t₀ + 1) (init copyM word) =
      embedAppend (bits.getD address false) (init (appendM (bits.getD address false)) word) := by
    rw [run_succ, copy_phase_read word t₀ hmin, hr₀, copy_switch]
  have ha := appendM_at_input_length (bits.getD address false) bits address p₀ p₁ p₂ suffix
  refine ⟨t₀ + 1 + word.length, ?_, ?_⟩
  · change t₀ + 1 + word.length ≤ readClock word.length + word.length + 1
    omega
  · change run copyM (t₀ + 1 + word.length) (init copyM word) = _
    rw [run_add, hswitch, copy_phase_append]
    rw [ha]
    rfl

theorem copyM_run (bits : List Bool) (address : ℕ)
    (p₀ p₁ p₂ : Bool) (suffix : List Bool) :
    run copyM (copyClock (frame bits address (p₀ :: p₁ :: p₂ :: suffix)).length)
      (init copyM (frame bits address (p₀ :: p₁ :: p₂ :: suffix))) =
        ⟨.inr (bits.getD address false,(10,false,false,false)),0,
          frame (bits ++ [bits.getD address false]) address suffix⟩ := by
  obtain ⟨t,ht,hr⟩ := copyM_halts_exact bits address p₀ p₁ p₂ suffix
  have hh : copyM.halt
      (run copyM t (init copyM (frame bits address (p₀ :: p₁ :: p₂ :: suffix)))).st = true := by
    rw [hr]
    rfl
  rw [run_stable copyM _ ht hh,hr]

theorem copyM_reserved_pool (bits : List Bool) (address capacity : ℕ) (suffix : List Bool) :
    run copyM (copyClock
        (frame bits address (List.replicate (3 * (capacity + 1)) false ++ suffix)).length)
      (init copyM (frame bits address (List.replicate (3 * (capacity + 1)) false ++ suffix))) =
        ⟨.inr (bits.getD address false,(10,false,false,false)),0,
          frame (bits ++ [bits.getD address false]) address
            (List.replicate (3 * capacity) false ++ suffix)⟩ := by
  have hp : List.replicate (3 * (capacity + 1)) false ++ suffix =
      false :: false :: false :: (List.replicate (3 * capacity) false ++ suffix) := by
    rw [show 3 * (capacity + 1) = 3 * capacity + 1 + 1 + 1 by omega]
    simp only [List.replicate_succ,List.cons_append]
  rw [hp]
  exact copyM_run bits address false false false _

end GodMoveMarkedAppendMachine

#print axioms GodMoveMarkedAppendMachine.appendM_state_card
#print axioms GodMoveMarkedAppendMachine.begin_append
#print axioms GodMoveMarkedAppendMachine.shift_address
#print axioms GodMoveMarkedAppendMachine.appendM_run
#print axioms GodMoveMarkedAppendMachine.appendM_at_input_length
#print axioms GodMoveMarkedAppendMachine.appendM_reserved_pool
#print axioms GodMoveMarkedAppendMachine.appendM_correct
#print axioms GodMoveMarkedAppendMachine.copyM_state_card
#print axioms GodMoveMarkedAppendMachine.copyClock_poly
#print axioms GodMoveMarkedAppendMachine.copyM_run
#print axioms GodMoveMarkedAppendMachine.copyM_reserved_pool
