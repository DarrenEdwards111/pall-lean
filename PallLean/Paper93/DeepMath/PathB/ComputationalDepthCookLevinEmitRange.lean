import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitLoop

/-!
# Cook–Levin M2 emitter, E4 (ii) — the range-emitter (loop-variable body, in-place counter)

Second brick of E4: the counted loop with a **loop variable**.  `rangeMachine` runs
`for k in range N: splice k; increment k`, emitting `encodeNat 0 · encodeNat 1 · ⋯ · encodeNat (N-1)`
into the doubled output — the block stream of the tableau's loop-shaped (at-least-one) templates.

The new layout element is the **capacity-bounded counter**: the loop variable `j` lives in a fixed-footprint
region `jT N j = 11^j 01 00^(N-j)` (`2N+2` cells for any value `j ≤ N`), so the increment is **in place** —
the four marker-advancing writes land on the `00` padding and no region ever moves.  This is the layout
decision that makes nested loops possible: every work region has a static address.

Three regions: the bound `cntT N k` (countdown-marked, as in E4 (i)), the loop variable `jsT/jhT/jT`
(splice-marked, healed, incremented in place), and the doubled output.  A round marks the bound's pair `k`,
splices `J` (its own marking sub-rounds — mark a `J` pair, seek across two region boundaries to the output
terminator, emit a doubled `true`, reset), emits the closing `false` (`encodeNat k` complete), heals `J`,
increments it in place, and resets; the bound's boundary exits into the restore pass and halt.

All output-region facts, the four-write snoc, the bound-region suite, and the healing descriptor are
**reused** (`preD_*`, `writes_snoc`, `cntT`/`cntE`, `hlT`/`hlE`); new here are the `J`-region descriptors
with their suites, the three structural `J`-writes (mark/heal/**increment-in-place**), and the two-prefix
lifts (`writes_snoc2`, `preD2_*`, `writeAt_append_right`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat encodeNat_length)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice

/-! ## The emitted range -/

/-- `encodeNat 0 · encodeNat 1 · ⋯ · encodeNat (k-1)`. -/
def rangeEnc : ℕ → List Bool
  | 0 => []
  | k + 1 => rangeEnc k ++ encodeNat k

/-- Its bit-length (the triangular sum, kept recursive). -/
def rangeLen : ℕ → ℕ
  | 0 => 0
  | k + 1 => rangeLen k + (k + 1)

theorem rangeEnc_length (k : ℕ) : (rangeEnc k).length = rangeLen k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rangeEnc, rangeLen, List.length_append, ih, encodeNat_length]

theorem rangeLen_le (k : ℕ) : rangeLen k ≤ k * k := by
  induction k with
  | zero => simp [rangeLen]
  | succ k ih => simp only [rangeLen]; nlinarith

/-! ## Two-prefix lifts -/

/-- `writeAt` inside the right part of an append. -/
theorem writeAt_append_right (A X : List Bool) (q p : ℕ) (w : Bool) (hq : A.length = q)
    (hp : p < X.length) :
    writeAt (A ++ X) (q + p) w = A ++ writeAt X p w := by
  rw [writeAt_of_lt w (by rw [List.length_append]; omega), writeAt_of_lt w hp,
    set_append_left_length' A X hq p w]

/-- The four-write snoc under a two-part work prefix. -/
theorem writes_snoc2 (A B out : List Bool) (q : ℕ) (hq : A.length + B.length = q) (b : Bool) :
    writeAt (writeAt (writeAt (writeAt (A ++ (B ++ encodeD out)) (q + 2 * out.length) b)
        (q + 2 * out.length + 1) b) (q + 2 * out.length + 2) false) (q + 2 * out.length + 3) true
      = A ++ (B ++ encodeD (out ++ [b])) := by
  have h := writes_snoc (A ++ B) out q (by rw [List.length_append]; omega) b
  simpa [List.append_assoc] using h

/-- Output data pairs read equal, under a two-part work prefix. -/
theorem preD2_data_eq (A B out : List Bool) (q i : ℕ) (hq : A.length + B.length = q)
    (h : i < out.length) :
    (A ++ (B ++ encodeD out)).getD (q + 2 * i) false
      = (A ++ (B ++ encodeD out)).getD (q + 2 * i + 1) false := by
  have := preD_data_eq (A ++ B) out q i (by rw [List.length_append]; omega) h
  simpa [List.append_assoc] using this

theorem preD2_mark_lo (A B out : List Bool) (q : ℕ) (hq : A.length + B.length = q) :
    (A ++ (B ++ encodeD out)).getD (q + 2 * out.length) false = false := by
  have := preD_mark_lo (A ++ B) out q (by rw [List.length_append]; omega)
  simpa [List.append_assoc] using this

theorem preD2_mark_hi (A B out : List Bool) (q : ℕ) (hq : A.length + B.length = q) :
    (A ++ (B ++ encodeD out)).getD (q + 2 * out.length + 1) false = true := by
  have := preD_mark_hi (A ++ B) out q (by rw [List.length_append]; omega)
  simpa [List.append_assoc] using this

/-! ## The loop-variable region descriptors -/

/-- The capacity-bounded loop variable: value `j`, capacity `N`, fixed footprint `2N+2`. -/
def jT (N j : ℕ) : List Bool :=
  List.replicate (2 * j) true ++ ([false, true] ++ List.replicate (2 * (N - j)) false)

/-- The loop variable mid-splice: value `k`, `j'` pairs splice-marked. -/
def jsT (N k j' : ℕ) : List Bool :=
  markedD j' ++ (List.replicate (2 * (k - j')) true
    ++ ([false, true] ++ List.replicate (2 * (N - k)) false))

/-- The loop variable mid-heal: value `k`, `i` pairs healed. -/
def jhT (N k i : ℕ) : List Bool :=
  List.replicate (2 * i) true ++ (markedD (k - i)
    ++ ([false, true] ++ List.replicate (2 * (N - k)) false))

theorem jsT_zero (N k : ℕ) : jsT N k 0 = jT N k := by
  simp [jsT, jT, markedD]

theorem jhT_zero (N k : ℕ) : jhT N k 0 = jsT N k k := by
  simp [jhT, jsT]

theorem jhT_last (N k : ℕ) : jhT N k k = jT N k := by
  simp [jhT, jT, markedD]

theorem jT_full (N : ℕ) : jT N N = unaryD N := by
  simp [jT, unaryD_eq]

theorem jT_length (N j : ℕ) (hj : j ≤ N) : (jT N j).length = 2 * N + 2 := by
  simp only [jT, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

theorem jsT_length (N k j' : ℕ) (hj : j' ≤ k) (hk : k ≤ N) : (jsT N k j').length = 2 * N + 2 := by
  simp only [jsT, List.length_append, markedD_length, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

theorem jhT_length (N k i : ℕ) (hi : i ≤ k) (hk : k ≤ N) : (jhT N k i).length = 2 * N + 2 := by
  simp only [jhT, List.length_append, markedD_length, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

/-! ### `getD` suites (suffix-generic) -/

theorem jsE_mark_lo (N k j' : ℕ) (E : List Bool) (i : ℕ) (h : i < j') :
    (jsT N k j' ++ E).getD (2 * i) false = true := by
  rw [jsT, List.append_assoc, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo j' i h

theorem jsE_mark_hi (N k j' : ℕ) (E : List Bool) (i : ℕ) (h : i < j') :
    (jsT N k j' ++ E).getD (2 * i + 1) false = false := by
  rw [jsT, List.append_assoc, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi j' i h

theorem jsE_data (N k j' : ℕ) (E : List Bool) (c : ℕ) (hj : j' ≤ k) (h1 : 2 * j' ≤ c)
    (h2 : c < 2 * k) :
    (jsT N k j' ++ E).getD c false = true := by
  rw [jsT]
  simp only [List.append_assoc]
  rw [show c = 2 * j' + (c - 2 * j') from by omega,
    getD_append_left_length' _ _ (markedD_length j'),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem jsE_m_lo (N k j' : ℕ) (E : List Bool) (hj : j' ≤ k) :
    (jsT N k j' ++ E).getD (2 * k) false = false := by
  rw [jsT]
  simp only [List.append_assoc]
  rw [show 2 * k = 2 * j' + (2 * (k - j') + 0) from by omega,
    getD_append_left_length' _ _ (markedD_length j'),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem jsE_m_hi (N k j' : ℕ) (E : List Bool) (hj : j' ≤ k) :
    (jsT N k j' ++ E).getD (2 * k + 1) false = true := by
  rw [jsT]
  simp only [List.append_assoc]
  rw [show 2 * k + 1 = 2 * j' + (2 * (k - j') + 1) from by omega,
    getD_append_left_length' _ _ (markedD_length j'),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-- Padding cells read `false` (both cells of every padding pair). -/
theorem jsE_pad (N k j' : ℕ) (E : List Bool) (c : ℕ) (hj : j' ≤ k) (hk : k ≤ N)
    (h1 : 2 * k + 2 ≤ c) (h2 : c < 2 * N + 2) :
    (jsT N k j' ++ E).getD c false = false := by
  rw [jsT]
  simp only [List.append_assoc]
  rw [show c = 2 * j' + (2 * (k - j') + (2 + (c - 2 * k - 2))) from by omega,
    getD_append_left_length' _ _ (markedD_length j'),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem jhE_pair_lo (N k i : ℕ) (E : List Bool) (h : i < k) :
    (jhT N k i ++ E).getD (2 * i) false = true := by
  rw [jhT, List.append_assoc, getD_append_length' _ _ List.length_replicate,
    show k - i = (k - i - 1) + 1 from by omega]
  rfl

theorem jhE_pair_hi (N k i : ℕ) (E : List Bool) (h : i < k) :
    (jhT N k i ++ E).getD (2 * i + 1) false = false := by
  rw [jhT, List.append_assoc, getD_append_left_length' _ _ List.length_replicate,
    show k - i = (k - i - 1) + 1 from by omega]
  rfl

theorem jhE_m_lo (N k : ℕ) (E : List Bool) :
    (jhT N k k ++ E).getD (2 * k) false = false := by
  rw [jhT, Nat.sub_self, List.append_assoc, getD_append_length' _ _ List.length_replicate]
  rfl

theorem jhE_m_hi (N k : ℕ) (E : List Bool) :
    (jhT N k k ++ E).getD (2 * k + 1) false = true := by
  rw [jhT, Nat.sub_self, List.append_assoc, getD_append_left_length' _ _ List.length_replicate]
  rfl

/-! ### The three structural `J`-writes -/

/-- Splice-marking the loop variable's next data pair. -/
theorem jsT_mark (N k j' : ℕ) (E : List Bool) (hj : j' < k) (hk : k ≤ N) :
    writeAt (jsT N k j' ++ E) (2 * j' + 1) false = jsT N k (j' + 1) ++ E := by
  rw [writeAt_of_lt false (by
      rw [List.length_append, jsT_length N k j' (by omega) hk]; omega),
    List.set_append_left _ _ (by rw [jsT_length N k j' (by omega) hk]; omega), jsT,
    set_append_left_length' _ _ (markedD_length j'),
    show 2 * (k - j') = 2 * (k - j' - 1) + 1 + 1 from by omega,
    List.replicate_succ, List.replicate_succ]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc, markedD_snoc,
    show k - j' - 1 = k - (j' + 1) from by omega]
  rfl

/-- Healing the loop variable's next splice-marked pair. -/
theorem jhT_heal (N k i : ℕ) (E : List Bool) (hi : i < k) (hk : k ≤ N) :
    writeAt (jhT N k i ++ E) (2 * i + 1) true = jhT N k (i + 1) ++ E := by
  rw [writeAt_of_lt true (by
      rw [List.length_append, jhT_length N k i (by omega) hk]; omega),
    List.set_append_left _ _ (by rw [jhT_length N k i (by omega) hk]; omega), jhT,
    set_append_left_length' _ _ List.length_replicate,
    show k - i = (k - i - 1) + 1 from by omega]
  simp only [markedD, List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc,
    show ([true, true] : List Bool) = List.replicate 2 true from rfl, ← List.replicate_add,
    show 2 * i + 2 = 2 * (i + 1) from by ring,
    show k - i - 1 = k - (i + 1) from by omega]
  rfl

/-- `set` at exactly a prefix's length. -/
theorem set_append_length' {α : Type} (l₁ l₂ : List α) {k : ℕ} (hk : l₁.length = k) (w : α) :
    (l₁ ++ l₂).set k w = l₁ ++ l₂.set 0 w := by
  subst hk
  have h := set_append_left_length' l₁ l₂ rfl 0 w
  rwa [Nat.add_zero] at h

/-- **The in-place increment.**  The four marker-advancing writes turn value `j` into `j + 1` inside the
fixed footprint — the marker moves onto the padding, no region grows. -/
theorem jT_incr (N j : ℕ) (E : List Bool) (hj : j < N) :
    writeAt (writeAt (writeAt (writeAt (jT N j ++ E) (2 * j) true) (2 * j + 1) true)
        (2 * j + 2) false) (2 * j + 3) true
      = jT N (j + 1) ++ E := by
  have hlen : (jT N j).length = 2 * N + 2 := jT_length N j (by omega)
  have hpad : 2 * (N - j) = 2 * (N - j - 1) + 1 + 1 := by omega
  -- write 1: marker low cell `false ↦ true`
  have e1 : writeAt (jT N j ++ E) (2 * j) true
      = (List.replicate (2 * j) true ++ ([true, true]
          ++ List.replicate (2 * (N - j)) false)) ++ E := by
    rw [writeAt_of_lt true (by rw [List.length_append]; omega),
      List.set_append_left _ _ (by omega), jT,
      set_append_length' _ _ List.length_replicate]
    rfl
  -- write 2: marker high cell `true ↦ true`
  have e2 : writeAt ((List.replicate (2 * j) true ++ ([true, true]
        ++ List.replicate (2 * (N - j)) false)) ++ E) (2 * j + 1) true
      = (List.replicate (2 * j) true ++ ([true, true]
          ++ List.replicate (2 * (N - j)) false)) ++ E := by
    rw [writeAt_of_lt true (by
        simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
        omega),
      List.set_append_left _ _ (by
        simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
        omega),
      set_append_left_length' _ _ List.length_replicate]
    rfl
  -- write 3: first padding cell `false ↦ false`
  have e3 : writeAt ((List.replicate (2 * j) true ++ ([true, true]
        ++ List.replicate (2 * (N - j)) false)) ++ E) (2 * j + 2) false
      = (List.replicate (2 * j) true ++ ([true, true]
          ++ List.replicate (2 * (N - j)) false)) ++ E := by
    rw [writeAt_of_lt false (by
        simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
        omega),
      List.set_append_left _ _ (by
        simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
        omega),
      set_append_left_length' _ _ List.length_replicate, hpad,
      List.replicate_succ, List.replicate_succ]
    simp only [List.cons_append, List.nil_append, List.set_cons_succ, List.set_cons_zero]
  -- write 4: second padding cell `false ↦ true` — the fresh marker's high cell
  have e4 : writeAt ((List.replicate (2 * j) true ++ ([true, true]
        ++ List.replicate (2 * (N - j)) false)) ++ E) (2 * j + 3) true
      = jT N (j + 1) ++ E := by
    rw [writeAt_of_lt true (by
        simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
        omega),
      List.set_append_left _ _ (by
        simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
        omega),
      set_append_left_length' _ _ List.length_replicate, hpad,
      List.replicate_succ, List.replicate_succ]
    simp only [List.cons_append, List.nil_append, List.set_cons_succ, List.set_cons_zero]
    rw [jT, show 2 * (j + 1) = 2 * j + 1 + 1 from by ring,
      List.replicate_succ', List.replicate_succ',
      show 2 * (N - (j + 1)) = 2 * (N - j - 1) from by omega]
    simp [List.append_assoc]
  rw [e1, e2, e3, e4]

/-- A combined bound-region fact: every pair's low cell reads `true`. -/
theorem cntE_lo (v a : ℕ) (E : List Bool) (i : ℕ) (ha : a ≤ v) (h : i < v) :
    (cntT v a ++ E).getD (2 * i) false = true := by
  rcases Nat.lt_or_ge i a with hia | hia
  · exact cntE_mark_lo v a E i hia
  · exact cntE_data v a E (2 * i) ha (by omega) (by omega)

/-- Lifting a suffix-generic `getD` fact past a known-length prefix. -/
theorem liftJ (A X : List Bool) {q c : ℕ} (hq : A.length = q) {b : Bool}
    (h : X.getD c false = b) : (A ++ X).getD (q + c) false = b := by
  rw [getD_append_left_length' A X hq c]; exact h

/-- The four-write spine past a known-length prefix. -/
theorem W4_append_right (A X : List Bool) (q p : ℕ) (b1 b2 b3 b4 : Bool) (hq : A.length = q)
    (h : p + 3 < X.length) :
    writeAt (writeAt (writeAt (writeAt (A ++ X) (q + p) b1) (q + p + 1) b2) (q + p + 2) b3)
        (q + p + 3) b4
      = A ++ writeAt (writeAt (writeAt (writeAt X p b1) (p + 1) b2) (p + 2) b3) (p + 3) b4 := by
  have hl1 : (writeAt X p b1).length = X.length := by
    rw [writeAt_of_lt b1 (by omega), List.length_set]
  have hl2 : (writeAt (writeAt X p b1) (p + 1) b2).length = X.length := by
    rw [writeAt_of_lt b2 (by omega), List.length_set, hl1]
  have hl3 : (writeAt (writeAt (writeAt X p b1) (p + 1) b2) (p + 2) b3).length = X.length := by
    rw [writeAt_of_lt b3 (by omega), List.length_set, hl2]
  rw [writeAt_append_right A X q p b1 hq (by omega),
    show q + p + 1 = q + (p + 1) from by omega,
    writeAt_append_right A _ q (p + 1) b2 hq (by omega),
    show q + p + 2 = q + (p + 2) from by omega,
    writeAt_append_right A _ q (p + 2) b3 hq (by omega),
    show q + p + 3 = q + (p + 3) from by omega,
    writeAt_append_right A _ q (p + 3) b4 hq (by omega)]

/-! ## The range machine

Control: `Fin 31 × Bool` (stored low cell).  Phases: `0/1` find in the bound (skip `10`, mark `11` + reset
⇒ splice the loop variable, boundary `01` ⇒ restore-and-halt), `2/3` skip the whole bound region (low cell
`true` ⇒ skip, boundary ⇒ cross), `4/5` find in the loop variable (skip `10`, mark ⇒ seek, boundary ⇒ the
closing `false`), `6/7` seek the variable's rest to its boundary, `8/9` seek the output data to its
terminator, `10–13` the doubled-`true` snoc + reset (next sub-round), `14/15` the final seek, `16–19` the
doubled-`false` snoc + reset, `20/21` skip the bound again, `22/23` heal the loop variable (boundary ⇒
increment), `24–27` the in-place increment + reset (next round), `28/29` restore the bound, `30` = halt. -/

def rangeMachine : Machine where
  State := Fin 31 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 30)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then (if b then ((2, s.2), some false, 3) else ((0, s.2), none, 1))
       else (if b then ((28, s.2), none, 3) else ((30, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((30, s.2), none, 2)))
    else if s.1 = 4 then ((5, b), none, 1)
    else if s.1 = 5 then
      (if s.2 then (if b then ((6, s.2), some false, 1) else ((4, s.2), none, 1))
       else (if b then ((14, s.2), none, 1) else ((30, s.2), none, 2)))
    else if s.1 = 6 then ((7, b), none, 1)
    else if s.1 = 7 then
      (if b = s.2 then ((6, s.2), none, 1) else ((8, s.2), none, 1))
    else if s.1 = 8 then ((9, b), none, 1)
    else if s.1 = 9 then
      (if b = s.2 then ((8, s.2), none, 1) else ((10, s.2), none, 0))
    else if s.1 = 10 then ((11, s.2), some true, 1)
    else if s.1 = 11 then ((12, s.2), some true, 1)
    else if s.1 = 12 then ((13, s.2), some false, 1)
    else if s.1 = 13 then ((2, s.2), some true, 3)
    else if s.1 = 14 then ((15, b), none, 1)
    else if s.1 = 15 then
      (if b = s.2 then ((14, s.2), none, 1) else ((16, s.2), none, 0))
    else if s.1 = 16 then ((17, s.2), some false, 1)
    else if s.1 = 17 then ((18, s.2), some false, 1)
    else if s.1 = 18 then ((19, s.2), some false, 1)
    else if s.1 = 19 then ((20, s.2), some true, 3)
    else if s.1 = 20 then ((21, b), none, 1)
    else if s.1 = 21 then
      (if s.2 then ((20, s.2), none, 1)
       else (if b then ((22, s.2), none, 1) else ((30, s.2), none, 2)))
    else if s.1 = 22 then ((23, b), none, 1)
    else if s.1 = 23 then
      (if s.2 then (if b then ((30, s.2), none, 2) else ((22, true), some true, 1))
       else (if b then ((24, s.2), none, 0) else ((30, s.2), none, 2)))
    else if s.1 = 24 then ((25, s.2), some true, 1)
    else if s.1 = 25 then ((26, s.2), some true, 1)
    else if s.1 = 26 then ((27, s.2), some false, 1)
    else if s.1 = 27 then ((0, s.2), some true, 3)
    else if s.1 = 28 then ((29, b), none, 1)
    else if s.1 = 29 then
      (if s.2 then (if b then ((30, s.2), none, 2) else ((28, true), some true, 1))
       else ((30, s.2), none, 2))
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_rg (x : List Bool) : init rangeMachine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem step_r0 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r1_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step rangeMachine ⟨(1, true), p, T⟩ = ⟨(2, true), 0, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r1_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step rangeMachine ⟨(1, true), p, T⟩ = ⟨(0, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r1_done {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step rangeMachine ⟨(1, false), p, T⟩ = ⟨(28, false), 0, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r2 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r3_skip {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(3, true), p, T⟩ = ⟨(2, true), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r3_cross {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step rangeMachine ⟨(3, false), p, T⟩ = ⟨(4, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r4 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r5_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step rangeMachine ⟨(5, true), p, T⟩ = ⟨(6, true), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r5_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step rangeMachine ⟨(5, true), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r5_done {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step rangeMachine ⟨(5, false), p, T⟩ = ⟨(14, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r6 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(6, s), p, T⟩ = ⟨(7, T.getD p false), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r7_eq {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = s) :
    step rangeMachine ⟨(7, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r7_ne {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false ≠ s) :
    step rangeMachine ⟨(7, s), p, T⟩ = ⟨(8, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r8 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(8, s), p, T⟩ = ⟨(9, T.getD p false), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r9_eq {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = s) :
    step rangeMachine ⟨(9, s), p, T⟩ = ⟨(8, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r9_ne {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false ≠ s) :
    step rangeMachine ⟨(9, s), p, T⟩ = ⟨(10, s), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r10 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(10, s), p, T⟩ = ⟨(11, s), p + 1, writeAt T p true⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r11 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(11, s), p, T⟩ = ⟨(12, s), p + 1, writeAt T p true⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r12 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(12, s), p, T⟩ = ⟨(13, s), p + 1, writeAt T p false⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r13 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(13, s), p, T⟩ = ⟨(2, s), 0, writeAt T p true⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r14 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(14, s), p, T⟩ = ⟨(15, T.getD p false), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r15_eq {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = s) :
    step rangeMachine ⟨(15, s), p, T⟩ = ⟨(14, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r15_ne {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false ≠ s) :
    step rangeMachine ⟨(15, s), p, T⟩ = ⟨(16, s), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r16 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(16, s), p, T⟩ = ⟨(17, s), p + 1, writeAt T p false⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r17 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(17, s), p, T⟩ = ⟨(18, s), p + 1, writeAt T p false⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r18 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(18, s), p, T⟩ = ⟨(19, s), p + 1, writeAt T p false⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r19 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(19, s), p, T⟩ = ⟨(20, s), 0, writeAt T p true⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r20 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(20, s), p, T⟩ = ⟨(21, T.getD p false), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r21_skip {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(21, true), p, T⟩ = ⟨(20, true), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r21_cross {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step rangeMachine ⟨(21, false), p, T⟩ = ⟨(22, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r22 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(22, s), p, T⟩ = ⟨(23, T.getD p false), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r23_heal {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step rangeMachine ⟨(23, true), p, T⟩ = ⟨(22, true), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r23_toIncr {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step rangeMachine ⟨(23, false), p, T⟩ = ⟨(24, false), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r24 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(24, s), p, T⟩ = ⟨(25, s), p + 1, writeAt T p true⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r25 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(25, s), p, T⟩ = ⟨(26, s), p + 1, writeAt T p true⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r26 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(26, s), p, T⟩ = ⟨(27, s), p + 1, writeAt T p false⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r27 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(27, s), p, T⟩ = ⟨(0, s), 0, writeAt T p true⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r28 {s : Bool} {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(28, s), p, T⟩ = ⟨(29, T.getD p false), p + 1, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

theorem step_r29_heal {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step rangeMachine ⟨(29, true), p, T⟩ = ⟨(28, true), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rangeMachine, moveHead, h]

theorem step_r29_done {p : ℕ} {T : List Bool} :
    step rangeMachine ⟨(29, false), p, T⟩ = ⟨(30, false), p, T⟩ := by
  simp only [step, rangeMachine, moveHead]; rfl

/-! ### Pair-step lemmas -/

theorem run_two_skipD {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run rangeMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r0, h1, step_r1_skip h2]

theorem run_two_markD {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_r0, h1, step_r1_mark h2]

theorem run_two_toRstD {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(0, s), p, T⟩ = ⟨(28, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r0, h1, step_r1_done h2]

theorem run_two_skipW {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run rangeMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r2, h1, step_r3_skip]

theorem run_two_crossW {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r2, h1, step_r3_cross h2]

theorem run_two_skipJ {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run rangeMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r4, h1, step_r5_skip h2]

theorem run_two_markJ {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(4, s), p, T⟩ = ⟨(6, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_r4, h1, step_r5_mark h2]

theorem run_two_doneJ {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(4, s), p, T⟩ = ⟨(14, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r4, h1, step_r5_done h2]

theorem run_two_seekA {s : Bool} {p : ℕ} {T : List Bool}
    (h : T.getD p false = T.getD (p + 1) false) :
    run rangeMachine 2 ⟨(6, s), p, T⟩ = ⟨(6, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r6, step_r7_eq h.symm]

theorem run_two_crossA {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(6, s), p, T⟩ = ⟨(8, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r6, h1, step_r7_ne (by rw [h2]; simp)]

theorem run_two_seekB {s : Bool} {p : ℕ} {T : List Bool}
    (h : T.getD p false = T.getD (p + 1) false) :
    run rangeMachine 2 ⟨(8, s), p, T⟩ = ⟨(8, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r8, step_r9_eq h.symm]

theorem run_two_detectB {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(8, s), p, T⟩ = ⟨(10, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r8, h1, step_r9_ne (by rw [h2]; simp),
    show p + 1 - 1 = p from by omega]

theorem run_four_true {s : Bool} {p : ℕ} {T : List Bool} :
    run rangeMachine 4 ⟨(10, s), p, T⟩
      = ⟨(2, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_r10, step_r11, step_r12, step_r13]

theorem run_two_seekFr {s : Bool} {p : ℕ} {T : List Bool}
    (h : T.getD p false = T.getD (p + 1) false) :
    run rangeMachine 2 ⟨(14, s), p, T⟩ = ⟨(14, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r14, step_r15_eq h.symm]

theorem run_two_detectF {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(14, s), p, T⟩ = ⟨(16, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r14, h1, step_r15_ne (by rw [h2]; simp),
    show p + 1 - 1 = p from by omega]

theorem run_four_false {s : Bool} {p : ℕ} {T : List Bool} :
    run rangeMachine 4 ⟨(16, s), p, T⟩
      = ⟨(20, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_r16, step_r17, step_r18, step_r19]

theorem run_two_skipW2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run rangeMachine 2 ⟨(20, s), p, T⟩ = ⟨(20, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r20, h1, step_r21_skip]

theorem run_two_crossW2 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(20, s), p, T⟩ = ⟨(22, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r20, h1, step_r21_cross h2]

theorem run_two_healJ {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run rangeMachine 2 ⟨(22, s), p, T⟩ = ⟨(22, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_r22, h1, step_r23_heal h2]

theorem run_two_toIncr {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run rangeMachine 2 ⟨(22, s), p, T⟩ = ⟨(24, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r22, h1, step_r23_toIncr h2,
    show p + 1 - 1 = p from by omega]

theorem run_four_incr {s : Bool} {p : ℕ} {T : List Bool} :
    run rangeMachine 4 ⟨(24, s), p, T⟩
      = ⟨(0, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_r24, step_r25, step_r26, step_r27]

theorem run_two_healD {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run rangeMachine 2 ⟨(28, s), p, T⟩ = ⟨(28, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_r28, h1, step_r29_heal h2]

theorem run_two_doneD {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run rangeMachine 2 ⟨(28, s), p, T⟩ = ⟨(30, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_r28, h1, step_r29_done]

/-! ### Scan run-invariants -/

theorem run_skipDs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run rangeMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipD hk.1 hk.2]
    rfl

theorem run_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rangeMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipW (h k (by omega))]
    rfl

theorem run_skipJs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run rangeMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipJ hk.1 hk.2]
    rfl

theorem run_seekAs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run rangeMachine (2 * k) ⟨(6, s), q, T⟩
      = ⟨(6, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekA (h k (by omega))]
    rfl

theorem run_seekBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run rangeMachine (2 * k) ⟨(8, s), q, T⟩
      = ⟨(8, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekB (h k (by omega))]
    rfl

theorem run_seekFrs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run rangeMachine (2 * k) ⟨(14, s), q, T⟩
      = ⟨(14, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekFr (h k (by omega))]
    rfl

theorem run_skipW2s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run rangeMachine (2 * k) ⟨(20, s), q, T⟩
      = ⟨(20, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipW2 (h k (by omega))]
    rfl

/-- The loop-variable heal invariant (evolving tape, past the bound prefix). -/
theorem run_healJs (A : List Bool) (N k : ℕ) (E : List Bool) (hq : A.length = 2 * N + 2)
    (hk : k ≤ N) (s : Bool) (i : ℕ) (hi : i ≤ k) :
    run rangeMachine (2 * i) ⟨(22, s), 2 * N + 2, A ++ (jhT N k 0 ++ E)⟩
      = ⟨(22, if i = 0 then s else true), 2 * N + 2 + 2 * i, A ++ (jhT N k i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hlo : (A ++ (jhT N k i ++ E)).getD (2 * N + 2 + 2 * i) false = true :=
      liftJ A _ hq (jhE_pair_lo N k i E (by omega))
    have hhi : (A ++ (jhT N k i ++ E)).getD (2 * N + 2 + 2 * i + 1) false = false := by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
      exact liftJ A _ hq (jhE_pair_hi N k i E (by omega))
    have hw : writeAt (A ++ (jhT N k i ++ E)) (2 * N + 2 + 2 * i + 1) true
        = A ++ (jhT N k (i + 1) ++ E) := by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega,
        writeAt_append_right A _ (2 * N + 2) (2 * i + 1) true hq
          (by rw [List.length_append, jhT_length N k i (by omega) hk]; omega),
        jhT_heal N k i E (by omega) hk]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_healJ hlo hhi, hw]
    rfl

/-- The bound-restore invariant (reusing the E1 healing descriptor). -/
theorem run_healDs (v : ℕ) (E : List Bool) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run rangeMachine (2 * i) ⟨(28, s), 0, hlT v 0 ++ E⟩
      = ⟨(28, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_healD (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ## The splice sub-round -/

/-- **One splice sub-round.**  Skip the bound region, mark the loop variable's pair `j'`, seek across two
region boundaries to the output terminator, splice one doubled `true`, reset. -/
theorem run_subround (N a k j' : ℕ) (OUT : List Bool) (ha : a ≤ N) (hk : k ≤ N) (hj : j' < k)
    (s : Bool) :
    run rangeMachine (4 * N + 2 * OUT.length + 2 * j' + 10)
      ⟨(2, s), 0, cntT N a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))⟩
      = ⟨(2, false), 0,
          cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate (j' + 1) true))⟩ := by
  have hcl := cntT_length N a ha
  -- skip the bound region and cross its boundary
  have st1 := run_skipWs (cntT N a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))
    0 N s (fun i hi => by simpa using cntE_lo N a _ i ha hi)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_crossW (s := if N = 0 then s else true) (p := 2 * N)
    (T := cntT N a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))
    (cntE_cm_lo N a _ ha) (cntE_cm_hi N a _ ha)
  -- skip the loop variable's marks and mark its pair `j'`
  have st3 := run_skipJs (cntT N a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))
    (2 * N + 2) j' false (fun i hi =>
      ⟨liftJ _ _ hcl (jsE_mark_lo N k j' _ i hi), by
        rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
        exact liftJ _ _ hcl (jsE_mark_hi N k j' _ i hi)⟩)
  have st4 := run_two_markJ (s := if j' = 0 then false else true) (p := 2 * N + 2 + 2 * j')
    (T := cntT N a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))
    (liftJ _ _ hcl (jsE_data N k j' _ (2 * j') (by omega) (by omega) (by omega)))
    (by rw [show 2 * N + 2 + 2 * j' + 1 = 2 * N + 2 + (2 * j' + 1) from by omega]
        exact liftJ _ _ hcl (jsE_data N k j' _ (2 * j' + 1) (by omega) (by omega) (by omega)))
  have hw4 : writeAt (cntT N a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))
      (2 * N + 2 + 2 * j' + 1) false
      = cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)) := by
    rw [show 2 * N + 2 + 2 * j' + 1 = 2 * N + 2 + (2 * j' + 1) from by omega,
      writeAt_append_right _ _ (2 * N + 2) (2 * j' + 1) false hcl
        (by rw [List.length_append, jsT_length N k j' (by omega) hk]; omega),
      jsT_mark N k j' _ (by omega) hk]
  rw [hw4] at st4
  -- seek across the variable's rest and its boundary
  have st5 := run_seekAs
    (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
    (2 * N + 2 + 2 * j' + 2) (k - j' - 1) true (fun i hi => by
      have e1 : (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))).getD
          (2 * N + 2 + 2 * j' + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 2 * j' + 2 + 2 * i = 2 * N + 2 + (2 * j' + 2 + 2 * i) from by omega]
        exact liftJ _ _ hcl (jsE_data N k (j' + 1) _ (2 * j' + 2 + 2 * i)
          (by omega) (by omega) (by omega))
      have e2 : (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))).getD
          (2 * N + 2 + 2 * j' + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * j' + 2 + 2 * i + 1
            = 2 * N + 2 + (2 * j' + 2 + 2 * i + 1) from by omega]
        exact liftJ _ _ hcl (jsE_data N k (j' + 1) _ (2 * j' + 2 + 2 * i + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 2 * j' + 2 + 2 * (k - j' - 1) = 2 * N + 2 + 2 * k from by omega] at st5
  have st6 := run_two_crossA
    (s := storedD (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
      (2 * N + 2 + 2 * j' + 2) true (k - j' - 1))
    (p := 2 * N + 2 + 2 * k)
    (T := cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
    (liftJ _ _ hcl (jsE_m_lo N k (j' + 1) _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * k + 1 = 2 * N + 2 + (2 * k + 1) from by omega]
        exact liftJ _ _ hcl (jsE_m_hi N k (j' + 1) _ (by omega)))
  -- seek the padding, then the output data
  have st7 := run_seekBs
    (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
    (2 * N + 2 + 2 * k + 2) (N - k) false (fun i hi => by
      have e1 : (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))).getD
          (2 * N + 2 + 2 * k + 2 + 2 * i) false = false := by
        rw [show 2 * N + 2 + 2 * k + 2 + 2 * i = 2 * N + 2 + (2 * k + 2 + 2 * i) from by omega]
        exact liftJ _ _ hcl (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i)
          (by omega) hk (by omega) (by omega))
      have e2 : (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))).getD
          (2 * N + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
        rw [show 2 * N + 2 + 2 * k + 2 + 2 * i + 1
            = 2 * N + 2 + (2 * k + 2 + 2 * i + 1) from by omega]
        exact liftJ _ _ hcl (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i + 1)
          (by omega) hk (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 2 * k + 2 + 2 * (N - k) = 4 * N + 4 from by omega] at st7
  have hq2 : (cntT N a).length + (jsT N k (j' + 1)).length = 4 * N + 4 := by
    rw [hcl, jsT_length N k (j' + 1) (by omega) hk]; omega
  have st8 := run_seekBs
    (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
    (4 * N + 4) (OUT.length + j')
    (storedD (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
      (2 * N + 2 + 2 * k + 2) false (N - k))
    (fun i hi => preD2_data_eq (cntT N a) (jsT N k (j' + 1)) (OUT ++ List.replicate j' true)
      (4 * N + 4) i hq2 (by rw [List.length_append, List.length_replicate]; omega))
  -- detect the terminator and splice the doubled `true`
  have hm1 := preD2_mark_lo (cntT N a) (jsT N k (j' + 1)) (OUT ++ List.replicate j' true)
    (4 * N + 4) hq2
  have hm2 := preD2_mark_hi (cntT N a) (jsT N k (j' + 1)) (OUT ++ List.replicate j' true)
    (4 * N + 4) hq2
  rw [show (OUT ++ List.replicate j' true).length = OUT.length + j' from by
    rw [List.length_append, List.length_replicate]] at hm1 hm2
  have st9 := run_two_detectB
    (s := storedD (cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
      (4 * N + 4) (storedD (cntT N a ++ (jsT N k (j' + 1)
        ++ encodeD (OUT ++ List.replicate j' true))) (2 * N + 2 + 2 * k + 2) false (N - k))
      (OUT.length + j'))
    (p := 4 * N + 4 + 2 * (OUT.length + j')) hm1 hm2
  have hsn := writes_snoc2 (cntT N a) (jsT N k (j' + 1)) (OUT ++ List.replicate j' true)
    (4 * N + 4) hq2 true
  rw [show (OUT ++ List.replicate j' true).length = OUT.length + j' from by
      rw [List.length_append, List.length_replicate],
    List.append_assoc, ← List.replicate_succ'] at hsn
  have st10 := run_four_true (s := false) (p := 4 * N + 4 + 2 * (OUT.length + j'))
    (T := cntT N a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
  rw [hsn] at st10
  -- assemble
  rw [show 4 * N + 2 * OUT.length + 2 * j' + 10
      = 2 * N + (2 + (2 * j' + (2 + (2 * (k - j' - 1) + (2 + (2 * (N - k)
          + (2 * (OUT.length + j') + (2 + 4)))))))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, run_add, st8, run_add, st9, st10]

/-! ## The sub-rounds and the round -/

/-- Cumulative clock of the first `j'` splice sub-rounds (`Lo` the round's base output length). -/
def subs (N Lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | j' + 1 => subs N Lo j' + (4 * N + 2 * Lo + 2 * j' + 10)

theorem run_subrounds (N a k : ℕ) (OUT : List Bool) (ha : a ≤ N) (hk : k ≤ N) (s : Bool)
    (j'' : ℕ) (hj : j'' ≤ k) :
    run rangeMachine (subs N OUT.length j'')
      ⟨(2, s), 0, cntT N a ++ (jsT N k 0 ++ encodeD OUT)⟩
      = ⟨(2, if j'' = 0 then s else false), 0,
          cntT N a ++ (jsT N k j'' ++ encodeD (OUT ++ List.replicate j'' true))⟩ := by
  induction j'' with
  | zero =>
    simp
    rfl
  | succ j'' ih =>
    rw [show subs N OUT.length (j'' + 1)
        = subs N OUT.length j'' + (4 * N + 2 * OUT.length + 2 * j'' + 10) from rfl,
      run_add, ih (by omega), run_subround N a k j'' OUT ha hk (by omega), if_neg (by omega)]

/-- The full round clock: find-and-mark, `k` sub-rounds, the closing `false`, heal, increment. -/
def roundClock (N L k : ℕ) : ℕ :=
  subs N (L + rangeLen k) k + 6 * N + 2 * (L + rangeLen k) + 6 * k + 20

/-- **One range round.**  Marks the bound's pair `k`, splices `encodeNat k`, increments the loop variable in
place, and resets. -/
theorem run_range_round (N k : ℕ) (out : List Bool) (hk : k < N) (s : Bool) :
    run rangeMachine (roundClock N out.length k)
      ⟨(0, s), 0, cntT N k ++ (jT N k ++ encodeD (out ++ rangeEnc k))⟩
      = ⟨(0, false), 0,
          cntT N (k + 1) ++ (jT N (k + 1) ++ encodeD (out ++ rangeEnc (k + 1)))⟩ := by
  have hcl := cntT_length N (k + 1) (by omega : k + 1 ≤ N)
  have hOl : (out ++ rangeEnc k).length = out.length + rangeLen k := by
    rw [List.length_append, rangeEnc_length]
  -- find and mark the bound's pair `k` (resetting)
  have st1 := run_skipDs (cntT N k ++ (jT N k ++ encodeD (out ++ rangeEnc k))) 0 k s
    (fun i hi => ⟨by simpa using cntE_mark_lo N k _ i hi,
                  by simpa using cntE_mark_hi N k _ i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_markD (s := if k = 0 then s else true) (p := 2 * k)
    (T := cntT N k ++ (jT N k ++ encodeD (out ++ rangeEnc k)))
    (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega))
    (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark N k _ hk] at st2
  -- the `k` splice sub-rounds
  have st3 := run_subrounds N (k + 1) k (out ++ rangeEnc k) (by omega) (by omega) true k
    (le_refl k)
  rw [hOl, jsT_zero] at st3
  -- the closing `false`: exhaust the variable, seek, splice
  have st4 := run_skipWs (cntT N (k + 1) ++ (jsT N k k
      ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true))) 0 N
    (if k = 0 then true else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at st4
  have st5 := run_two_crossW (s := if N = 0 then (if k = 0 then true else false) else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (jsT N k k
      ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true)))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have st6 := run_skipJs (cntT N (k + 1) ++ (jsT N k k
      ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true))) (2 * N + 2) k false
    (fun i hi => ⟨liftJ _ _ hcl (jsE_mark_lo N k k _ i hi), by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hcl (jsE_mark_hi N k k _ i hi)⟩)
  have st7 := run_two_doneJ (s := if k = 0 then false else true) (p := 2 * N + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (jsT N k k
      ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true)))
    (liftJ _ _ hcl (jsE_m_lo N k k _ (le_refl k)))
    (by rw [show 2 * N + 2 + 2 * k + 1 = 2 * N + 2 + (2 * k + 1) from by omega]
        exact liftJ _ _ hcl (jsE_m_hi N k k _ (le_refl k)))
  have st8 := run_seekFrs (cntT N (k + 1) ++ (jsT N k k
      ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true))) (2 * N + 2 + 2 * k + 2)
    (N - k) false (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (jsT N k k
          ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true))).getD
          (2 * N + 2 + 2 * k + 2 + 2 * i) false = false := by
        rw [show 2 * N + 2 + 2 * k + 2 + 2 * i = 2 * N + 2 + (2 * k + 2 + 2 * i) from by omega]
        exact liftJ _ _ hcl (jsE_pad N k k _ (2 * k + 2 + 2 * i) (le_refl k) (by omega)
          (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (jsT N k k
          ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true))).getD
          (2 * N + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
        rw [show 2 * N + 2 + 2 * k + 2 + 2 * i + 1
            = 2 * N + 2 + (2 * k + 2 + 2 * i + 1) from by omega]
        exact liftJ _ _ hcl (jsE_pad N k k _ (2 * k + 2 + 2 * i + 1) (le_refl k) (by omega)
          (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 2 * k + 2 + 2 * (N - k) = 4 * N + 4 from by omega] at st8
  have hq2 : (cntT N (k + 1)).length + (jsT N k k).length = 4 * N + 4 := by
    rw [hcl, jsT_length N k k (le_refl k) (by omega)]; omega
  have st9 := run_seekFrs (cntT N (k + 1) ++ (jsT N k k
      ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true))) (4 * N + 4)
    ((out ++ rangeEnc k).length + k)
    (storedD (cntT N (k + 1) ++ (jsT N k k
      ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true))) (2 * N + 2 + 2 * k + 2)
      false (N - k))
    (fun i hi => preD2_data_eq (cntT N (k + 1)) (jsT N k k)
      ((out ++ rangeEnc k) ++ List.replicate k true) (4 * N + 4) i hq2
      (by rw [List.length_append, List.length_replicate]; omega))
  rw [hOl] at st9
  have hm1 := preD2_mark_lo (cntT N (k + 1)) (jsT N k k)
    ((out ++ rangeEnc k) ++ List.replicate k true) (4 * N + 4) hq2
  have hm2 := preD2_mark_hi (cntT N (k + 1)) (jsT N k k)
    ((out ++ rangeEnc k) ++ List.replicate k true) (4 * N + 4) hq2
  rw [show ((out ++ rangeEnc k) ++ List.replicate k true).length
      = (out ++ rangeEnc k).length + k from by rw [List.length_append, List.length_replicate],
    hOl] at hm1 hm2
  have st10 := run_two_detectF
    (s := storedD (cntT N (k + 1) ++ (jsT N k k
      ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true))) (4 * N + 4)
      (storedD (cntT N (k + 1) ++ (jsT N k k
        ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true))) (2 * N + 2 + 2 * k + 2)
        false (N - k)) (out.length + rangeLen k + k))
    (p := 4 * N + 4 + 2 * (out.length + rangeLen k + k)) hm1 hm2
  have hsn := writes_snoc2 (cntT N (k + 1)) (jsT N k k)
    ((out ++ rangeEnc k) ++ List.replicate k true) (4 * N + 4) hq2 false
  rw [show ((out ++ rangeEnc k) ++ List.replicate k true).length
      = (out ++ rangeEnc k).length + k from by rw [List.length_append, List.length_replicate],
    hOl, List.append_assoc (out ++ rangeEnc k),
    show List.replicate k true ++ [false] = encodeNat k from rfl,
    show (out ++ rangeEnc k) ++ encodeNat k = out ++ rangeEnc (k + 1) from by
      rw [List.append_assoc]; rfl] at hsn
  have st11 := run_four_false (s := false)
    (p := 4 * N + 4 + 2 * (out.length + rangeLen k + k))
    (T := cntT N (k + 1) ++ (jsT N k k
      ++ encodeD ((out ++ rangeEnc k) ++ List.replicate k true)))
  rw [hsn] at st11
  -- heal the loop variable and increment it in place
  have st12 := run_skipW2s (cntT N (k + 1) ++ (jsT N k k
      ++ encodeD (out ++ rangeEnc (k + 1)))) 0 N false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at st12
  have st13 := run_two_crossW2 (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (jsT N k k ++ encodeD (out ++ rangeEnc (k + 1))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have st14 := run_healJs (cntT N (k + 1)) N k (encodeD (out ++ rangeEnc (k + 1))) hcl
    (by omega) false k (le_refl k)
  rw [jhT_zero] at st14
  have st15 := run_two_toIncr (s := if k = 0 then false else true) (p := 2 * N + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (jhT N k k ++ encodeD (out ++ rangeEnc (k + 1))))
    (liftJ _ _ hcl (jhE_m_lo N k _))
    (by rw [show 2 * N + 2 + 2 * k + 1 = 2 * N + 2 + (2 * k + 1) from by omega]
        exact liftJ _ _ hcl (jhE_m_hi N k _))
  have st16 := run_four_incr (s := false) (p := 2 * N + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (jhT N k k ++ encodeD (out ++ rangeEnc (k + 1))))
  have hw16 : writeAt (writeAt (writeAt (writeAt (cntT N (k + 1)
        ++ (jhT N k k ++ encodeD (out ++ rangeEnc (k + 1)))) (2 * N + 2 + 2 * k) true)
        (2 * N + 2 + 2 * k + 1) true) (2 * N + 2 + 2 * k + 2) false)
        (2 * N + 2 + 2 * k + 3) true
      = cntT N (k + 1) ++ (jT N (k + 1) ++ encodeD (out ++ rangeEnc (k + 1))) := by
    rw [jhT_last,
      W4_append_right (cntT N (k + 1)) (jT N k ++ encodeD (out ++ rangeEnc (k + 1)))
        (2 * N + 2) (2 * k) true true false true hcl
        (by rw [List.length_append, jT_length N k (by omega)]; omega),
      jT_incr N k _ hk]
  rw [hw16] at st16
  -- assemble
  rw [show roundClock N out.length k
      = 2 * k + (2 + (subs N (out.length + rangeLen k) k + (2 * N + (2 + (2 * k + (2
          + (2 * (N - k) + (2 * (out.length + rangeLen k + k) + (2 + (4 + (2 * N + (2
          + (2 * k + (2 + 4)))))))))))))) from by rw [roundClock]; omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, run_add, st8, run_add, st9, run_add, st10, run_add, st11, run_add, st12,
    run_add, st13, run_add, st14, run_add, st15, st16]

/-! ## The rounds, the finale, and the top theorem -/

/-- Cumulative clock of the first `k` rounds. -/
def rgRounds (N L : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => rgRounds N L k + roundClock N L k

/-- **Rounds invariant.** -/
theorem run_range_rounds (N : ℕ) (out : List Bool) (k : ℕ) (hk : k ≤ N) (s : Bool) :
    run rangeMachine (rgRounds N out.length k)
      ⟨(0, s), 0, cntT N 0 ++ (jT N 0 ++ encodeD out)⟩
      = ⟨(0, if k = 0 then s else false), 0,
          cntT N k ++ (jT N k ++ encodeD (out ++ rangeEnc k))⟩ := by
  induction k with
  | zero =>
    simp [rangeEnc]
    rfl
  | succ k ih =>
    rw [show rgRounds N out.length (k + 1)
        = rgRounds N out.length k + roundClock N out.length k from rfl,
      run_add, ih (by omega), run_range_round N k out (by omega), if_neg (by omega)]

/-- The range-emitter's explicit clock. -/
def rgClock (N L : ℕ) : ℕ := rgRounds N L N + (2 * N + (2 + (2 * N + 2)))

/-- **The range-emitter runs to completion.**  On `unaryD N ++ (jT N 0 ++ encodeD out)` — the bound, a
zeroed capacity-`N` loop variable, and the output — the machine halts by itself at the explicit clock with
tape **exactly** `unaryD N ++ (unaryD N ++ encodeD (out ++ rangeEnc N))`: the full range
`encodeNat 0 ⋯ encodeNat (N-1)` emitted, the bound restored, the loop variable full. -/
theorem range_run (N : ℕ) (out : List Bool) :
    run rangeMachine (rgClock N out.length)
      (init rangeMachine (unaryD N ++ (jT N 0 ++ encodeD out)))
      = ⟨(30, false), 2 * N + 1,
          unaryD N ++ (unaryD N ++ encodeD (out ++ rangeEnc N))⟩ := by
  rw [init_rg, ← cntT_zero, rgClock, run_add,
    run_range_rounds N out N (le_refl N) false, ite_self]
  have st1 := run_skipDs (cntT N N ++ (jT N N ++ encodeD (out ++ rangeEnc N))) 0 N false
    (fun i hi => ⟨by simpa using cntE_mark_lo N N _ i hi,
                  by simpa using cntE_mark_hi N N _ i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_toRstD (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N N ++ (jT N N ++ encodeD (out ++ rangeEnc N)))
    (cntE_cm_lo N N _ (le_refl N)) (cntE_cm_hi N N _ (le_refl N))
  have st3 := run_healDs N (jT N N ++ encodeD (out ++ rangeEnc N)) false N (le_refl N)
  have st4 := run_two_doneD (s := if N = 0 then false else true) (p := 2 * N)
    (hlE_cm_lo N (jT N N ++ encodeD (out ++ rangeEnc N)))
  rw [run_add, st1, run_add, st2, ← hlT_zero, run_add, st3, st4, hlT_last, cntT_zero, jT_full]

/-- The machine **halts by itself** at its clock. -/
theorem range_halted (N : ℕ) (out : List Bool) :
    rangeMachine.halt
      (run rangeMachine (rgClock N out.length)
        (init rangeMachine (unaryD N ++ (jT N 0 ++ encodeD out)))).st = true := by
  rw [range_run]; rfl

/-- **The range-emitter's output.** -/
theorem range_output (N : ℕ) (out : List Bool) :
    (run rangeMachine (rgClock N out.length)
      (init rangeMachine (unaryD N ++ (jT N 0 ++ encodeD out)))).tp
      = unaryD N ++ (unaryD N ++ encodeD (out ++ rangeEnc N)) := by
  rw [range_run]

/-! ## Polynomial clock bounds -/

theorem subs_le (N Lo j : ℕ) : subs N Lo j ≤ j * (4 * N + 2 * Lo + 2 * j + 10) := by
  induction j with
  | zero => simp [subs]
  | succ j ih => simp only [subs]; nlinarith

/-- The stage bound, atom-preserved. -/
theorem roundClock_le (N L k : ℕ) (hk : k ≤ N) :
    roundClock N L k
      ≤ N * (4 * N + 2 * (L + N * N) + 2 * N + 10) + 6 * N + 2 * (L + N * N) + 6 * N + 20 := by
  have hr : rangeLen k ≤ N * N :=
    le_trans (rangeLen_le k) (Nat.mul_le_mul hk hk)
  have hs : subs N (L + rangeLen k) k
      ≤ N * (4 * N + 2 * (L + N * N) + 2 * N + 10) :=
    le_trans (subs_le N (L + rangeLen k) k)
      (Nat.mul_le_mul hk (by omega))
  rw [roundClock]
  omega

theorem rgRounds_le (N L k : ℕ) (hk : k ≤ N) :
    rgRounds N L k
      ≤ k * (N * (4 * N + 2 * (L + N * N) + 2 * N + 10) + 6 * N + 2 * (L + N * N)
          + 6 * N + 20) := by
  induction k with
  | zero => simp [rgRounds]
  | succ k ih =>
    calc rgRounds N L (k + 1) = rgRounds N L k + roundClock N L k := rfl
      _ ≤ k * (N * (4 * N + 2 * (L + N * N) + 2 * N + 10) + 6 * N + 2 * (L + N * N)
            + 6 * N + 20)
          + (N * (4 * N + 2 * (L + N * N) + 2 * N + 10) + 6 * N + 2 * (L + N * N)
            + 6 * N + 20) :=
        Nat.add_le_add (ih (by omega)) (roundClock_le N L k (by omega))
      _ = (k + 1) * (N * (4 * N + 2 * (L + N * N) + 2 * N + 10) + 6 * N + 2 * (L + N * N)
            + 6 * N + 20) := by ring

/-- **The clock is polynomial** (explicitly quartic: `N` rounds, each seeking over the
quadratically-growing output). -/
theorem rgClock_le (N L : ℕ) :
    rgClock N L
      ≤ N * (N * (4 * N + 2 * (L + N * N) + 2 * N + 10) + 6 * N + 2 * (L + N * N)
          + 6 * N + 20) + (4 * N + 4) := by
  have h := rgRounds_le N L N (le_refl N)
  rw [rgClock]
  omega

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
