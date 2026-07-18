import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLindseyIP

/-!
# INNER PRODUCT is in P: completing the randomized separation

`LindseyIP` proved `IP`'s randomized communication complexity is `Ω(n)` (Lindsey's lemma +
the discrepancy method).  This file supplies the other half: the inner-product predicate is
decided by a polynomial-time machine (`ipLang_inP`), so it is a genuine
`P`-vs-randomized-communication separation (`IP_in_P_but_randomized_hard`).

The machine `ipMachine` scans the same self-delimiting encoding `encPairs` as `eqMachine`, but
carries a running **parity** of `xᵢ ∧ yᵢ` in its state instead of comparing.  It is structurally
identical to `eqMachine` — writes nothing, advances one cell per non-halting step, halts on every
input within `|w|+2` steps — and on a well-formed encoding halts with accept bit `ipVal false`
(the XOR-fold, `ip_run`), which on an encoded `(x, y)` is exactly `IP x y` (`ipLang_encFn`, via the
parity identity `ipVal_spec` and the count bridge `ipCount_zip`).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.IPInP

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (getD_at getD_beyond run_one run_two)
open PallLean.Paper93.DeepMath.PathB.EqInP (encPairs)
open PallLean.Paper93.DeepMath.PathB.RandCommDisc (DistProtocol errμ)
open PallLean.Paper93.DeepMath.PathB.LindseyIP (IP ipCard unif ip_randomized_lb)

/-! ## The parity spec -/

/-- The running XOR-fold of `xᵢ ∧ yᵢ` (the machine's accumulator). -/
def ipVal : Bool → List (Bool × Bool) → Bool
  | p, [] => p
  | p, (a, b) :: rest => ipVal (Bool.xor p (a && b)) rest

/-- The XOR-fold is the parity of the shared-`1` count. -/
theorem ipVal_spec (p : Bool) (pairs : List (Bool × Bool)) :
    ipVal p pairs = Bool.xor p (decide (Odd (pairs.countP (fun q => q.1 && q.2)))) := by
  induction pairs generalizing p with
  | nil => simp [ipVal]
  | cons ab rest ih =>
    obtain ⟨a, b⟩ := ab
    rw [ipVal, ih, List.countP_cons]
    show (Bool.xor (Bool.xor p (a && b)) (decide (Odd (rest.countP (fun q => q.1 && q.2)))))
        = Bool.xor p (decide (Odd (rest.countP (fun q => q.1 && q.2)
            + if (a && b) = true then 1 else 0)))
    cases hab : (a && b)
    · simp
    · have hodd : decide (Odd (rest.countP (fun q => q.1 && q.2) + 1))
          = !decide (Odd (rest.countP (fun q => q.1 && q.2))) := by
        rcases Nat.even_or_odd (rest.countP (fun q => q.1 && q.2)) with he | ho
        · simp [he.add_one, Nat.not_odd_iff_even.mpr he]
        · simp [Nat.not_odd_iff_even.mpr ho.add_one, ho]
      rw [if_pos rfl, hodd]
      cases decide (Odd (rest.countP (fun q => q.1 && q.2))) <;> cases p <;> rfl

/-! ## The machine -/

/-- The inner-product parity machine.  States `0`–`3` scan a `[T,xᵢ,T,yᵢ]` block, XOR-ing `xᵢ∧yᵢ`
into the parity bit; `4` halts (parity stored). -/
def ipMachine : Machine where
  State := Fin 5 × Bool × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false, false)
  halt := fun s => decide (s.1 = 4)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2.1, s.2.2), none, 1) else ((4, s.2.1, s.2.2), none, 2))
    else if s.1 = 1 then ((2, s.2.1, b), none, 1)
    else if s.1 = 2 then (if b then ((3, s.2.1, s.2.2), none, 1) else ((4, s.2.1, s.2.2), none, 2))
    else if s.1 = 3 then ((0, Bool.xor s.2.1 (s.2.2 && b), false), none, 1)
    else ((4, s.2.1, s.2.2), none, 2)
  accept := fun s => s.2.1

theorem step_0_T {par sx : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step ipMachine ⟨(0, par, sx), p, x⟩ = ⟨(1, par, sx), p + 1, x⟩ := by
  simp only [step, ipMachine, h, moveHead]; rfl

theorem step_0_F {par sx : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step ipMachine ⟨(0, par, sx), p, x⟩ = ⟨(4, par, sx), p, x⟩ := by
  simp only [step, ipMachine, h, moveHead]; rfl

theorem step_1 {par sx : Bool} {p : ℕ} {x : List Bool} :
    step ipMachine ⟨(1, par, sx), p, x⟩ = ⟨(2, par, x.getD p false), p + 1, x⟩ := by
  simp only [step, ipMachine, moveHead]; rfl

theorem step_2_T {par sx : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step ipMachine ⟨(2, par, sx), p, x⟩ = ⟨(3, par, sx), p + 1, x⟩ := by
  simp only [step, ipMachine, h, moveHead]; rfl

theorem step_2_F {par sx : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step ipMachine ⟨(2, par, sx), p, x⟩ = ⟨(4, par, sx), p, x⟩ := by
  simp only [step, ipMachine, h, moveHead]; rfl

theorem step_3 {par sx : Bool} {p : ℕ} {x : List Bool} :
    step ipMachine ⟨(3, par, sx), p, x⟩
      = ⟨(0, Bool.xor par (sx && x.getD p false), false), p + 1, x⟩ := by
  simp only [step, ipMachine, moveHead]; rfl

theorem step_4 {par sx : Bool} {p : ℕ} {x : List Bool} :
    step ipMachine ⟨(4, par, sx), p, x⟩ = ⟨(4, par, sx), p, x⟩ :=
  step_of_halted ipMachine (by rfl)

/-! ## No writes -/

theorem ipMachine_no_write (s : Fin 5 × Bool × Bool) (b : Bool) :
    (ipMachine.δ s b).2.1 = none := by
  simp only [ipMachine]
  split_ifs <;> rfl

theorem tape_preserved (c : Cfg ipMachine) : (step ipMachine c).tp = c.tp := by
  unfold step
  by_cases h : ipMachine.halt c.st = true
  · rw [if_pos h]
  · rw [if_neg h]
    show (match (ipMachine.δ c.st (c.tp.getD c.hd false)).2.1 with
      | none => c.tp | some w => writeAt c.tp c.hd w) = c.tp
    rw [ipMachine_no_write]

theorem tape_unchanged (w : List Bool) (t : ℕ) :
    (run ipMachine t (init ipMachine w)).tp = w := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, tape_preserved, ih]

/-! ## One block -/

/-- **One `[T,a,T,b]` block.**  Four steps XOR `a∧b` into the parity and return to state `0`. -/
theorem block_step (P rest_tail : List Bool) (a b par sx : Bool) :
    run ipMachine 4 ⟨(0, par, sx), P.length, P ++ true :: a :: true :: b :: rest_tail⟩
      = ⟨(0, Bool.xor par (a && b), false), P.length + 4,
          P ++ true :: a :: true :: b :: rest_tail⟩ := by
  have g0 : (P ++ true :: a :: true :: b :: rest_tail).getD P.length false = true :=
    getD_at P true _
  have g1 : (P ++ true :: a :: true :: b :: rest_tail).getD (P.length + 1) false = a := by
    rw [show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ true :: a :: true :: b :: rest_tail
        = (P ++ [true]) ++ a :: true :: b :: rest_tail from by simp]
    exact getD_at _ a _
  have g2 : (P ++ true :: a :: true :: b :: rest_tail).getD (P.length + 1 + 1) false = true := by
    rw [show P.length + 1 + 1 = (P ++ [true, a]).length from by simp,
      show P ++ true :: a :: true :: b :: rest_tail
        = (P ++ [true, a]) ++ true :: b :: rest_tail from by simp]
    exact getD_at _ true _
  have g3 : (P ++ true :: a :: true :: b :: rest_tail).getD (P.length + 1 + 1 + 1) false = b := by
    rw [show P.length + 1 + 1 + 1 = (P ++ [true, a, true]).length from by simp,
      show P ++ true :: a :: true :: b :: rest_tail
        = (P ++ [true, a, true]) ++ b :: rest_tail from by simp]
    exact getD_at _ b _
  rw [show run ipMachine 4 ⟨(0, par, sx), P.length, P ++ true :: a :: true :: b :: rest_tail⟩
        = step ipMachine (step ipMachine (step ipMachine (step ipMachine
            ⟨(0, par, sx), P.length, P ++ true :: a :: true :: b :: rest_tail⟩))) from rfl,
    step_0_T g0, step_1, g1, step_2_T g2, step_3, g3]

/-! ## Semantics -/

/-- **The scan.**  From state `0` at the start of `encPairs pairs` with parity `par`, the machine
halts with accept bit `ipVal par pairs`. -/
theorem ip_run (pairs : List (Bool × Bool)) : ∀ (P : List Bool) (par : Bool),
    ∃ t pos, run ipMachine t ⟨(0, par, false), P.length, P ++ encPairs pairs⟩
      = ⟨(4, ipVal par pairs, false), pos, P ++ encPairs pairs⟩ := by
  induction pairs with
  | nil =>
    intro P par
    refine ⟨1, P.length, ?_⟩
    rw [run_one, show P ++ encPairs [] = P ++ false :: [] from rfl, step_0_F (getD_at P false [])]
    rfl
  | cons ab rest ih =>
    intro P par
    obtain ⟨a, b⟩ := ab
    obtain ⟨t', pos', hrec⟩ := ih (P ++ [true, a, true, b]) (Bool.xor par (a && b))
    refine ⟨4 + t', pos', ?_⟩
    rw [run_add, show P ++ encPairs ((a, b) :: rest)
          = P ++ true :: a :: true :: b :: encPairs rest from rfl,
      block_step P (encPairs rest) a b par false,
      show P.length + 4 = (P ++ [true, a, true, b]).length from by simp,
      show P ++ true :: a :: true :: b :: encPairs rest
        = (P ++ [true, a, true, b]) ++ encPairs rest from by simp, hrec,
      show ipVal par ((a, b) :: rest) = ipVal (Bool.xor par (a && b)) rest from rfl,
      show (P ++ [true, a, true, b]) ++ encPairs rest = P ++ encPairs ((a, b) :: rest) from by
        show _ = P ++ true :: a :: true :: b :: encPairs rest; simp]

/-! ## Totality -/

theorem halt_st4 {s : Fin 5 × Bool × Bool} (h : ipMachine.halt s = true) : s.1 = 4 := by
  simp only [ipMachine, decide_eq_true_eq] at h; exact h

theorem halt_of_st4 {s : Fin 5 × Bool × Bool} (h : s.1 = 4) : ipMachine.halt s = true := by
  simp only [ipMachine, decide_eq_true_eq]; exact h

theorem delta_move (s : Fin 5 × Bool × Bool) (b : Bool) :
    (ipMachine.δ s b).1.1 ≠ 4 → (ipMachine.δ s b).2.2 = 1 := by
  simp only [ipMachine]
  split_ifs <;> first | (intro _; rfl) | (intro h; exact absurd rfl h)

theorem step_hd (c : Cfg ipMachine) (h : (step ipMachine c).st.1 ≠ 4) :
    (step ipMachine c).hd = c.hd + 1 := by
  by_cases hnh : ipMachine.halt c.st = true
  · rw [step_of_halted ipMachine hnh] at h
    exact absurd (halt_st4 hnh) h
  · have st_h : (step ipMachine c).st = (ipMachine.δ c.st (c.tp.getD c.hd false)).1 := by
      unfold step; rw [if_neg hnh]
    have hd_h : (step ipMachine c).hd
        = moveHead c.hd (ipMachine.δ c.st (c.tp.getD c.hd false)).2.2 := by
      unfold step; rw [if_neg hnh]
    rw [st_h] at h
    rw [hd_h, delta_move c.st (c.tp.getD c.hd false) h]
    simp [moveHead]

theorem hd_eq (w : List Bool) : ∀ t, (run ipMachine t (init ipMachine w)).st.1 ≠ 4 →
    (run ipMachine t (init ipMachine w)).hd = t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro hne
    have hnt : (run ipMachine t (init ipMachine w)).st.1 ≠ 4 := by
      intro h4
      apply hne
      rw [run_succ, step_of_halted ipMachine (halt_of_st4 h4)]
      exact h4
    rw [run_succ] at hne ⊢
    rw [step_hd (run ipMachine t (init ipMachine w)) hne, ih hnt]

/-- From any padding configuration the machine is halted within two steps. -/
theorem pad_halt (s : Fin 5 × Bool × Bool) (p : ℕ) (w : List Bool)
    (h0 : w.getD p false = false) (h1 : w.getD (p + 1) false = false) :
    ipMachine.halt (run ipMachine 2 ⟨s, p, w⟩).st = true := by
  obtain ⟨q, par, sx⟩ := s
  match q with
  | 0 => rw [run_two, step_0_F h0, step_4]; rfl
  | 1 => rw [run_two, step_1, step_2_F h1]; rfl
  | 2 => rw [run_two, step_2_F h0, step_4]; rfl
  | 3 => rw [run_two, step_3, step_0_F h1]; rfl
  | 4 => rw [run_two, step_4, step_4]; rfl

/-- **Totality.**  The machine halts on every input within `|w| + 2` steps. -/
theorem halts_all (w : List Bool) : HaltsBy ipMachine w (w.length + 2) := by
  by_cases hh : ipMachine.halt (run ipMachine w.length (init ipMachine w)).st = true
  · show ipMachine.halt (run ipMachine (w.length + 2) (init ipMachine w)).st = true
    rw [run_stable ipMachine w (by omega) hh]; exact hh
  · have hne : (run ipMachine w.length (init ipMachine w)).st.1 ≠ 4 := fun h4 =>
      hh (halt_of_st4 h4)
    have hhd := hd_eq w w.length hne
    have htp := tape_unchanged w w.length
    have key := pad_halt (run ipMachine w.length (init ipMachine w)).st
      (run ipMachine w.length (init ipMachine w)).hd
      (run ipMachine w.length (init ipMachine w)).tp
      (by rw [htp, hhd]; exact getD_beyond w w.length (le_refl _))
      (by rw [htp, hhd]; exact getD_beyond w (w.length + 1) (by omega))
    show ipMachine.halt (run ipMachine (w.length + 2) (init ipMachine w)).st = true
    rw [run_add]
    exact key

/-! ## In P -/

/-- The language decided by `ipMachine`. -/
noncomputable def ipLang (w : List Bool) : Bool := decideOut ipMachine w (w.length + 2)

/-- **INNER PRODUCT is in P.** -/
theorem ipLang_inP : InP ipLang :=
  ⟨ipMachine, fun m => m + 2, ⟨3, 1, fun n => by
    show n + 2 ≤ 3 * (n + 1) ^ 1
    have : (n + 1) ^ 1 = n + 1 := pow_one _
    omega⟩, fun w => ⟨halts_all w, rfl⟩⟩

/-- On a well-formed encoding, the language is `ipVal false`: the parity of shared `1`-coordinates. -/
theorem ipLang_enc (pairs : List (Bool × Bool)) : ipLang (encPairs pairs) = ipVal false pairs := by
  obtain ⟨t, pos, hrun⟩ := ip_run pairs [] false
  simp only [List.length_nil, List.nil_append] at hrun
  show decideOut ipMachine (encPairs pairs) ((encPairs pairs).length + 2) = ipVal false pairs
  unfold decideOut
  rcases le_total t ((encPairs pairs).length + 2) with hle | hle
  · rw [run_stable ipMachine (encPairs pairs) hle
      (by show ipMachine.halt (run ipMachine t ⟨(0, false, false), 0, encPairs pairs⟩).st = true
          rw [hrun]; rfl)]
    show ipMachine.accept (run ipMachine t ⟨(0, false, false), 0, encPairs pairs⟩).st = ipVal false pairs
    rw [hrun]; rfl
  · rw [← run_stable ipMachine (encPairs pairs) hle (halts_all (encPairs pairs))]
    show ipMachine.accept (run ipMachine t ⟨(0, false, false), 0, encPairs pairs⟩).st = ipVal false pairs
    rw [hrun]; rfl

/-! ## The bridge to INNER PRODUCT -/

/-- `countP` over `ofFn` is the corresponding `Finset` filter cardinality. -/
theorem countP_ofFn {α : Type} {n : ℕ} (g : Fin n → α) (p : α → Bool) :
    (List.ofFn g).countP p = (Finset.univ.filter (fun i => p (g i) = true)).card := by
  have hsum : ∀ l : List α, l.countP p = (l.map (fun a => if p a then 1 else 0)).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.countP_cons, List.map_cons, List.sum_cons, ih]; omega
  rw [hsum, List.map_ofFn, List.sum_ofFn, Finset.card_filter]
  rfl

/-- Zipping two `ofFn` lists pairs coordinatewise. -/
theorem zip_ofFn_eq {n : ℕ} (x y : Fin n → Bool) :
    (List.ofFn x).zip (List.ofFn y) = List.ofFn (fun i => (x i, y i)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zip, List.getElem_ofFn]

/-- The shared-`1` count of the encoded pair is `ipCard`. -/
theorem ipCount_zip {n : ℕ} (x y : Fin n → Bool) :
    ((List.ofFn x).zip (List.ofFn y)).countP (fun q => q.1 && q.2) = ipCard x y := by
  rw [zip_ofFn_eq, countP_ofFn]
  rfl

/-- **The encoded-input bridge.**  On the encoding of `(x, y)`, the language is exactly `IP x y`. -/
theorem ipLang_encFn {n : ℕ} (x y : Fin n → Bool) :
    ipLang (encPairs ((List.ofFn x).zip (List.ofFn y))) = IP x y := by
  rw [ipLang_enc, ipVal_spec, ipCount_zip, Bool.false_xor]
  rfl

/-- **INNER PRODUCT: in P, but linear randomized communication.**  The inner-product predicate is
decided in polynomial time (`ipLang_inP`), yet its communication function `IP` needs `Ω(n)` bits of
*randomized* (bounded-error) communication (`ip_randomized_lb`, via Lindsey's lemma): a `c`-bit
protocol with uniform-error `≤ ε` forces `1 − 2ε ≤ 2^c · 2^{-n/2}`.  Polynomial time does not imply
sublinear randomized communication. -/
theorem IP_in_P_but_randomized_hard :
    InP ipLang
      ∧ (∀ (n : ℕ) (x y : Fin n → Bool),
          ipLang (encPairs ((List.ofFn x).zip (List.ofFn y))) = IP x y)
      ∧ ∀ (n c : ℕ) (P : DistProtocol (Fin n → Bool) (Fin n → Bool) (2 ^ c)) (ε : ℝ),
          errμ P IP unif ≤ ε → 1 - 2 * ε ≤ (2 ^ c : ℕ) * Real.sqrt (((2 : ℝ) ^ n)⁻¹) :=
  ⟨ipLang_inP, fun _ x y => ipLang_encFn x y, fun _ c P ε hε => ip_randomized_lb c P ε hε⟩

end PallLean.Paper93.DeepMath.PathB.IPInP
