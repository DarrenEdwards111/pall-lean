import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSelectorMonotone

/-!
# N-Frame: DAG wire surgery — sharing-aware gate elimination and the circuit one-kill schedule

The observer-taxonomy step 2: from tree observers to the DAG/`cbudget` observer.  The question was exact — *when
fixing a variable, how many DAG gates die despite reuse?*  This file builds the actual surgery and answers with
the honest rate:

  `substGateC` / `computes_subst` / `cbudget_restrict_le` — **PROVED**: variables enter circuits only through
        `var` gates, so restriction is a pure gate-map — `cbudget` never increases under restriction.
  `elimGate` / `runFrom_elim` / `computes_elim` — **PROVED, the wire surgery**: deleting a constant gate at
        position `p` re-indexes every later reference (`elimRef`) and *absorbs* the constant into every reader —
        in either operand position, including double reads (`bin op p p`) — despite arbitrary fan-out.  The
        simulation invariant is `eraseIdx`: the new wire list is the old one with wire `p` removed.
  `cbudget_onekill` — **PROVED, the DAG one-kill**: if `f` depends on `xᵢ` and the restriction is not constant,
        fixing `xᵢ` kills a gate — the forced `var i` gate becomes the deletable constant.
  `cbudget_livechain` — **PROVED, the engine**: a dependence-live restriction schedule of length `L` forces
        `L ≤ cbudget f` — gate elimination iterated through the sharing.
  `sat3_cbudget_wire_surgery` — **PROVED, the record**:

        `m·v + (m−2) ≤ cbudget (sat3Family N)`

        — the selector schedule continues into the sign bits, strictly beating the dependency-count record
        `m·v` (`sat3_cbudget_lb`): the first sat3 circuit bound past variable counting.

## Honest scope

One kill per step is the honest DAG rate at this rung: the tree mechanisms do **not** transfer — a single
`var i` gate fans out, recombines, and computes xor-like behavior in any basis, so the polarity/orientation
route and the `¬TopDecomp` two-kill have no DAG analogue here, and none is claimed.  The classical ladder past
one-per-step is Schnorr/Stockmeyer-style case analysis (`2n`, `2.5n`, `3n−o(n)`, …) — named, open rungs.  The
schedule itself can grow: zeroing slot-1 and slot-0 selectors down to one live literal per clause and ending in
the all-equal-signs endgame should reach `~3·m·v ≈ N` steps — a named next rung needing new witness families.
Superlinear `cbudget` for an explicit function is the field's wall, untouched.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Index bookkeeping for a deleted wire -/

/-- Re-index a wire reference after deleting position `p`. -/
def elimRef (p j : ℕ) : ℕ := if j < p then j else j - 1

theorem getD_eraseIdx_ge (l : List Bool) (p j : ℕ) (hj : p ≤ j) :
    (l.eraseIdx p).getD j false = l.getD (j + 1) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx,
    if_neg (by omega)]

theorem getD_eraseIdx_elimRef (l : List Bool) (p j : ℕ) (hj : j ≠ p) :
    (l.eraseIdx p).getD (elimRef p j) false = l.getD j false := by
  by_cases h : j < p
  · rw [show elimRef p j = j from if_pos h]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx,
      if_pos h]
  · rw [show elimRef p j = j - 1 from if_neg h]
    rw [getD_eraseIdx_ge l p (j - 1) (by omega)]
    rw [show j - 1 + 1 = j by omega]

/-! ### Restriction is a pure gate-map: `cbudget` never increases -/

/-- Substitute `xᵢ := b`: replace every `var i` gate by the constant. -/
def substGateC {n : ℕ} (i : Fin n) (b : Bool) : CGate n → CGate n
  | .var j => if j = i then .cst b else .var j
  | .cst c => .cst c
  | .un op j => .un op j
  | .bin op j k => .bin op j k

theorem evalGate_subst {n : ℕ} (x : Fin n → Bool) (i : Fin n) (b : Bool)
    (vals : List Bool) (g : CGate n) :
    evalGate x vals (substGateC i b g) = evalGate (Function.update x i b) vals g := by
  cases g with
  | var j =>
    show evalGate x vals (if j = i then CGate.cst b else CGate.var j)
        = Function.update x i b j
    by_cases hj : j = i
    · rw [if_pos hj, hj, Function.update_self]
      rfl
    · rw [if_neg hj, Function.update_of_ne hj]
      rfl
  | cst c => rfl
  | un op j => rfl
  | bin op j k => rfl

theorem runFrom_subst {n : ℕ} (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool),
      runFrom x vals (gs.map (substGateC i b)) = runFrom (Function.update x i b) vals gs := by
  intro gs
  induction gs with
  | nil => intro vals; rfl
  | cons g rest ih =>
    intro vals
    show runFrom x (vals ++ [evalGate x vals (substGateC i b g)]) (rest.map (substGateC i b))
        = runFrom (Function.update x i b)
          (vals ++ [evalGate (Function.update x i b) vals g]) rest
    rw [evalGate_subst x i b vals g]
    exact ih _

/-- **Restriction at the circuit level (proved)**: the substituted circuit computes the restricted function with
the same gate count. -/
theorem computes_subst {n : ℕ} (c : List (CGate n)) (f : (Fin n → Bool) → Bool)
    (i : Fin n) (b : Bool) (hcomp : computes c f) :
    computes (c.map (substGateC i b)) (restrictF f i b) := by
  intro x
  show (runFrom x [] (c.map (substGateC i b))).getD
      ((c.map (substGateC i b)).length - 1) false = f (Function.update x i b)
  rw [runFrom_subst x i b c [], List.length_map]
  exact hcomp (Function.update x i b)

theorem cbudget_set_nonempty {n : ℕ} (f : (Fin n → Bool) → Bool) :
    {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}.Nonempty := by
  refine ⟨(compile 0 (dnfFor f)).length, compile 0 (dnfFor f), ?_, rfl⟩
  have := compile_computes (dnfFor f)
  rwa [show (fun x => eval (dnfFor f) x) = f from funext (fun x => by rw [eval_dnfFor])] at this

/-- **Restriction never increases the circuit energy (proved).** -/
theorem cbudget_restrict_le {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool) :
    cbudget (restrictF f i b) ≤ cbudget f := by
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem (cbudget_set_nonempty f)
  have hlen' : c.length = cbudget f := hlen
  have hb : cbudget (restrictF f i b) ≤ (c.map (substGateC i b)).length :=
    Nat.sInf_le ⟨c.map (substGateC i b), computes_subst c f i b hcomp, rfl⟩
  rw [List.length_map] at hb
  omega

/-! ### The wire surgery: deleting a constant gate despite fan-out -/

/-- Rewire one gate after deleting the constant wire `p` (value `b`): references to `p` absorb the constant —
in either operand position, including double reads — and later references shift down. -/
def elimGate {n : ℕ} (p : ℕ) (b : Bool) : CGate n → CGate n
  | .var i => .var i
  | .cst c => .cst c
  | .un op j => if j = p then .cst (op b) else .un op (elimRef p j)
  | .bin op j k =>
      if j = p then
        (if k = p then .cst (op b b) else .un (fun c => op b c) (elimRef p k))
      else if k = p then .un (fun a => op a b) (elimRef p j)
      else .bin op (elimRef p j) (elimRef p k)

theorem evalGate_elim {n : ℕ} (x : Fin n → Bool) (vals : List Bool) (p : ℕ) (b : Bool)
    (hp : vals.getD p false = b) (g : CGate n) :
    evalGate x (vals.eraseIdx p) (elimGate p b g) = evalGate x vals g := by
  cases g with
  | var i => rfl
  | cst c => rfl
  | un op j =>
    show evalGate x (vals.eraseIdx p)
        (if j = p then CGate.cst (op b) else CGate.un op (elimRef p j))
        = op (vals.getD j false)
    by_cases hj : j = p
    · rw [if_pos hj]
      show op b = op (vals.getD j false)
      rw [hj, hp]
    · rw [if_neg hj]
      show op ((vals.eraseIdx p).getD (elimRef p j) false) = op (vals.getD j false)
      rw [getD_eraseIdx_elimRef vals p j hj]
  | bin op j k =>
    show evalGate x (vals.eraseIdx p)
        (if j = p then
          (if k = p then CGate.cst (op b b) else CGate.un (fun c => op b c) (elimRef p k))
        else if k = p then CGate.un (fun a => op a b) (elimRef p j)
        else CGate.bin op (elimRef p j) (elimRef p k))
        = op (vals.getD j false) (vals.getD k false)
    by_cases hj : j = p
    · by_cases hk : k = p
      · rw [if_pos hj, if_pos hk]
        show op b b = op (vals.getD j false) (vals.getD k false)
        rw [hj, hk, hp]
      · rw [if_pos hj, if_neg hk]
        show op b ((vals.eraseIdx p).getD (elimRef p k) false)
            = op (vals.getD j false) (vals.getD k false)
        rw [hj, hp, getD_eraseIdx_elimRef vals p k hk]
    · by_cases hk : k = p
      · rw [if_neg hj, if_pos hk]
        show op ((vals.eraseIdx p).getD (elimRef p j) false) b
            = op (vals.getD j false) (vals.getD k false)
        rw [hk, hp, getD_eraseIdx_elimRef vals p j hj]
      · rw [if_neg hj, if_neg hk]
        show op ((vals.eraseIdx p).getD (elimRef p j) false)
            ((vals.eraseIdx p).getD (elimRef p k) false)
            = op (vals.getD j false) (vals.getD k false)
        rw [getD_eraseIdx_elimRef vals p j hj, getD_eraseIdx_elimRef vals p k hk]

/-- **The simulation invariant (proved)**: running the rewired gates on the shortened wire list produces exactly
the old wire list with wire `p` removed. -/
theorem runFrom_elim {n : ℕ} (x : Fin n → Bool) (p : ℕ) (b : Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool), p < vals.length → vals.getD p false = b →
      runFrom x (vals.eraseIdx p) (gs.map (elimGate p b)) = (runFrom x vals gs).eraseIdx p := by
  intro gs
  induction gs with
  | nil => intro vals _ _; rfl
  | cons g rest ih =>
    intro vals hp hb
    show runFrom x (vals.eraseIdx p ++ [evalGate x (vals.eraseIdx p) (elimGate p b g)])
        (rest.map (elimGate p b))
        = (runFrom x (vals ++ [evalGate x vals g]) rest).eraseIdx p
    rw [evalGate_elim x vals p b hb g]
    rw [← List.eraseIdx_append_of_lt_length hp [evalGate x vals g]]
    exact ih (vals ++ [evalGate x vals g])
      (by rw [List.length_append]; show p < vals.length + 1; omega)
      (by rw [List.getD_append vals [evalGate x vals g] false p hp]; exact hb)

/-- **The wire surgery (proved)**: a non-final constant gate can be deleted — every reader absorbs the constant,
every later reference shifts, and the circuit still computes `f` with one gate fewer. -/
theorem computes_elim {n : ℕ} (c₁ c₂ : List (CGate n)) (b : Bool)
    (f : (Fin n → Bool) → Bool)
    (hcomp : computes (c₁ ++ CGate.cst b :: c₂) f) (hne : c₂ ≠ []) :
    computes (c₁ ++ c₂.map (elimGate c₁.length b)) f := by
  have hc2 : 1 ≤ c₂.length := by
    cases c₂ with
    | nil => exact absurd rfl hne
    | cons g rest => show 1 ≤ rest.length + 1; omega
  intro x
  have hx := hcomp x
  have hV : (runFrom x [] c₁).length = c₁.length := by
    rw [runFrom_length]
    simp
  have hsplit : runFrom x [] (c₁ ++ CGate.cst b :: c₂)
      = runFrom x (runFrom x [] c₁ ++ [b]) c₂ := by
    rw [show c₁ ++ CGate.cst b :: c₂ = (c₁ ++ [CGate.cst b]) ++ c₂ by simp, runFrom_append,
      runFrom_append]
    rfl
  have hVe : (runFrom x [] c₁ ++ [b]).eraseIdx c₁.length = runFrom x [] c₁ := by
    rw [List.eraseIdx_append_of_length_le (le_of_eq hV) [b]]
    rw [show c₁.length - (runFrom x [] c₁).length = 0 by omega]
    rw [show ([b] : List Bool).eraseIdx 0 = ([] : List Bool) from rfl, List.append_nil]
  have hnew : runFrom x (runFrom x [] c₁) (c₂.map (elimGate c₁.length b))
      = (runFrom x (runFrom x [] c₁ ++ [b]) c₂).eraseIdx c₁.length := by
    have h1 := runFrom_elim x c₁.length b c₂ (runFrom x [] c₁ ++ [b])
      (by rw [List.length_append, hV]; show c₁.length < c₁.length + 1; omega)
      (by rw [show c₁.length = (runFrom x [] c₁).length from hV.symm]; exact getD_concat _ _)
    rw [hVe] at h1
    exact h1
  show (runFrom x [] (c₁ ++ c₂.map (elimGate c₁.length b))).getD
      ((c₁ ++ c₂.map (elimGate c₁.length b)).length - 1) false = f x
  rw [runFrom_append, hnew]
  rw [show (c₁ ++ c₂.map (elimGate c₁.length b)).length = c₁.length + c₂.length by
    rw [List.length_append, List.length_map]]
  rw [getD_eraseIdx_ge _ c₁.length (c₁.length + c₂.length - 1) (by omega)]
  rw [show c₁.length + c₂.length - 1 + 1 = c₁.length + c₂.length by omega]
  have hxold : (runFrom x (runFrom x [] c₁ ++ [b]) c₂).getD
      ((c₁ ++ CGate.cst b :: c₂).length - 1) false = f x := by
    rw [← hsplit]
    exact hx
  rw [show (c₁ ++ CGate.cst b :: c₂).length - 1 = c₁.length + c₂.length by
    rw [List.length_append, List.length_cons]; omega] at hxold
  exact hxold

/-! ### The DAG one-kill -/

theorem output_last_var {n : ℕ} (c₁ : List (CGate n)) (i : Fin n) (x : Fin n → Bool) :
    output (c₁ ++ [CGate.var i]) x = x i := by
  show (runFrom x [] (c₁ ++ [CGate.var i])).getD
      ((c₁ ++ [CGate.var i]).length - 1) false = x i
  rw [runFrom_append]
  show ((runFrom x [] c₁) ++ [evalGate x (runFrom x [] c₁) (CGate.var i)]).getD
      ((c₁ ++ [CGate.var i]).length - 1) false = x i
  have hV : (runFrom x [] c₁).length = c₁.length := by
    rw [runFrom_length]
    simp
  rw [show (c₁ ++ [CGate.var i]).length - 1 = (runFrom x [] c₁).length by
    rw [List.length_append, hV]
    show c₁.length + 1 - 1 = c₁.length
    omega]
  exact getD_concat _ _

/-- **THE DAG ONE-KILL (proved)**: if `f` depends on `xᵢ` and its restriction is not constant, fixing `xᵢ` kills
a gate — the forced `var i` gate becomes a constant, and the surgery deletes it through any fan-out. -/
theorem cbudget_onekill {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (hdep : DependsOnF f i)
    (hnc : ∃ u w : Fin n → Bool, restrictF f i b u ≠ restrictF f i b w) :
    cbudget (restrictF f i b) + 1 ≤ cbudget f := by
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem (cbudget_set_nonempty f)
  have hlen' : c.length = cbudget f := hlen
  obtain ⟨x₁, x₀, hd, hnev⟩ := hdep
  have hvar : CGate.var i ∈ c := depends_var_mem c f hcomp i x₁ x₀ hd hnev
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hvar
  cases t with
  | nil =>
    -- the output gate is `var i`: the restriction is the constant `b`, contradicting `hnc`
    exfalso
    have hfx : ∀ y, f y = y i := by
      intro y
      rw [← hcomp y]
      exact output_last_var s i y
    obtain ⟨u, w, hne'⟩ := hnc
    apply hne'
    show f (Function.update u i b) = f (Function.update w i b)
    rw [hfx, hfx, Function.update_self, Function.update_self]
  | cons g rest =>
    have hsub := computes_subst (s ++ CGate.var i :: g :: rest) f i b hcomp
    have hmap : (s ++ CGate.var i :: g :: rest).map (substGateC i b)
        = s.map (substGateC i b)
          ++ CGate.cst b :: (g :: rest).map (substGateC i b) := by
      rw [List.map_append, List.map_cons]
      show s.map (substGateC i b) ++ (if i = i then CGate.cst b else CGate.var i)
          :: (g :: rest).map (substGateC i b) = _
      rw [if_pos rfl]
    rw [hmap] at hsub
    have hne2 : (g :: rest).map (substGateC i b) ≠ [] := by
      rw [List.map_cons]
      exact List.cons_ne_nil _ _
    have helim := computes_elim (s.map (substGateC i b)) ((g :: rest).map (substGateC i b))
      b (restrictF f i b) hsub hne2
    have hb : cbudget (restrictF f i b)
        ≤ (s.map (substGateC i b) ++ ((g :: rest).map (substGateC i b)).map
            (elimGate (s.map (substGateC i b)).length b)).length :=
      Nat.sInf_le ⟨_, helim, rfl⟩
    rw [List.length_append, List.length_map, List.length_map, List.length_map] at hb
    have hclen : (s ++ CGate.var i :: g :: rest).length
        = s.length + ((g :: rest).length + 1) := by
      rw [List.length_append, List.length_cons]
    omega

/-! ### The one-kill engine over live schedules -/

theorem cbudget_pos_of_dep {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (hdep : DependsOnF f i) : 1 ≤ cbudget f := by
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem (cbudget_set_nonempty f)
  have hlen' : c.length = cbudget f := hlen
  obtain ⟨x₁, x₀, -, hnev⟩ := hdep
  cases c with
  | nil =>
    exfalso
    apply hnev
    rw [← hcomp x₁, ← hcomp x₀]
    rfl
  | cons g rest =>
    rw [← hlen']
    show 1 ≤ (g :: rest).length
    rw [List.length_cons]
    omega

/-- **The engine (proved)**: a dependence-live restriction schedule forces one gate per step. -/
theorem cbudget_livechain {n : ℕ} :
    ∀ (steps : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool),
      LiveChain f steps → steps.length ≤ cbudget f := by
  intro steps
  induction steps with
  | nil => intro f _; exact Nat.zero_le _
  | cons s rest ih =>
    intro f h
    have h' : DependsOnF f s.1 ∧ LiveChain (restrictF f s.1 s.2) rest := h
    obtain ⟨hdep, hchain⟩ := h'
    cases rest with
    | nil =>
      show 1 ≤ cbudget f
      exact cbudget_pos_of_dep f s.1 hdep
    | cons s' rest' =>
      have h'' : DependsOnF (restrictF f s.1 s.2) s'.1 ∧
          LiveChain (restrictF (restrictF f s.1 s.2) s'.1 s'.2) rest' := hchain
      have hnc : ∃ u w, restrictF f s.1 s.2 u ≠ restrictF f s.1 s.2 w := by
        obtain ⟨⟨y₁, y₀, -, hnev⟩, -⟩ := h''
        exact ⟨y₁, y₀, hnev⟩
      have hkill := cbudget_onekill f s.1 s.2 hdep hnc
      have hih : (s' :: rest').length ≤ cbudget (restrictF f s.1 s.2) :=
        ih (restrictF f s.1 s.2) hchain
      have hihlen : rest'.length + 1 ≤ cbudget (restrictF f s.1 s.2) := hih
      show rest'.length + 1 + 1 ≤ cbudget f
      omega

theorem liveChain_of_twoKillChain {n : ℕ} :
    ∀ (steps : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool),
      TwoKillChain f steps → LiveChain f steps := by
  intro steps
  induction steps with
  | nil => intro f _; trivial
  | cons s rest ih =>
    intro f h
    have h' : DependsOnF f s.1 ∧ ¬TopDecomp f s.1 ∧
        TwoKillChain (restrictF f s.1 s.2) rest := h
    exact ⟨h'.1, ih (restrictF f s.1 s.2) h'.2.2⟩

theorem liveChain_append {n : ℕ} :
    ∀ (L₁ L₂ : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool),
      LiveChain f L₁ → LiveChain (restrictAll f L₁) L₂ → LiveChain f (L₁ ++ L₂) := by
  intro L₁
  induction L₁ with
  | nil => intro L₂ f _ h2; exact h2
  | cons s rest ih =>
    intro L₂ f h1 h2
    have h1' : DependsOnF f s.1 ∧ LiveChain (restrictF f s.1 s.2) rest := h1
    exact ⟨h1'.1, ih L₂ (restrictF f s.1 s.2) h1'.2 h2⟩

/-! ### The SAT schedule continues into the sign bits -/

/-- **Dependence survives the whole interleave (proved)**: with all slot-2 selectors zeroed and any interior
sign prefix frozen, every remaining interior sign bit is still live — the identity context is a dependence pair
inside the frozen cube. -/
theorem sat3_interleave_dependsOn (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (S : List (Fin (sat3M N))) (hS : ∀ c' ∈ S, 1 ≤ c'.val ∧ c'.val ≤ sat3M N - 2)
    (c : Fin (sat3M N)) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ sat3M N - 2) (hcS : c ∉ S) :
    DependsOnF (restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S))
      (sat3SignBit N c) := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvj
  have hcomp : ∀ a : Bool, ∀ p ∈ sat3SelSteps N ++ sat3SignFreeze N S,
      Function.update (sat3Patch N c (sat3Context N c hk (fun _ => false))
        (sat3Probe N vj false)) (sat3SignBit N c) a p.1 = p.2 := by
    intro a p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      show Function.update (sat3Patch N c (sat3Context N c hk (fun _ => false))
        (sat3Probe N vj false)) (sat3SignBit N c) a (sat3S2Sel N q.1 q.2) = false
      rw [Function.update_of_ne (sat3S2Sel_ne_signBit N q.1 q.2 c)]
      exact sat3_context_s2_false N hk hkv c (fun _ => false) vj false q.1 q.2
    · obtain ⟨c', hc'S, rfl⟩ := List.mem_map.mp hp
      obtain ⟨hc'1, hc'2⟩ := hS c' hc'S
      have hnec : c' ≠ c := fun h => hcS (h ▸ hc'S)
      show Function.update (sat3Patch N c (sat3Context N c hk (fun _ => false))
        (sat3Probe N vj false)) (sat3SignBit N c) a (sat3SignBit N c') = true
      rw [Function.update_of_ne (sat3SignBit_ne N hnec)]
      exact sat3_freeze_compliant N hk hkv c c' hnec hc1 hc2 hc'1 hc'2 (fun _ => false)
        (fun j _ => rfl) _
  have hbeh₁ : ∀ a : Bool,
      restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S)
        (Function.update (sat3Patch N c (sat3Context N c hk (fun _ => false))
          (sat3Probe N vj false)) (sat3SignBit N c) a) = a := by
    intro a
    rw [restrictAll_agree _ _ _ (hcomp a), patch_probe_update]
    have hval := sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl a
    rw [hval]
    cases a <;> rfl
  refine ⟨Function.update (sat3Patch N c (sat3Context N c hk (fun _ => false))
      (sat3Probe N vj false)) (sat3SignBit N c) true,
    Function.update (sat3Patch N c (sat3Context N c hk (fun _ => false))
      (sat3Probe N vj false)) (sat3SignBit N c) false, ?_, ?_⟩
  · intro cc hcc
    by_contra hne
    apply hcc
    rw [Function.update_of_ne hne, Function.update_of_ne hne]
  · rw [hbeh₁ true, hbeh₁ false]
    decide

/-- The sign-bit continuation is a live chain over the selector-zeroed function. -/
theorem sat3_sign_livechain (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N) :
    ∀ (L S : List (Fin (sat3M N))),
      (∀ c ∈ S, 1 ≤ c.val ∧ c.val ≤ sat3M N - 2) →
      (∀ c ∈ L, 1 ≤ c.val ∧ c.val ≤ sat3M N - 2) →
      (∀ c ∈ L, c ∉ S) → L.Nodup →
      LiveChain (restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S))
        (L.map (fun c => (sat3SignBit N c, true))) := by
  intro L
  induction L with
  | nil => intro S _ _ _ _; trivial
  | cons c L' ih =>
    intro S hS hL hLS hnd
    have hc := hL c List.mem_cons_self
    have hcS : c ∉ S := hLS c List.mem_cons_self
    refine ⟨sat3_interleave_dependsOn N hv hm3 S hS c hc.1 hc.2 hcS, ?_⟩
    have hres : restrictF
        (restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S))
        (sat3SignBit N c) true
        = restrictAll (sat3Family N)
            (sat3SelSteps N ++ sat3SignFreeze N (S ++ [c])) := by
      rw [sat3SignFreeze_append, ← List.append_assoc,
        restrictAll_append (sat3SelSteps N ++ sat3SignFreeze N S)
          (sat3SignFreeze N [c]) (sat3Family N)]
      rfl
    rw [hres]
    have hS' : ∀ c' ∈ S ++ [c], 1 ≤ c'.val ∧ c'.val ≤ sat3M N - 2 := by
      intro c' hc'
      rcases List.mem_append.mp hc' with h | h
      · exact hS c' h
      · rw [List.mem_singleton] at h
        exact h ▸ hc
    have hL' : ∀ c' ∈ L', 1 ≤ c'.val ∧ c'.val ≤ sat3M N - 2 :=
      fun c' hc' => hL c' (List.mem_cons_of_mem c hc')
    have hLS' : ∀ c' ∈ L', c' ∉ S ++ [c] := by
      intro c' hc' hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hLS c' (List.mem_cons_of_mem c hc') h
      · rw [List.mem_singleton] at h
        subst h
        exact (List.nodup_cons.mp hnd).1 hc'
    have hnd' : L'.Nodup := (List.nodup_cons.mp hnd).2
    exact ih (S ++ [c]) hS' hL' hLS' hnd'

/-- **THE DAG RECORD (proved)**: `m·v + (m−2) ≤ cbudget (sat3Family N)` — the wire-surgery engine runs the
selector schedule and continues into the sign bits, strictly beating the dependency-count record `m·v`. -/
theorem sat3_cbudget_wire_surgery (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N) :
    sat3M N * sat3V N + (sat3M N - 2) ≤ cbudget (sat3Family N) := by
  have hsel : LiveChain (sat3Family N) (sat3SelSteps N) :=
    liveChain_of_twoKillChain (sat3SelSteps N) (sat3Family N)
      (sat3_selector_chain N hv (by omega))
  have hinj : Function.Injective
      (fun j : Fin (sat3M N - 2) =>
        (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (sat3M N))) := by
    intro j j' h
    have hval : j.val + 1 = j'.val + 1 := congrArg Fin.val h
    exact Fin.ext (by omega)
  have hsign := sat3_sign_livechain N hv hm3
    ((List.finRange (sat3M N - 2)).map
      (fun j : Fin (sat3M N - 2) =>
        (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (sat3M N))))
    []
    (fun c hc => absurd hc List.not_mem_nil)
    (by
      intro c hc
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
      have := j.isLt
      constructor
      · show 1 ≤ j.val + 1
        omega
      · show j.val + 1 ≤ sat3M N - 2
        omega)
    (fun c _ hc => absurd hc List.not_mem_nil)
    ((List.nodup_finRange _).map hinj)
  have hnil : sat3SelSteps N ++ sat3SignFreeze N ([] : List (Fin (sat3M N)))
      = sat3SelSteps N := List.append_nil _
  rw [hnil] at hsign
  have hfull := liveChain_append (sat3SelSteps N) _ (sat3Family N) hsel hsign
  have hlen := cbudget_livechain _ (sat3Family N) hfull
  rw [List.length_append, sat3SelSteps_length, List.length_map, List.length_map,
    List.length_finRange] at hlen
  exact hlen

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.computes_subst
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_restrict_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.runFrom_elim
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.computes_elim
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_onekill
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_livechain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_interleave_dependsOn
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_wire_surgery
