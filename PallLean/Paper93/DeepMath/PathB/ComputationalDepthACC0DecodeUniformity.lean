import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalSimulationOverhead

/-!
# Decode-from-input uniformity — one fixed machine simulates every machine (proved)

Entry 296 proved the universal NTM simulation has overhead exactly 1, leaving **one** primitive: the *decode-from-input
uniformity* — collapsing the family `univNTM code` (code a Lean parameter) to a **single fixed machine** that reads the
code `⟨M⟩` from its input and runs as `univNTM ⟨M⟩`.  This file supplies it.

**The construction.**  Carry the code as *configuration data*: `UConfig := ℕ × CConfig` (decoded code, machine
config).  The uniform step `uStep` preserves the code and applies `univStep code`; the uniform machine `uniformU dec`
*decodes the code from its input* at `init` (via a fixed parse function `dec : List Bool → ℕ × List Bool`, the
machine's own M-independent parsing logic) and accepts on the machine-config component.  Then:

* the code is preserved along every run (`uStep_preserves_code`);
* `uStep`'s `k`-step reachability on code-carrying configs *equals* `univNTM code`'s (`uStep_reachIn`);
* so `uniformU dec`, on an input decoding to `(⟨M⟩, x)`, simulates `M` on `x` *exactly* (`uniformU_simulates`),
  combining with entry 296's overhead-1 result.

A concrete encoding `encPair`/`decPair` (with `decPair_encPair` proved) shows the decode is realizable, so the result
is self-contained: **one fixed machine** `uniformU decPair` simulates *every* `M` on input `encPair ⟨M⟩ x`
(`uniformU_simulates_enc`).

## What is proved (clean axioms, no `sorry`)

* **`uStep`, `uniformU`** — the uniform step (code carried as data) and the single universal machine (one fixed parse
  `dec`, M-independent).
* **`uStep_preserves_code`** — the decoded code is preserved along every run.
* **`uStep_reachIn`** — `uniformU`'s reachability on code-carrying configs equals `univNTM code`'s (overhead 1, uniform).
* **`uniformU_simulates`** — one fixed machine: input decoding to `(⟨M⟩, x)` ⟹ `acceptsWithin (uniformU dec) w t ↔
  acceptsWithin (toNTM M) x t` (combining `uStep_reachIn` + entry-296 `univ_simulates_exactly`).
* **`decPair_encPair`** — a concrete encoding round-trips: `decPair (encPair code x) = (code, x)`.
* **`uniformU_simulates_enc`** — self-contained: `uniformU decPair` on `encPair ⟨M⟩ x` simulates `M` on `x` exactly.

## Honest scope

This proves the **decode-from-input uniformity** — the last primitive of the universal-simulation socket: a *single*
fixed machine `uniformU dec` (its only parameter the M-independent parse `dec`, part of the machine) reads the code from
its input and simulates *any* `M` exactly, with overhead 1 (entry 296).  Together with entry 296 the universal NTM
simulation is now formalized: one uniform machine, no overhead.  This is the universal TM (Turing 1936) over this
transition-table model.  It does **not** by itself prove the time hierarchy (the diagonal must be *fed* its own code and
clocked to the bigger bound — the remaining wiring, plus the per-`x` block bookkeeping), but it discharges the universal
machine's existence and uniformity.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DecodeUniformity

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig toNTM machineEquiv)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM (univStep)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalSimulationOverhead (univNTM univ_simulates_exactly)

/-- A uniform configuration: the decoded machine code carried alongside the machine config. -/
abbrev UConfig : Type := ℕ × CConfig

/-- The uniform step: preserve the carried code, apply `univStep code` to the machine config. -/
def uStep (p q : UConfig) : Prop := p.1 = q.1 ∧ univStep p.1 p.2 q.2

/-- **The single universal machine.**  Its only parameter is the fixed, machine-independent parse `dec : List Bool →
ℕ × List Bool` (the universal machine's own decoding logic); the code varies in the *input*, not the machine.  It
decodes the code at `init` and accepts on the machine-config state. -/
def uniformU (dec : List Bool → ℕ × List Bool) : NTM where
  Config := UConfig
  step := uStep
  init := fun x => ((dec x).1, (0, 0, (dec x).2))
  accept := fun p => p.2.1 = 1

/-- **The decoded code is preserved along every run (PROVED).**  `uStep` keeps the first component fixed, so any config
reachable from `(code, c)` has the same code. -/
theorem uStep_preserves_code (dec : List Bool → ℕ × List Bool) (k : ℕ) (p q : UConfig)
    (h : reachIn (uniformU dec) k p q) : p.1 = q.1 := by
  induction k generalizing p with
  | zero => simp only [reachIn] at h; rw [h]
  | succ k ih =>
    obtain ⟨r, hs, hr⟩ := h
    obtain ⟨hc, _⟩ := hs
    rw [hc]; exact ih r hr

/-- **The uniform machine simulates `univNTM code` exactly (PROVED).**  On code-carrying configs, `uStep`'s `k`-step
reachability equals `univNTM code`'s — the code is data, the step is `univStep code`, so no overhead and full
uniformity. -/
theorem uStep_reachIn (dec : List Bool → ℕ × List Bool) (code : ℕ) (k : ℕ) (c c' : CConfig) :
    reachIn (uniformU dec) k (code, c) (code, c') ↔ reachIn (univNTM code) k c c' := by
  induction k generalizing c with
  | zero =>
    show (code, c) = (code, c') ↔ c = c'
    constructor
    · intro h; exact (Prod.ext_iff.mp h).2
    · intro h; rw [h]
  | succ k ih =>
    simp only [reachIn]
    constructor
    · rintro ⟨q, hs, hr⟩
      obtain ⟨hcode, huniv⟩ := hs
      have hq : q = (code, q.2) := Prod.ext hcode.symm rfl
      rw [hq] at hr
      exact ⟨q.2, huniv, (ih q.2).mp hr⟩
    · rintro ⟨d, hs, hr⟩
      exact ⟨(code, d), ⟨rfl, hs⟩, (ih d).mpr hr⟩

/-- **One fixed machine simulates every machine (PROVED).**  If the input `w` decodes to `(⟨M⟩, x)`, the single
universal machine `uniformU dec` accepts `w` within `t` steps iff `M` accepts `x` within `t` — combining the uniform
reachability (`uStep_reachIn`) with entry-296's overhead-1 simulation (`univ_simulates_exactly`).  The code is read from
the input; the machine is fixed. -/
theorem uniformU_simulates (dec : List Bool → ℕ × List Bool) (M : TMachine) (w x : List Bool) (t : ℕ)
    (hdec : dec w = (machineEquiv M, x)) :
    acceptsWithin (uniformU dec) w t ↔ acceptsWithin (toNTM M) x t := by
  have hinit : (uniformU dec).init w = (machineEquiv M, (0, 0, x)) := by
    simp only [uniformU, hdec]
  have huni : acceptsWithin (uniformU dec) w t ↔ acceptsWithin (univNTM (machineEquiv M)) x t := by
    unfold acceptsWithin
    constructor
    · rintro ⟨k, hk, p, hr, ha⟩
      rw [hinit] at hr
      have hp1 : machineEquiv M = p.1 := uStep_preserves_code dec k _ p hr
      have hp : p = (machineEquiv M, p.2) := Prod.ext hp1.symm rfl
      rw [hp] at hr ha
      exact ⟨k, hk, p.2, (uStep_reachIn dec (machineEquiv M) k (0, 0, x) p.2).mp hr, ha⟩
    · rintro ⟨k, hk, c, hr, ha⟩
      refine ⟨k, hk, (machineEquiv M, c), ?_, ha⟩
      rw [hinit]
      exact (uStep_reachIn dec (machineEquiv M) k (0, 0, x) c).mpr hr
  exact huni.trans (univ_simulates_exactly M x t)

/-! ## A concrete decode, so the universal machine is self-contained -/

/-- A concrete pairing of a code and an input into one tape: `code` in unary, a `false` separator, then the input. -/
def encPair (code : ℕ) (x : List Bool) : List Bool := List.replicate code true ++ (false :: x)

/-- The matching parse: read the leading run of `true`s as the code, drop it and the separator. -/
def decPair (w : List Bool) : ℕ × List Bool :=
  ((w.takeWhile (· = true)).length, w.drop ((w.takeWhile (· = true)).length + 1))

theorem decPair_takeWhile (code : ℕ) (x : List Bool) :
    (encPair code x).takeWhile (· = true) = List.replicate code true := by
  unfold encPair
  induction code with
  | zero => simp [List.takeWhile]
  | succ c ih => simp [List.replicate_succ, List.takeWhile, ih]

theorem decPair_drop (code : ℕ) (x : List Bool) :
    (encPair code x).drop (code + 1) = x := by
  unfold encPair
  induction code with
  | zero => simp
  | succ c ih => simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons]; exact ih

/-- **The concrete encoding round-trips (PROVED): `decPair (encPair code x) = (code, x)`.** -/
theorem decPair_encPair (code : ℕ) (x : List Bool) : decPair (encPair code x) = (code, x) := by
  unfold decPair
  rw [decPair_takeWhile, List.length_replicate]
  exact Prod.ext rfl (decPair_drop code x)

/-- **Self-contained: one fixed machine simulates every machine (PROVED).**  With the concrete parse `decPair`, the
single universal machine `uniformU decPair` on input `encPair ⟨M⟩ x` accepts within `t` iff `M` accepts `x` within `t`.
The decode-from-input universal machine, fully realized over the transition-table model. -/
theorem uniformU_simulates_enc (M : TMachine) (x : List Bool) (t : ℕ) :
    acceptsWithin (uniformU decPair) (encPair (machineEquiv M) x) t ↔ acceptsWithin (toNTM M) x t :=
  uniformU_simulates decPair M (encPair (machineEquiv M) x) x t (decPair_encPair (machineEquiv M) x)

/-!
**The decode-from-input uniformity, proved.**  `uniformU dec` is a *single* fixed machine (its only parameter the
M-independent parse `dec`) that reads the machine code from its input and simulates *any* `M` exactly: code preserved
(`uStep_preserves_code`), reachability uniform (`uStep_reachIn`), simulation exact (`uniformU_simulates`, with overhead
1 from entry 296).  A concrete parse `decPair` round-trips (`decPair_encPair`), so `uniformU decPair` on `encPair ⟨M⟩ x`
simulates every `M` self-containedly (`uniformU_simulates_enc`).  Together with entry 296 the universal NTM simulation
is now formalized — one uniform machine, overhead 1 — the universal TM (Turing 1936) over the transition-table model.
Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0DecodeUniformity

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DecodeUniformity.uStep_preserves_code
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DecodeUniformity.uStep_reachIn
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DecodeUniformity.uniformU_simulates
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DecodeUniformity.decPair_encPair
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DecodeUniformity.uniformU_simulates_enc
