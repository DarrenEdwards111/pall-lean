import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFrontLookup
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupDynamicRoute

/-!
# Charged local lookup: route a rebased-front lookup into runtime output

The marker-relative lookup already returns the real literal accept bit while
preserving the physical prefix before the doubled entry marker.  This file
places the verified dynamic one-bit output router around that complete body.
The router resets to the true output origin, extends only `outputCap`, and
leaves the residue, marker, rebased selector prefix, and completed lookup tape
unchanged.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontOutput

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeMarkedEntry
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontLookup

/-- The complete marker-relative lookup followed by its accept-bit router. -/
def runtimeMarkedFrontOutputMachine : Machine :=
  acceptRouteMachine runtimeMarkedFrontLookupMachine

def runtimeMarkedFrontOutputClock (pairs : List (Bool × Bool))
    (d : Nat) (w : List Bool) (l : Lit) (out : List Bool) : Nat :=
  runtimeMarkedFrontLookupClock pairs d w l + 1 + outputRouteClock out

/-- Dynamic cashout from a genuinely rebased selector.

`flattenPairs pairs` is the concrete aligned prefix consisting of the
fixed-capacity output followed by the arbitrary surviving residue.  The
machine discovers the marker, performs the complete lookup, reads its actual
accept bit in finite control, resets to physical origin, and appends exactly
that bit to the output. -/
theorem runtimeMarkedFrontOutput_run
    (B : Nat) (out residue : List Bool)
    (pairs : List (Bool × Bool)) (w : List Bool) (l : Lit)
    (rest : List (List Bool))
    (hout : out.length < B)
    (hpairs : outputCap B out ++ residue = flattenPairs pairs)
    (hsafe : RuntimeNoDoubleSepFrom false pairs) :
    let bits := literalLookupTape w l
    let d := (bits :: rest).length
    let source := sourceSelectorInput d 0 (bits :: rest)
    let marker := [false, true, false, true]
    let sourcePre := flattenPairs (List.replicate d (true, true)) ++
      [false, true]
    let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ archiveTail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let bv := evalLit (fun k => w.getD k false) l
    let T := outputCap B out ++ residue ++ marker ++ source
    let clock := runtimeMarkedFrontOutputClock pairs d w l out
    HaltsBy runtimeMarkedFrontOutputMachine T clock ∧
      (run runtimeMarkedFrontOutputMachine clock
        (init runtimeMarkedFrontOutputMachine T)).tp =
        outputCap B (out ++ [bv]) ++ residue ++ marker ++
          sourcePre ++ mcf.tp := by
  dsimp only
  let bits := literalLookupTape w l
  let d := (bits :: rest).length
  let source := sourceSelectorInput d 0 (bits :: rest)
  let marker := [false, true, false, true]
  let sourcePre := flattenPairs (List.replicate d (true, true)) ++
    [false, true]
  let archiveTail := flattenPairs (rest.flatMap freshSourceBlock)
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ archiveTail
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let bv := evalLit (fun k => w.getD k false) l
  let T := outputCap B out ++ residue ++ marker ++ source
  let payload := residue ++ marker ++ sourcePre ++ mcf.tp
  have hbody0 := runtimeMarkedFrontLookup_run pairs w l rest hsafe
  have hbody1 := hbody0
  rw [← hpairs] at hbody1
  have hbody : run runtimeMarkedFrontLookupMachine
      (runtimeMarkedFrontLookupClock pairs d w l)
      (init runtimeMarkedFrontLookupMachine T) =
      ⟨Sum.inr (Sum.inr mcf.st),
        (outputCap B out ++ residue ++ marker).length +
          (sourcePre.length + mcf.hd),
        outputCap B out ++ payload⟩ := by
    simpa [bits, d, source, marker, sourcePre, archiveTail, trailer, mcf,
      T, payload, List.append_assoc] using hbody1
  have hnative := runtimeFrontLookup_run w l rest
  have hnative' : run runtimeFrontLookupCore
      (runtimeFrontLookupClock d w l)
      (init runtimeFrontLookupCore source) =
      ⟨Sum.inr mcf.st, sourcePre.length + mcf.hd,
        sourcePre ++ mcf.tp⟩ := by
    simpa [bits, d, source, sourcePre, archiveTail, trailer, mcf] using hnative
  have hha := runtimeFrontLookup_halt_accept w l rest
  have hha' : runtimeFrontLookupCore.halt (Sum.inr mcf.st) = true ∧
      runtimeFrontLookupCore.accept (Sum.inr mcf.st) = bv := by
    change runtimeFrontLookupCore.halt
        (run runtimeFrontLookupCore (runtimeFrontLookupClock d w l)
          (init runtimeFrontLookupCore source)).st = true ∧
      runtimeFrontLookupCore.accept
        (run runtimeFrontLookupCore (runtimeFrontLookupClock d w l)
          (init runtimeFrontLookupCore source)).st = bv at hha
    rw [hnative'] at hha
    exact hha
  have hh : runtimeMarkedFrontLookupMachine.halt
      (Sum.inr (Sum.inr mcf.st)) = true := by
    simpa [runtimeMarkedFrontLookupMachine, runtimeMarkedAcceptBody,
      headSeqAcceptMachine] using hha'.1
  have ha : runtimeMarkedFrontLookupMachine.accept
      (Sum.inr (Sum.inr mcf.st)) = bv := by
    simpa [runtimeMarkedFrontLookupMachine, runtimeMarkedAcceptBody,
      headSeqAcceptMachine] using hha'.2
  by_cases hb : bv = true
  · have hr := acceptRoute_output_true runtimeMarkedFrontLookupMachine T
      (runtimeMarkedFrontLookupClock pairs d w l) B out payload
      (Sum.inr (Sum.inr mcf.st))
      ((outputCap B out ++ residue ++ marker).length +
        (sourcePre.length + mcf.hd)) hbody hh (by rw [ha, hb]) hout
    constructor
    · change runtimeMarkedFrontOutputMachine.halt
        (run runtimeMarkedFrontOutputMachine
          (runtimeMarkedFrontOutputClock pairs d w l out)
          (init runtimeMarkedFrontOutputMachine T)).st = true
      simpa [runtimeMarkedFrontOutputMachine, runtimeMarkedFrontOutputClock]
        using congrArg
          (fun c => runtimeMarkedFrontOutputMachine.halt c.st) hr
    · have hb' : evalLit (fun k => w.getD k false) l = true := hb
      rw [hb']
      simpa [runtimeMarkedFrontOutputMachine, runtimeMarkedFrontOutputClock,
        bits, d, source, marker, sourcePre, archiveTail, trailer, mcf,
        T, payload, List.append_assoc] using congrArg Cfg.tp hr
  · have hb0 : bv = false := by simpa using hb
    have hr := acceptRoute_output_false runtimeMarkedFrontLookupMachine T
      (runtimeMarkedFrontLookupClock pairs d w l) B out payload
      (Sum.inr (Sum.inr mcf.st))
      ((outputCap B out ++ residue ++ marker).length +
        (sourcePre.length + mcf.hd)) hbody hh (by rw [ha, hb0]) hout
    constructor
    · change runtimeMarkedFrontOutputMachine.halt
        (run runtimeMarkedFrontOutputMachine
          (runtimeMarkedFrontOutputClock pairs d w l out)
          (init runtimeMarkedFrontOutputMachine T)).st = true
      simpa [runtimeMarkedFrontOutputMachine, runtimeMarkedFrontOutputClock]
        using congrArg
          (fun c => runtimeMarkedFrontOutputMachine.halt c.st) hr
    · have hb0' : evalLit (fun k => w.getD k false) l = false := hb0
      rw [hb0']
      simpa [runtimeMarkedFrontOutputMachine, runtimeMarkedFrontOutputClock,
        bits, d, source, marker, sourcePre, archiveTail, trailer, mcf,
        T, payload, List.append_assoc] using congrArg Cfg.tp hr

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontOutput

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFrontOutput.runtimeMarkedFrontOutput_run
