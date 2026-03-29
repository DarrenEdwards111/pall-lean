import PallLean.HoloCompilerDistinctPartition
import Mathlib.Tactic

/-!
# HoloCompilerDistinctLocality

This file proves the first concrete locality facts for the distinct holographic
compiler scaffold. These are not the full paper gadgets yet, but they establish
that the current duplicated-layer factors are genuinely local objects.
-/

namespace HoloCompilerDistinctLocality

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
