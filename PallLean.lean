-- Critical path: P ≠ NP via SPDP rank separation
-- Existing infrastructure
import PallLean.SPDPDefs
import PallLean.TuringMachine
import PallLean.Compiler
import PallLean.TseitinDefs
import PallLean.Tseitin
import PallLean.NPWitness
import PallLean.IdentityMinor
import PallLean.TagMonomial
import PallLean.CoeffDisjoint
import PallLean.ProductDeriv
import PallLean.BinomialBound
import PallLean.BinomialBound2
import PallLean.MultilinearSPDP
import PallLean.Leibniz
import PallLean.Profile

-- Paper-faithful architecture (main chain)
import PallLean.BoolEval
import PallLean.Restriction
import PallLean.CircuitModel
import PallLean.RestrictedSPDP
import PallLean.SPDPClass
import PallLean.PaperAxioms
import PallLean.PsideCollapse
import PallLean.DiagonalFunction
import PallLean.PneqNP_PaperFaithful

-- Legacy chain intentionally not imported in paper-faithful build
-- import PallLean.PneqNP
