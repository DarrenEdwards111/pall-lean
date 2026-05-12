import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef

/-!
# Le-diagram instances at n = 15 and n = 20

This file extends `LeDiagramLargeNExamples` (which provides instances at
n = 5 and n = 10) with the corresponding instances at n = 15 and n = 20.
We give the all-zeros and all-ones Le diagrams on a 15×15 and 20×20
rectangle, together with the basic filling-evaluation lemmas.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound` may be used by the
underlying `LeDiagram` definitions.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

def le_diagram_15x15_zero : LeDiagram 15 15 := LeDiagram.zero 15 15
def le_diagram_15x15_one : LeDiagram 15 15 := LeDiagram.one 15 15
def le_diagram_20x20_zero : LeDiagram 20 20 := LeDiagram.zero 20 20
def le_diagram_20x20_one : LeDiagram 20 20 := LeDiagram.one 20 20

theorem le_diagram_15x15_zero_filling (i j : Fin 15) :
    le_diagram_15x15_zero.filling i j = false := rfl

theorem le_diagram_15x15_one_filling (i j : Fin 15) :
    le_diagram_15x15_one.filling i j = true := rfl

theorem le_diagram_20x20_zero_filling (i j : Fin 20) :
    le_diagram_20x20_zero.filling i j = false := rfl

theorem le_diagram_20x20_one_filling (i j : Fin 20) :
    le_diagram_20x20_one.filling i j = true := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
