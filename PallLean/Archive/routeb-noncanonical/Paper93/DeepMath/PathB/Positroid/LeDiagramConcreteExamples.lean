import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The 3×3 zero Le diagram. -/
def le_diagram_3x3_zero : LeDiagram 3 3 := LeDiagram.zero 3 3

/-- The 3×3 all-ones Le diagram. -/
def le_diagram_3x3_one : LeDiagram 3 3 := LeDiagram.one 3 3

/-- The 4×4 zero Le diagram. -/
def le_diagram_4x4_zero : LeDiagram 4 4 := LeDiagram.zero 4 4

/-- The 4×4 all-ones Le diagram. -/
def le_diagram_4x4_one : LeDiagram 4 4 := LeDiagram.one 4 4

theorem le_diagram_3x3_zero_filling (i j : Fin 3) :
    le_diagram_3x3_zero.filling i j = false := rfl

theorem le_diagram_3x3_one_filling (i j : Fin 3) :
    le_diagram_3x3_one.filling i j = true := rfl

theorem le_diagram_4x4_zero_filling (i j : Fin 4) :
    le_diagram_4x4_zero.filling i j = false := rfl

theorem le_diagram_4x4_one_filling (i j : Fin 4) :
    le_diagram_4x4_one.filling i j = true := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
