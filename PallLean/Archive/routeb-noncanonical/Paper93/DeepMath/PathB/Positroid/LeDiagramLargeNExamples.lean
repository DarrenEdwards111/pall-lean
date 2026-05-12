import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid

def le_diagram_5x5_zero : LeDiagram 5 5 := LeDiagram.zero 5 5
def le_diagram_5x5_one : LeDiagram 5 5 := LeDiagram.one 5 5
def le_diagram_10x10_zero : LeDiagram 10 10 := LeDiagram.zero 10 10
def le_diagram_10x10_one : LeDiagram 10 10 := LeDiagram.one 10 10

theorem le_diagram_5x5_zero_filling (i j : Fin 5) :
    le_diagram_5x5_zero.filling i j = false := rfl

theorem le_diagram_5x5_one_filling (i j : Fin 5) :
    le_diagram_5x5_one.filling i j = true := rfl

theorem le_diagram_10x10_zero_filling (i j : Fin 10) :
    le_diagram_10x10_zero.filling i j = false := rfl

theorem le_diagram_10x10_one_filling (i j : Fin 10) :
    le_diagram_10x10_one.filling i j = true := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
