structure Coord where
  x : Int
  y : Int
deriving DecidableEq, Hashable, Inhabited, Nonempty, Repr, TypeName

namespace Coord
abbrev up : Coord := ⟨0, -1⟩
abbrev down : Coord := ⟨0, 1⟩
abbrev left : Coord := ⟨-1, 0⟩
abbrev right : Coord := ⟨1, 0⟩

@[simp] instance : Add Coord := ⟨fun ⟨x1, y1⟩ ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩⟩
@[simp] instance : Sub Coord := ⟨fun ⟨x1, y1⟩ ⟨x2, y2⟩ => ⟨x1 - x2, y1 - y2⟩⟩
@[simp] instance : HMul Int Coord Coord := ⟨fun s ⟨x, y⟩ => ⟨s * x, s * y⟩⟩
@[simp] instance : HMul Coord Int Coord := ⟨fun ⟨x, y⟩ s => ⟨x * s, y * s⟩⟩

abbrev manhattanAdjacentDelta : List Coord := [up, left, right, down]
def manhattanAdjacent (pos : Coord) : List Coord :=
  List.map (pos + ·) manhattanAdjacentDelta

abbrev adjacentDelta : List Coord :=
  [up + left  , up  , up + right,
   left       ,       right,
   down + left, down, down + right]
def adjacent (pos : Coord) : List Coord :=
  List.map (pos + ·) adjacentDelta
end Coord
