@[ext]
structure Coord where
  x : Int
  y : Int
deriving DecidableEq, Hashable, Inhabited, Nonempty, Repr, TypeName, Ord
@[simp] instance : LE Coord := leOfOrd
@[simp] instance : LT Coord := ltOfOrd

namespace Coord

instance : ToString Coord where
  toString | ⟨x, y⟩ => s!"{x},{y}"

abbrev origin : Coord := ⟨0, 0⟩
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

def magnitudeSqr (pos : Coord) : Nat :=
  (pos.x^2).toNat * (pos.y^2).toNat

def abs (pos : Coord) : Coord := ⟨pos.x.natAbs, pos.y.natAbs⟩
def area (pos : Coord) : Int := pos.x * pos.y

def sign (pos : Coord) : Coord :=
  ⟨pos.x.sign, pos.y.sign⟩

abbrev bothLT (pos pos' : Coord) :=
  pos.x < pos'.x ∧ pos.y < pos'.y
abbrev bothLE (pos pos' : Coord) :=
  pos.x ≤ pos'.x ∧ pos.y ≤ pos'.y

def transpose (pos : Coord) : Coord := ⟨pos.y, pos.x⟩

end Coord
