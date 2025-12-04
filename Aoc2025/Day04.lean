structure Grid (α : Type) where
  width : Nat
  height : Nat
  rows : Vector (Vector α width) height
deriving DecidableEq, Inhabited, Repr

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

namespace Grid

variable {α : Type} (grid : Grid α)

instance : Inhabited (Grid α) := ⟨⟨0, 0, #v[]⟩⟩
instance : ∀ [ToString α], ToString (Grid α) where
  toString grid :=
    ("\n".intercalate ·.toList) <|
      grid.rows.map (fun row => "".intercalate (row.map toString).toList)

def fromLines {m : Type -> Type}
  [Monad m] [Inhabited (m α)]
  (lines : Array String) (cell : Char -> m α)
  : m (Grid α) := do
  let height := lines.size
  let width := Array.foldl max 0 (lines.map (·.length))
  let rows <- (Vector.mapM · lines.toVector) fun row =>
    let row := row.toList.toArray
    Vector.ofFnM fun i => do
      if h : i < row.size
      then cell row[i]
      else default
  return mk width height rows

abbrev inBoundsXY (x y : Int) :=
  0 <= x ∧ x < grid.width ∧ 0 <= y ∧ y < grid.height
abbrev inBounds (pos : Coord) :=
  grid.inBoundsXY pos.x pos.y

instance : GetElem (Grid α) Coord α inBounds where
  getElem grid pos h := grid.rows[pos.y.toNat][pos.x.toNat]

-- Replace grid[pos] with (f grid[pos]), linearly.
def modify? (pos : Coord) (f : α -> α) : Grid α :=
  let ⟨width, height, ⟨rows, hrows⟩⟩ := grid
  let rows' := ⟨rows.modify pos.y.toNat (fun ⟨row, hrow⟩ =>
      ⟨row.modify pos.x.toNat f, (by grind)⟩),
      (by grind)⟩
  Grid.mk width height rows'

-- Replace grid[pos] with value, linearly.
def set? (pos : Coord) (value : α) : Grid α :=
  grid.modify? pos (fun _ => value)

end Grid

namespace Day04
open Day04

inductive Cell : Type where
  | nil : Cell
  | roll : Cell
deriving DecidableEq, Hashable, Nonempty, Repr, TypeName

instance : Inhabited Cell := ⟨.nil⟩
instance : ToString Cell where
  toString
  | .nil => "."
  | .roll => "@"

def Cell.parse : Char -> IO Cell
  | '.' => pure nil
  | '@' => pure roll
  | c => throw <| IO.userError s!"Bad cell {c}"

def parseInput : IO (Grid Cell) := do
  let stdin <- IO.getStdin
  Grid.fromLines (<- stdin.lines) Cell.parse

abbrev ForkLiftAccessible (grid : Grid Cell) (pos : Coord) :=
  pos.adjacent.countP (grid[·]? = some Cell.roll) < 4

def getForkliftAccessible (grid : Grid Cell) : Array Coord := Id.run do
  let mut ret := #[]
  for y in List.range grid.height do
    for x in List.range grid.width do
      if grid[Coord.mk x y]? = some .roll ∧ ForkLiftAccessible grid ⟨x, y⟩
      then ret := ret.push ⟨x, y⟩
  return ret

def part1 (grid : Grid Cell) : IO Nat := do
  return (getForkliftAccessible grid).size

def part2 (grid : Grid Cell) : IO Nat := do
  let mut grid := grid
  let mut total := 0
  for _ in List.range (grid.width * grid.height) do
    let accessible := getForkliftAccessible grid
    if accessible = #[] then break
    total := total + accessible.size
    for pos in accessible do
      grid := grid.set? pos .nil
  return total

end Day04
open Day04

def main : IO Unit := do
  let grid <- parseInput
  IO.println s!"Part 1: {<- part1 grid}"
  IO.println s!"Part 2: {<- part2 grid}"
  return ()
