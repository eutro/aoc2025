import Aoc2025.Util
import Std.Data.HashMap

namespace Day07
open Day07

inductive Cell where
  | nil
  | splitter
  | start
deriving Repr, DecidableEq

def Cell.parse : Char -> IO Cell
  | '.' => pure nil
  | '^' => pure splitter
  | 'S' => pure start
  | c => throw <| IO.userError s!"Invalid cell {c}"
instance : ToString Cell where
  toString
    | .nil => "."
    | .splitter => "^"
    | .start => "S"

abbrev IsSplitter (grid : Grid Cell) (pos : Coord) :=
  grid[pos]? = some .splitter

def parseInput : IO (Coord × Grid Cell) := do
  let grid <- Grid.fromLines (<- (<- IO.getStdin).lines) Cell.parse
  let mut start := Option.none
  for y in List.range grid.height do
    for x in List.range grid.width do
      let pos := Coord.mk x y
      if grid[pos]? = .some .start
      then start := .some pos ; break
  return (start.get!, grid)

def Std.HashMap.insertFold {α β : Type} [BEq α] [Hashable α] 
  (map : Std.HashMap α β) (key : α) (val : β) (fold : β -> β -> β) : Std.HashMap α β :=
  map.alter key fun
    | .none => val
    | .some val' => fold val val'

def countBeams (start : Coord) (grid : Grid Cell) : Nat × Nat := Id.run do
  let mut splits := 0
  let mut xs : Std.HashMap Nat Nat := {(start.x.toNat, 1)}
  for y in List.inclusiveRange start.y.toNat grid.height do
    for (x, fx) in xs do
      if IsSplitter grid ⟨x, y⟩ then
        splits := splits + 1
        xs := xs.erase x
        xs := xs.insertFold (x - 1) fx (· + ·)
        xs := xs.insertFold (x + 1) fx (· + ·)
  return (splits, xs.values.sum)

end Day07
open Day07

def main : IO Unit := do
  let (start, grid) <- parseInput
  let (part1, part2) := countBeams start grid
  IO.println s!"Part 1: {part1}"
  IO.println s!"Part 2: {part2}"
