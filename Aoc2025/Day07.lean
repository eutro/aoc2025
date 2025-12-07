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
      then start := .some pos
           break
  return (start.get!, grid)

def Std.HashMap.insertFold {α β : Type} [BEq α] [Hashable α] 
  (map : Std.HashMap α β) (key : α) (val : β) (fold : β -> β -> β) : Std.HashMap α β :=
  map.alter key (fun
    | .none => val
    | .some val' => fold val val')

def countBeams {α : Type}
  (start : Coord) (grid : Grid Cell)
  (init : α) (fold : α -> α -> α) : Nat × List α := Id.run do
  let mut splits := 0
  let mut xs : Std.HashMap Nat α := Std.HashMap.emptyWithCapacity
    |>.insert start.x.toNat init
  for y in List.inclusiveRange start.y.toNat grid.height do
    let mut xs' := Std.HashMap.emptyWithCapacity
    for (x, fx) in xs do
      let pos := Coord.mk x y
      if IsSplitter grid pos then
        splits := splits + 1
        xs' := xs'.insertFold (x - 1) fx fold
        xs' := xs'.insertFold (x + 1) fx fold
      else
        xs' := xs'.insertFold x fx fold
    xs := xs'
  return (splits, xs.values)

def part1 (start : Coord) (grid : Grid Cell) : Nat :=
  let (count, _) := countBeams start grid 1 (· + ·)
  count

def part2 (start : Coord) (grid : Grid Cell) : Nat :=
  let (_, worlds) := countBeams start grid 1 (· + ·)
  worlds.sum

end Day07
open Day07

def main : IO Unit := do
  let (start, grid) <- parseInput
  IO.println s!"Part 1: {part1 start grid}"
  IO.println s!"Part 2: {part2 start grid}"
