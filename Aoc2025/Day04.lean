import Aoc2025.Util

namespace Day04
open Day04

inductive Cell : Type where
  | nil
  | roll
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
