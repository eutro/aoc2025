import Aoc2025.Util
import Std.Data.HashMap

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

abbrev IsRoll (grid : Grid Cell) (pos : Coord) :=
  grid[pos]? = some Cell.roll
abbrev accessibility (grid : Grid Cell) (pos : Coord) :=
  pos.adjacent.countP (IsRoll grid ·)
abbrev ForkLiftAccessible (grid : Grid Cell) (pos : Coord) :=
  accessibility grid pos < 4

structure AccessibilityMap where
  grid : Grid Cell
  accessibleCoords : Array { pos : Coord // ForkLiftAccessible grid pos }
  coordToAcc : Std.DHashMap Coord (fun pos =>
    { n : Nat // n = accessibility grid pos })

def Grid.removeTowel (grid : Grid Cell) (pos : Coord) : Grid Cell :=
  grid.set? pos .nil

def AccessibilityMap.get (grid : Grid Cell) : AccessibilityMap := Id.run do
  let mut accessible := #[]
  let mut coordMap := Std.DHashMap.emptyWithCapacity
  for y in List.range grid.height do
    for x in List.range grid.width do
      let pos := Coord.mk x y
      if IsRoll grid pos then
        let acc := accessibility grid pos
        if h : acc < 4
        then accessible := accessible.push ⟨pos, by grind⟩
        else coordMap := coordMap.insert pos ⟨acc, by rfl⟩
  return ⟨grid, accessible, coordMap⟩

def part1 (grid : Grid Cell) : Id Nat := do
  let acc := AccessibilityMap.get grid
  return acc.accessibleCoords.size

def part2 (grid : Grid Cell) : Id Nat := do
  let mut total := 0
  let accMap := AccessibilityMap.get grid
  -- It would be nice to have the queue and cache retain their
  -- dependent types that prove their correspondence to the grid
  -- state, but it would be too much effort to prove.
  let mut grid := accMap.grid
  let mut queue := accMap.accessibleCoords.map (fun pos => pos.1)
  let mut coordToAcc := Std.HashMap.mk <| accMap.coordToAcc.map (fun _ v => v.1)
  for _ in List.range (grid.width * grid.height) do
    if h : queue.size = 0 then break else
    let pos := queue.back
    queue := queue.pop
    total := total + 1
    grid := grid.removeTowel pos
    for pos' in pos.adjacent do
      if h : IsRoll grid pos' ∧ pos' ∈ coordToAcc then
        let acc := coordToAcc[pos']'h.2
        if hacc : acc = 4
        then queue := queue.push pos'
             coordToAcc := coordToAcc.erase pos'
        else coordToAcc := coordToAcc.insert pos' (acc - 1)
  return total

end Day04
open Day04

def main : IO Unit := do
  let grid <- parseInput
  IO.println s!"Part 1: {<- part1 grid}"
  IO.println s!"Part 2: {<- part2 grid}"
  return ()
