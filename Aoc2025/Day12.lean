import Aoc2025.Util

namespace Day12
open Day12

structure Piece where
-- Not needed, apparently??
def Piece.parse (_s : String) : IO Piece := return ⟨⟩

structure Tree where
  size : Coord
  counts : Array Nat

def Tree.parse (s : String) : IO Tree := do
  match s.splitOn ": " with
  | [size, counts] =>
    match size.splitOn "x" with
    | [width, height] =>
      let counts <- counts.splitOn " " |>.toArray.mapM String.toNatIO
      return ⟨⟨<- width.toIntIO, <- height.toIntIO⟩, counts⟩
    | _ => throw <| IO.userError s!"Bad size: {size}"
  | _ => throw <| IO.userError s!"Bad tree: {s}"

def parseInput : IO (Array Piece × Array Tree) := do
  let stdin <- IO.getStdin
  let str <- stdin.readToEnd
  let parts := str.splitOn "\n\n" |>.toArray
  if _h : parts.size = 0 then
    throw <| IO.userError s!"Bad input"
  else
  let pieces <- parts.take (parts.size - 1) |>.mapM Piece.parse
  let trees <- parts.back.trim.splitOn "\n" |>.toArray.mapM Tree.parse
  return (pieces, trees)

def Tree.canFit (tree : Tree) (_pieces : Array Piece) : Bool :=
  tree.size.area >= tree.counts.sum * 9

def part1 (pieces : Array Piece) (trees : Array Tree) : Id Nat := do
  trees.countP (·.canFit pieces)

end Day12
open Day12

def main : IO Unit := do
  let (pieces, trees) <- parseInput
  println! "Part 1: {<- part1 pieces trees}"
