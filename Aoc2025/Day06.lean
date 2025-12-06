import Aoc2025.Util

namespace Day06
open Day06

inductive Op where | add | mul
deriving Repr

def Op.parse : String -> IO Op
  | "+" => pure add
  | "*" => pure mul
  | c => throw <| IO.userError s!"Invalid op: {c}"

def Op.perform : Op -> Nat -> Nat -> Nat
  | .add, x, y => x + y
  | .mul, x, y => x * y
def Op.identity : Op -> Nat
  | .add => 0
  | .mul => 1

structure Puzzle where
  op : Op
  args : Array Nat
deriving Repr

def Puzzle.compute (puzzle : Puzzle) : Nat :=
  puzzle.args.foldl puzzle.op.perform puzzle.op.identity

def String.splitWs (row : String) : Array String :=
  row.splitToList (·.isWhitespace)
    |>.filter (!·.isEmpty)
    |>.toArray

def parseInput : IO (Array Op × Array String) := do
  let lines <- (<- IO.getStdin).lines
  if h : 0 = lines.size then throw <| IO.userError "Not enough input lines" else
  let ops <- lines.back.splitWs.mapM Op.parse
  let numbers := lines.take (lines.size - 1)
  return (ops, numbers)

def computeAndSum (puzzles : Array Puzzle) : Nat :=
  puzzles.map (·.compute) |>.sum

def part1 (ops : Array Op) (numberLines : Array String) : IO Nat := do
  let parseNumberRow row := row.splitWs.mapM (·.toNatIO)
  let mut numbersGrid :=
    Grid.ofRows (<- numberLines.mapM parseNumberRow) 
    |>.transpose
  return ops.zip numbersGrid.toRows
    |>.map (fun ⟨op, args⟩ => Puzzle.mk op args)
    |> computeAndSum

def part2 (ops : Array Op) (numberLines : Array String) : IO Nat := do
  let mut charGrid : List String := Grid.ofRows (numberLines.map (·.toList.toArray))
    |>.transpose |>.toRows.toList |>.map (fun row => row.toList.asString.trim)
  let mut puzzles := #[]
  for op in ops do
    let numbers <- charGrid.takeWhile (· ≠ "") |>.toArray.mapM (·.toNatIO)
    puzzles := puzzles.push (Puzzle.mk op numbers)
    charGrid := charGrid.dropWhile (· ≠ "") |>.drop 1
  return computeAndSum puzzles

end Day06
open Day06

def main : IO Unit := do
  let (ops, numberLines) <- parseInput
  IO.println s!"Part 1: {<- part1 ops numberLines}"
  IO.println s!"Part 2: {<- part2 ops numberLines}"
