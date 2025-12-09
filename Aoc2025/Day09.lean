import Aoc2025.Util

namespace Day09
open Day09

def parseInput : IO (Array Coord) := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  let coords <- lines.mapM (fun line => do
    let components := line.splitOn ","
    match <- components.mapM String.toIntIO with
    | [x, y] => pure <| Coord.mk x y
    | _ => throw <| IO.userError s!"Bad coordinate: {line}")
  return coords

def allRects (pts : Array Coord) : List (Nat × Fin pts.size × Fin pts.size) := Id.run do
  let rects := List.range pts.size
    |>.mapRevMem (fun a ha =>
      let ptA := pts[a]'(by grind)
      Task.spawn fun () =>
        List.range' (a + 1) (pts.size - (a + 1))
          |>.mapRevMem (fun b hb =>
            let ptB := pts[b]'(by grind)
            (((ptA - ptB).abs + (.down + .right)).area.natAbs,
             Fin.mk (n:=pts.size) a (by grind),
             Fin.mk (n:=pts.size) b (by grind)))
          |>.mergeSort (·.1 ≥ ·.1))
    |>.parallelFoldComm (Task.lift (List.merge · · (·.1 ≥ ·.1))) []
  return rects.get

def part1 (pts : Array Coord) : Id Nat := do
  let rects := allRects pts
  return if h : rects = [] then 0 else (rects.head h).1

def makeEdge : Coord -> Coord -> Coord × Coord
  | ⟨x1, y1⟩, ⟨x2, y2⟩ =>
    (Coord.mk (min x1 x2) (min y1 y2),
     Coord.mk (max x1 x2) (max y1 y2))

def pointsToEdges (pts : Array Coord) : Array (Coord × Coord) :=
  List.range pts.size
    |>.mapRevMem (fun i hi0 =>
    have hi : i < pts.size := by grind
    let j := (i + 1) % pts.size
    have hj : j < pts.size := Nat.mod_lt _ (by grind)
    makeEdge pts[i] pts[j])
    |>.toArray

def part2 (pts : Array Coord) : IO Nat := do
  let rects := allRects pts
  let edges := pointsToEdges pts

  let rectInBounds (ptA ptB : Coord) : Bool := Id.run do
    let (ptA, ptB) := makeEdge ptA ptB
    for (eA, eB) in edges do
      if eA.bothLT ptB ∧ ptA.bothLT eB then return false
    return true

  return match rects.find? (fun (_, a, b) => rectInBounds pts[a] pts[b]) with
  | .some (size, _, _) => size
  | .none => 0

end Day09
open Day09

def main : IO Unit := do
  let input <- parseInput
  IO.println s!"Part 1: {<- part1 input}"
  IO.println s!"Part 2: {<- part2 input}"
