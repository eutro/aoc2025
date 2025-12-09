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
    |>.parallelFold (List.merge · · (·.1 ≥ ·.1)) []
  return rects.get

def part1 (pts : Array Coord) : Id Nat := do
  let rects := allRects pts
  return if h : rects = [] then 0 else (rects.head h).1

def countPrecedingEdges (edges : Array (Coord × Coord)) (pt : Coord) : IO Nat := do
  let mut cnt := 0
  let mut prevHalfEdgeRight : Option (Bool × Nat) := .none
  for (eA, eB) in edges do
    if eA.y > pt.y then break
    if ¬(eA.x ≤ pt.x ∧ pt.x ≤ eB.x) then continue else
    let thisHalfEdgeRight : Option (Bool × Nat) :=
      if eA.x = pt.x then .some (true, cnt)
      else if eB.x = pt.x then .some (false, cnt)
      else .none
    match prevHalfEdgeRight, thisHalfEdgeRight with
    -- #---# (ordinary edge)
    | .none, .none =>
      prevHalfEdgeRight := .none
      if eA.y = pt.y
      then if 2 ∣ cnt then cnt := cnt + 1
      else cnt := cnt + 1
    /- --#    #--
         | OR |
       --#    #-- -/
    | .some (false, n), .some (false, _)
    | .some (true, n), .some (true, _) =>
      prevHalfEdgeRight := .none
      if eA.y ≠ pt.y then
        -- If we are inside only thanks to this side edge, then we are
        -- no longer inside.
        if 2 ∣ n then cnt := cnt + 1
    /- --#        #--
         |   OR   |
         #--    --# -/
    | .some (false, n), .some (true, _)
    | .some (true, n), .some (false, _) =>
      prevHalfEdgeRight := .none
      if eA.y ≠ pt.y then
        -- We have crossed an edge
        cnt := n + 1
    -- Start of any of the above
    | .none, .some (_, _) =>
      prevHalfEdgeRight := thisHalfEdgeRight
      -- No matter what, we stay in/enter the green tiles
      if 2 ∣ cnt then cnt := cnt + 1
    -- Should not really happen
    | .some _, .none => prevHalfEdgeRight := .none
  return cnt

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

def partitionEdges (edges : Array (Coord × Coord)) : Array (Coord × Coord) × Array (Coord × Coord) :=
  let horizEdges := edges.filter (fun (ptA, ptB) => ptA.y = ptB.y) |>.qsort (·.1.y < ·.1.y)
  let vertEdges := edges.filter (fun (ptA, ptB) => ptA.x = ptB.x) |>.qsort (·.1.x < ·.1.x)
                   |>.map (fun (ptA, ptB) => (ptA.transpose, ptB.transpose))
  (horizEdges, vertEdges)

def testEdges (pts : Array Coord) (tests : Array Coord) : IO (Array Nat) := do
  tests.mapM (countPrecedingEdges (pointsToEdges pts |> partitionEdges |>.1) ·)

/- #-#
   | |
   #-# -/
def testE1 : Array Coord := #[⟨0, 0⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨0, 2⟩]
-- #eval testEdges testE1 #[⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨2, 3⟩]
/- #-#
   | |
   | #-#
   |   |
   #---# -/
def testE2 : Array Coord := #[⟨0, 0⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨4, 4⟩, ⟨0, 4⟩]
-- #eval testEdges testE2 #[⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 4⟩, ⟨1, 5⟩]
-- #eval testEdges testE2 #[⟨2, 3⟩, ⟨3, 1⟩, ⟨3, 2⟩, ⟨3, 4⟩]
-- #eval testEdges testE2 #[⟨3, 5⟩, ⟨4, 0⟩, ⟨4, 2⟩, ⟨4, 3⟩, ⟨4, 5⟩]
/- #---#
   |   |
   | #-#
   | |
   #-#   -/
def testE3 : Array Coord := #[⟨0, 0⟩, ⟨4, 0⟩, ⟨4, 2⟩, ⟨2, 2⟩, ⟨2, 4⟩, ⟨0, 4⟩]
-- #eval testEdges testE3 #[⟨0, 3⟩, ⟨3, 2⟩, ⟨3, 3⟩, ⟨4, 2⟩, ⟨4, 3⟩]
-- #eval testEdges testE3 #[⟨2, 2⟩, ⟨2, 3⟩, ⟨2, 4⟩, ⟨2, 5⟩]
/- #-----#
   |     |
   #-# #-#
     | |
   #-# #-#
   |     |
   #-----# -/
def testE4 : Array Coord := #[⟨0, 0⟩, ⟨6, 0⟩, ⟨6, 2⟩, ⟨4, 2⟩, ⟨4, 4⟩, ⟨6, 4⟩, ⟨6, 6⟩,
  ⟨0, 6⟩, ⟨0, 4⟩, ⟨2, 4⟩, ⟨2, 2⟩, ⟨0, 2⟩]
-- #eval testEdges testE4 #[⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨0, 4⟩, ⟨0, 6⟩, ⟨0, 7⟩]
-- #eval testEdges testE4 #[⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 3⟩, ⟨1, 4⟩, ⟨1, 6⟩, ⟨1, 7⟩]
-- #eval testEdges testE4 #[⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 3⟩, ⟨2, 5⟩, ⟨2, 6⟩, ⟨2, 7⟩]
-- #eval testEdges testE4 #[⟨5, 0⟩, ⟨5, 2⟩, ⟨5, 3⟩, ⟨5, 4⟩, ⟨5, 6⟩, ⟨5, 7⟩]

def part2 (pts : Array Coord) : IO Nat := do
  let rects := allRects pts
  let edges := pointsToEdges pts
  let (horizEdges, vertEdges) := partitionEdges edges
  let countEdges (pt : Coord) := do
    return (<- countPrecedingEdges horizEdges pt,
            <- countPrecedingEdges vertEdges pt.transpose)

  let rectInBounds (ptA ptB : Coord) : IO Bool := do
    let edgesA <- countEdges ptA
    let edgesB <- countEdges ptB
    let edgesAB <- countEdges ⟨ptA.x, ptB.y⟩
    let edgesBA <- countEdges ⟨ptB.x, ptA.y⟩
    return edgesA.1 = edgesAB.1 ∧ edgesA.2 = edgesBA.2 ∧
      edgesB.1 = edgesBA.1 ∧ edgesB.2 = edgesAB.2

  return match <- rects.findM? (fun (_, a, b) => rectInBounds pts[a] pts[b]) with
  | .some (size, _, _) => size
  | .none => 0

end Day09
open Day09

def main : IO Unit := do
  let input <- parseInput
  IO.println s!"Part 1: {<- part1 input}"
  IO.println s!"Part 2: {<- part2 input}"
