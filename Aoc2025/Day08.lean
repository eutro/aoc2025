import Aoc2025.Util

structure UnionFindNode (ℓ : Nat) where
  parent : Fin ℓ
  size : Nat
deriving Repr
abbrev UnionFind (ℓ : Nat) :=
  Vector (UnionFindNode ℓ) ℓ

namespace UnionFind
variable {ℓ : Nat} (uf : UnionFind ℓ)

def new (ℓ : Nat) : UnionFind ℓ := Vector.ofFn (⟨·, 1⟩)      

def find (n : Fin ℓ) : UnionFind ℓ × Fin ℓ :=
  let rec findAux (uf : UnionFind ℓ) (n : Fin ℓ) : Nat -> UnionFind ℓ × Fin ℓ
    | 0 => (uf, n)
    | fuel + 1 =>
      let node := uf[n]
      if node.parent = n
      then (uf, n)
      else let (uf', n') := findAux uf uf[n].parent fuel
           (uf'.set n {node with parent := n'}, n')
  findAux uf n ℓ

def union (n m : Fin ℓ) : UnionFind ℓ × Fin ℓ :=
  let (uf, n) := uf.find n
  let (uf, m) := uf.find m
  if n = m then ⟨uf, n⟩ else
  let ⟨n, nsize⟩ := uf[n]
  let ⟨m, msize⟩ := uf[m]
  if nsize <= msize
  then ⟨uf.set n ⟨m, 0⟩ |>.set m ⟨m, nsize + msize⟩, m⟩
  else ⟨uf.set m ⟨n, 0⟩ |>.set n ⟨n, nsize + msize⟩, n⟩

def groupSizes : Array Nat := Id.run do
  let mut sizes : Array Nat := #[]
  for h : n in List.range ℓ do
    let node := uf[n]'(by grind)
    if node.parent = n then
      sizes := sizes.push node.size
  sizes

end UnionFind

namespace Day08
open Day08

@[ext]
structure Pos3D where
  x : Int
  y : Int
  z : Int
deriving Repr, DecidableEq, Hashable

def Pos3D.parse (s : String) : IO Pos3D := do
  match <- s.splitOn "," |>.mapM (·.toIntIO) with
  | [x, y, z] => pure ⟨x, y, z⟩
  | _ => throw <| IO.userError s!"Bad position: {s}"

def parseInput : IO (Array Pos3D) := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  lines.mapM Pos3D.parse

def Pos3D.distanceSqr (a b : Pos3D) : Int :=
  (a.x - b.x)^2 + (a.y - b.y)^2 + (a.z - b.z)^2

def allEdges (boxes : Array Pos3D) : Id (Array (Fin boxes.size × Fin boxes.size)) := do
  let mut allDistances : Array (Int × Fin boxes.size × Fin boxes.size) := #[]
  for ha : a in List.range boxes.size do
    let boxA := boxes[a]'(by grind)
    for hb : b in List.range' (a + 1) (boxes.size - (a + 1)) do
      let boxB := boxes[b]'(by grind)
      let entry := (boxA.distanceSqr boxB, ⟨a, (by grind)⟩, ⟨b, (by grind)⟩)
      allDistances := allDistances.push entry
  return allDistances.qsort (·.1 < ·.1)
    |>.map (fun (dist, a, b) => (a, b))

def part1 (boxes : Array Pos3D) : Id Nat := do
  let edgesToTake := if boxes.size = 20 then 10 else 1000
  let edges := allEdges boxes |>.take edgesToTake
  let uf := edges.foldl (fun uf (a, b) => (uf.union a b).1) (UnionFind.new boxes.size)
  return uf.groupSizes.qsort (· > ·) |>.take 3 |>.foldl (· * ·) 1

def part2 (boxes : Array Pos3D) : Id Int := do
  let edges <- allEdges boxes
  let mut uf := UnionFind.new boxes.size
  for (a, b) in edges do
    let (uf', n) := uf.union a b
    uf := uf'
    if uf[n].size = boxes.size then
      return boxes[a].x * boxes[b].x
  return 0

end Day08
open Day08

def main : IO Unit := do
  let boxes <- parseInput
  IO.println s!"Part 1: {<- part1 boxes}"
  IO.println s!"Part 2: {<- part2 boxes}"
