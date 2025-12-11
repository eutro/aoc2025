import Aoc2025.Util
import Std.Data.HashMap

namespace Day11
open Day11

structure Graph where
  outEdges : Std.HashMap String (Array String)
  inEdges : Std.HashMap String (Array String)
  mem_outEdges_inEdges_iff (x : String)
    : x ∈ outEdges ↔ x ∈ inEdges
deriving Repr

@[simp]
instance : Membership String Graph where
  mem g x := x ∈ g.outEdges

@[simp, grind =]
theorem Graph.mem_inEdges_iff {g : Graph} {x : String}
  : x ∈ g.outEdges ↔ x ∈ g.inEdges := by
  apply g.mem_outEdges_inEdges_iff

def Graph.empty : Graph :=
  ⟨.emptyWithCapacity, .emptyWithCapacity, (by grind)⟩

def Std.HashMap.push {α β : Type} [BEq α] [Hashable α]
  (m : Std.HashMap α (Array β)) (k : α) (v : β) :=
  m.alter k fun
    | .none => #[v]
    | .some arr => arr.push v

@[simp, grind =]
theorem Std.HashMap.mem_push {α β : Type}
  [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
  {m : Std.HashMap α (Array β)} {k : α} {v : β} {k' : α}
  : k' ∈ (m.push k v) ↔ (k == k') = true ∨ k' ∈ m := by
  unfold push
  if hk : k == k'
  then grind
  else grind

def Graph.parseNode (graph : Graph) (line : String) : IO Graph := do
  let mut graph := graph
  match line.splitOn ": " with
  | [inNode, sfx] =>
    for outNode in sfx.splitOn " " do
      graph :=
        { outEdges := graph.outEdges.push inNode outNode
          |>.insertIfNew outNode #[]
        , inEdges := graph.inEdges.push outNode inNode
          |>.insertIfNew inNode #[]
        , mem_outEdges_inEdges_iff x := (by
          have := graph.3 x
          grind) }
    return graph
  | _ => throw <| IO.userError s!"Bad input line: {line}"

def Graph.parseLines (lines : Array String) : IO Graph :=
  lines.foldlM (·.parseNode ·) .empty

def parseInput : IO Graph := do
  Graph.parseLines <| <- (<- IO.getStdin).lines

def topSort (graph : Graph) : Array String := Id.run do
  letI Arr := (Array String)
  letI Set := (Std.HashMap String Unit)
  let rec dfs (n : String) : Nat ->
    StateT Set (StateM Arr) Unit
    | 0 => pure ()
    | fuel + 1 => do
      if n ∈ (<- getThe Set) then return () else
      modifyThe Set (·.insert n ())
      if h : n ∈ graph.outEdges then
      for dst in graph.outEdges[n] do
        dfs dst fuel
      modifyThe Arr (·.push n)
  let dfsAll : StateT Set (StateM Arr) Unit := do
    for (node, _) in graph.inEdges do
      dfs node graph.inEdges.size
  return dfsAll.run' {} |>.run #[] |>.2.reverse

def countWaysToReach (graph : Graph) (first last : String) : Id Nat := do
  let mut counts : Std.HashMap String Nat := {(first, 1)}
  for node in topSort graph do
    counts := counts.insertIfNew node
      (graph.inEdges.getD node #[]
        |>.map (counts.getD · 0)
        |>.sum)
  return counts.getD last 0

def part1 (graph : Graph) : Id Nat :=
  countWaysToReach graph "you" "out"

def part2 (graph : Graph) : IO Nat := do
  let dacToFft <- countWaysToReach graph "dac" "fft"
  if dacToFft = 0 then
    let svrToFft <- countWaysToReach graph "svr" "fft"
    let fftToDac <- countWaysToReach graph "fft" "dac"
    let dacToOut <- countWaysToReach graph "dac" "out"
    return svrToFft * fftToDac * dacToOut
  else
    let svrToDac <- countWaysToReach graph "svr" "dac"
    let fftToOut <- countWaysToReach graph "fft" "out"
    return svrToDac * dacToFft * fftToOut

end Day11
open Day11

def main : IO Unit := do
  let input <- parseInput
  println! "Part 1: {<- part1 input}"
  println! "Part 2: {<- part2 input}"
