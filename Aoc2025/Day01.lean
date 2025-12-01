abbrev Wheel := Int

def part1 (cmds : Array Int) :=
  let step : Int × Int -> Int -> Int × Int
    | ⟨state, counter⟩, command =>
      let state' := (state + command) % 100;
      let δcounter := if state' = 0 then 1 else 0
      ⟨state', counter + δcounter⟩
  Array.foldl step ⟨50, 0⟩ cmds

def part2 (cmds : Array Int) :=
  part1 (cmds.flatMap (fun n ↦ Array.replicate n.natAbs n.sign))

def readCommand (s : String) : Int :=
  let sign := match s.front with
    | 'L' => -1
    | 'R' => 1
    | _ => 0
  let mag := (s.drop 1).toInt!
  sign * mag

def main : IO Unit := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  let commands := lines.map readCommand
  IO.println s!"Part 1: {part1 commands}!"
  IO.println s!"Part 2: {part2 commands}!"
  return ()
