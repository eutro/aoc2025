import Aoc2025.Util
import Std.Data.HashMap

namespace Day10
open Day10

abbrev Button (ℓ : Nat) :=
  Array (Fin ℓ)

def Button.toggle {ℓ} (button : Button ℓ) (lights : Vector Bool ℓ)
  : Vector Bool ℓ := Id.run do
  let mut lights := lights
  for light in button do
    lights := ⟨lights.1.modify light (!·), (by grind)⟩
  return lights

def Button.increase {ℓ} (button : Button ℓ) (lights : Vector Nat ℓ)
  : Vector Nat ℓ := Id.run do
  let mut lights := lights
  for light in button do
    lights := ⟨lights.1.modify light (· + 1), (by grind)⟩
  return lights

structure Machine where
  size : Nat
  lights : Vector Bool size
  buttons : Array (Button size)
  joltages : Vector Nat size
deriving Repr, DecidableEq

def String.removeDelimiters (s : String) : String :=
  s.drop 1 |>.dropRight 1

def Machine.parse (line : String) : IO Machine := do
  let splits := line.splitOn " " |>.toArray
  if h : splits.size < 2 then
    throw <| IO.userError s!"Bad machine: {line}"
  else
  let lightsPart <- splits[0]
    |>.removeDelimiters
    |>.toList.toArray.mapM (fun
      | '.' => pure false
      | '#' => pure true
      | c => throw <| IO.userError s!"Bad light: {c}")
  let size := lightsPart.size
  let joltagesPart <- splits[splits.size - 1]
    |>.removeDelimiters
    |>.splitOn ","
    |>.toArray.mapM (·.toNatIO)
  if hj : joltagesPart.size ≠ size then
    throw <| IO.userError s!"Bad joltages: {joltagesPart}"
  else
  let buttonsPart <- splits.drop 1
    |>.take (splits.size - 2)
    |>.mapM (fun s => s
    |>.removeDelimiters
    |>.splitOn ","
    |>.toArray.mapM (fun n => do
        let n <- n.toNatIO
        if h : n < size
        then pure <| Fin.mk n h
        else throw <| IO.userError s!"Bad button: {n}"))
  return Machine.mk
    size
    ⟨lightsPart, (by rfl)⟩
    buttonsPart
    ⟨joltagesPart, (by grind)⟩

structure SearchNode1 (m : Machine) where
  state : Vector Bool m.size
deriving Repr, DecidableEq
instance SearchNode1.instHashable m : Hashable (SearchNode1 m) where
  hash n := hash n.state.toArray

def maxFuel := 2 ^ 20
def fuelArray := Array.range' 1 maxFuel

def Machine.computePresses1 (m : Machine) : IO Nat := do
  let initState := ⟨.replicate _ false⟩
  let mut queue : Array (SearchNode1 m) := #[initState]
  let mut seen : Std.HashMap (SearchNode1 m) Unit := {(initState, ())}
  for steps in fuelArray do
    let mut queue' := #[]
    for state in queue do
      for button in m.buttons do
        let state' := ⟨button.toggle state.1⟩
        if seen.contains state' then continue
        if state'.1 = m.lights then return steps
        queue' := queue'.push state'
    queue := queue'
  throw <| IO.userError s!"Bad machine: {repr m}"

def part1 (machines : Array Machine) : IO Nat := do
  let tasks <- machines.mapM (IO.asTask <| ·.computePresses1)
  let presses <- liftExcept <| tasks.mapM Task.get
  return presses.sum

structure Equation where
  vars : Array Nat
  result : Nat
deriving Repr

structure SatProgram (m : Machine) where
  eqns : Array Equation
deriving Repr

def Machine.toEquations (m : Machine) : Array Equation := Id.run do
  let mut ⟨eqns, _⟩ := m.joltages.map (Equation.mk #[] ·)
  for (button, buttonIdx) in m.buttons.zipIdx do
    for idx in button do
      eqns := eqns.modify idx fun eqn =>
        { eqn with vars := eqn.vars.push buttonIdx }
  eqns

instance : ToString Equation where
  toString eqn :=
    let varsStr := eqn.vars.map (s!"b{·}") |>.toList |> " ".intercalate
    s!"(assert (= (+ {varsStr}) {eqn.result}))"

def Machine.toSatProgram (m : Machine) : SatProgram m := Id.run do
  ⟨m.toEquations⟩

instance Machine.instToString m : ToString (SatProgram m) where
  toString p :=
    let consts := List.range m.buttons.size
        |>.map (fun n =>
          s!"(declare-const b{n} Int)\n(assert (<= 0 b{n}))")
        |> "\n".intercalate
    let eqns := p.eqns.map toString
        |>.toList
        |> "\n".intercalate
    let objective := List.range m.buttons.size
        |>.map (s!"b{·}")
        |> " ".intercalate
        |> (s!"(+ {·})")
    let minimizer := s!"(minimize {objective})"
    s!"{consts}\n{eqns}\n{minimizer}\n(check-sat)\n(eval {objective})"

def Machine.computePresses2 (m : Machine) : IO Nat := do
  let result <-
    IO.Process.run
      { cmd := "z3"
      , args := #["-in"] }
      (some <| toString m.toSatProgram)
  match result.splitOn "\n" with
  | ["sat", ans, ""] => ans.toNatIO
  | _ => throw <| IO.userError s!"Bad z3 result: {result}"

def part2 (machines : Array Machine) : IO Nat := do
  let tasks <- machines.mapM (IO.asTask <| ·.computePresses2)
  let presses <- liftExcept <| tasks.mapM Task.get
  return presses.sum

def parseInput : IO (Array Machine) := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  lines.mapM Machine.parse

end Day10
open Day10

def main : IO Unit := do
  let input <- parseInput
  println! "Part 1: {<- part1 input}"
  println! "Part 2: {<- part2 input}"
