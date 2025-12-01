abbrev Dial := Int
def dialSize : Nat := 100
def dialInit : Dial := 50

abbrev DialState α := StateM Dial α

-- Rotate the dial by the given command.
def stepDial (command : Int) : DialState Unit := do
  let dial <- get
  set $ (dial + command) % dialSize

theorem step_dial_homomorphism 
  : ∀ c0 c1, stepDial (c0 + c1) = (do stepDial c0; stepDial c1) := by
  intros
  apply StateT.ext
  intros
  simp [stepDial]
  grind

-- Rotate the dial at once, only counting 0 at the end.
def stepAtomic (command : Int) : DialState Int := do
  stepDial command
  let dial' <- get
  return if dial' = 0 then 1 else 0

-- Rotate the dial one step at a time, counting every 0.
def stepIncrementalSlow (command : Int) : DialState Int := do
  let substates <- (List.replicate command.natAbs command.sign).mapM stepAtomic
  return substates.sum

def stepIncremental (command : Int) : DialState Int := do
  let dial <- get
  stepDial command
  let rawDial' := dial + command
  let mut fullRotations := rawDial'.natAbs / dialSize
  if rawDial' <= 0 ∧ dial % dialSize != 0 then
    fullRotations := fullRotations + 1
  return fullRotations

-- Run the stepping function over the commands.
def runPart (step : Int -> DialState Int) (commands : Array Int) : Int :=
  let allState := commands.mapM step
  let runAll := allState.run' dialInit
  runAll.sum

def part1 (commands : Array Int) : Int :=
  runPart stepAtomic commands

def part2 (commands : Array Int) :=
  runPart stepIncremental commands

-- Read a line of input [LR]NNN as a rotation, L negative, R positive.
def parseCommand (s : String) : IO Int := do
  let sign <- match s.front with
    | 'L' => pure $ -1
    | 'R' => pure 1
    | c => throw (IO.userError s!"Bad prefix: {c}")
  let mag <- match (s.drop 1).toInt? with
    | some mag => pure mag
    | none => throw (IO.userError s!"Bad argument: {(s.drop 1)}")
  return sign * mag

-- Read stdin into an array of commands.
def parseInput : IO (Array Int) := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  let commands <- lines.mapM parseCommand
  return commands

def main : IO Unit := do
  let commands <- parseInput
  IO.println s!"Part 1: {part1 commands}"
  IO.println s!"Part 2: {part2 commands}"
  return ()
