namespace Day01

abbrev dialSize : Int := 100
structure Dial where
  toInt : Int
  isNormalised : toInt = toInt % dialSize

def dialInit : Dial := ⟨50, by grind⟩

theorem Dial.toInt_nonneg (d : Dial) : 0 <= d.toInt := by
  rw [d.isNormalised]; grind

/-- Note: DialState α over a monoid ⟨α, ×⟩ has the monoidal
  structure ((×) <$> · <*> ·), which we will define
  homomorphisms into. -/
abbrev DialState α := StateM Dial α

-- Rotate the dial by the given command.
def stepDial (command : Int) : DialState Unit := do
  let dial <- get
  set $ Dial.mk ((dial.toInt + command) % dialSize) (by grind)

/-- stepDial is a monoid homomorphism (ℤ, +) → DialState Unit. -/
theorem stepDial_hom (c0 c1 : Int)
  : stepDial (c0 + c1) = stepDial c0 *> stepDial c1 := by
  intros; ext
  simp [stepDial]
  grind

@[simp]
theorem stepDial_zero : stepDial 0 = pure ⟨⟩ := by
  ext d; simp [stepDial]; congr
  rw [← d.isNormalised]

-- Rotate the dial at once, only counting 0 at the end.
def stepAtomic (command : Int) : DialState Nat := do
  stepDial command
  let dial' <- get
  return if dial'.toInt = 0 then 1 else 0

-- Rotate the dial one step at a time, counting every 0.
def stepIncrementalSlow (command : Int) : DialState Nat :=
  List.sum <$> (List.replicate command.natAbs command.sign).mapM stepAtomic

theorem Int.add_same_sign_eq (c0 c1 : Int)
  : c0.sign = c1.sign →
    (c0 + c1).sign = c1.sign := by
  intro
  if _ : c1 = 0
  then grind [Int.eq_zero_of_sign_eq_zero]
  else if _ : c1 > 0
  then grind [Int.sign_eq_one_iff_pos]
  else grind [Int.sign_eq_neg_one_iff_neg]

theorem Int.natAbs_add_of_same_sign (c0 c1 : Int)
  : c0.sign = c1.sign →
    (c0 + c1).natAbs = c0.natAbs + c1.natAbs := by
  intro
  if _ : c1 = 0 then grind
  else if _ : c1 > 0
  then grind [Int.sign_eq_one_iff_pos, Int.natAbs_add_of_nonneg]
  else grind [Int.sign_eq_neg_one_iff_neg, Int.natAbs_add_of_nonpos]

/- stepIncrementalSlow is a monoid homomorphism
 from the fixed-signed integers to DialState Nat. -/
theorem stepIncrementalSlow_hom (c0 c1 : Int)
  : c0.sign = c1.sign →
    stepIncrementalSlow (c0 + c1)
    = ((· + ·) <$> stepIncrementalSlow c0 <*> stepIncrementalSlow c1) := by
  intros hsign; apply StateT.ext; intro dial0
  simp [stepIncrementalSlow]
  rw [Int.natAbs_add_of_same_sign _ _ hsign,
       ← List.replicate_append_replicate, List.mapM_append,
       Int.add_same_sign_eq _ _ hsign, hsign]
  simp

/- we could probably show that this is also a monoid homomorphism -/
def stepIncremental (command : Int) : DialState Nat := do
  let dial <- get
  stepDial command
  let rawDial' := dial.toInt + command
  let mut fullRotations := (rawDial'.natAbs / dialSize).natAbs
  if rawDial' <= 0 ∧ dial.toInt != 0 then
    fullRotations := fullRotations + 1
  return fullRotations

-- Run the stepping function over the commands.
def runPart (step : Int -> DialState Nat) (commands : Array Int) : Nat :=
  let allState := commands.mapM step
  let runAll := allState.run' dialInit
  runAll.sum

def part1 (commands : Array Int) : Nat :=
  runPart stepAtomic commands

def part2 (commands : Array Int) : Nat :=
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

end Day01
open Day01

def main : IO Unit := do
  let commands <- parseInput
  IO.println s!"Part 1: {part1 commands}"
  IO.println s!"Part 2: {part2 commands}"
  return ()
