import Std.Tactic.Do

namespace Day01

abbrev dialSize : Nat := 100
abbrev Dial := Fin dialSize
def dialInit : Dial := 50

/-- Note: DialState α over a monoid ⟨α, ×⟩ has the monoidal
  structure ((×) <$> · <*> ·), which we will define
  homomorphisms into. -/
abbrev DialState α := StateM Dial α

def stepDial0 (command : Int) (dial : Dial) : Dial :=
  ⟨((dial + command) % dialSize).toNat, (by grind)⟩

-- Rotate the dial by the given command.
def stepDial (command : Int) : DialState Unit := do
  modify (stepDial0 command)

-- Rotate the dial at once, only counting 0 at the end.
def stepAtomic (command : Int) : DialState Nat := do
  stepDial command
  let dial' <- get
  return if dial' = 0 then 1 else 0

-- Rotate the dial one step at a time, counting every 0.
def stepIncrementalSlow (command : Int) : DialState Nat :=
  List.sum <$> (List.replicate command.natAbs command.sign).mapM stepAtomic

-- This is proven to be equivalent to stepIncrementalSlow above.
def stepIncremental (command : Int) : DialState Nat := do
  let dial <- get
  stepDial command
  let rawDial' := dial + command
  let mut fullRotations := rawDial'.natAbs / dialSize
  if rawDial' ≤ 0 ∧ dial ≠ 0 then
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

-- Proofs
namespace Day01
open Day01

theorem Dial.toInt_nonneg (d : Dial) : 0 <= ↑d := by grind

@[grind]
theorem Dial.lt_dialSize (dial : Dial) : dial < (dialSize : Int) := by
  norm_cast ; grind

/-- stepDial is a monoid homomorphism (ℤ, +) → DialState Unit. -/
theorem stepDial_hom (c0 c1 : Int)
  : stepDial (c0 + c1) = stepDial c0 *> stepDial c1 := by
  intros; ext
  simp [stepDial, stepDial0]
  grind

@[simp]
theorem stepDial_zero : stepDial 0 = pure () := by
  ext d; simp [stepDial, stepDial0]; congr
  suffices ↑↑d % 100 = ↑↑d by grind
  grind

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
  else have _ : c1 < 0 := by grind
       grind [Int.sign_eq_neg_one_iff_neg, Int.natAbs_add_of_nonpos]

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

universe u
def Int.mag_rec :
  {motive : Int → Sort u} → 
  (zero : motive 0) → (one : motive 1) → (mone : motive (-1)) →
  (succ : (n : Int) → 0 ≠ n → motive n → motive n.sign → motive (n + n.sign)) →
  (t : Int) →
  motive t := by
  intros motive h0 h1 hm1 hplus t
  cases t
  case ofNat n =>
    cases n
    case zero => exact h0
    case succ n' =>
      induction n'
      case zero => exact h1
      case succ n' ih =>
        simp ; apply hplus
        · grind
        · exact ih
        · exact h1
  case negSucc n =>
    induction n
    case zero => exact hm1
    case succ n' ih =>
      rw [← Int.negSucc_sub_one, Int.sub_eq_add_neg]
      apply hplus
      · simp
      · exact ih
      · exact hm1

def Int.ring_rec :
  {motive : Int → Sort u} → 
  (zero : motive 0) → (one : motive 1) → (mone : motive (-1)) →
  (add : (n n' : Int) → n ≠ 0 → n.sign = n'.sign → motive n → motive n' → motive (n + n')) →
  (t : Int) →
  motive t := by
  intros motive h0 h1 hm1 hplus t
  induction t using Int.mag_rec <;> try assumption
  case succ =>
    apply hplus <;>
      (first | assumption | grind [Int.sign_sign])

theorem Int.natAbs_add_sign (n : Int)
  : n ≠ 0 → (n + n.sign).natAbs = n.natAbs + 1 := by
  intro h
  cases n
  · rw [Int.natAbs_add_of_nonneg]
    · grind [Int.natAbs_sign_of_ne_zero]
    · simp
    · simp
  · rw [Int.natAbs_add_of_nonpos]
    · grind [Int.natAbs_sign_of_ne_zero]
    · grind
    · simp

theorem stepIncrementalSlow_state (c0 : Int)
  : stepIncrementalSlow c0 *> pure () = stepDial c0 := by
  induction c0 using Int.ring_rec
  case add hn hsign ih0 ih1 =>
    rw [stepDial_hom, stepIncrementalSlow_hom _ _ hsign, ← ih0, ← ih1]
    ext : 2 ; simp
  all_goals
    ext : 2
    simp [stepIncrementalSlow, stepAtomic]

@[grind]
theorem Int.sign_zero (n : Int)
  : n.sign = 0 ↔ n = 0 := by
  cases n
  case ofNat n => cases n <;> simp <;> grind
  case negSucc n => simp

theorem stepIncremental_zero
  : stepIncremental 0 = pure 0 := by
  ext : 2
  simp [stepIncremental]

theorem stepIncremental_one
  : stepIncremental 1 = stepAtomic 1 := by
  ext : 2
  simp [stepIncremental, stepAtomic, stepDial]
  split
  · exfalso ; grind
  split <;> simp [stepDial0] at * <;> grind

theorem stepIncremental_minus_one
  : stepIncremental (-1) = stepAtomic (-1) := by
  ext : 2
  simp [stepIncremental, stepAtomic, stepDial]
  split <;> split <;> simp [stepDial0] at *
  · grind
  case _ dial h _ =>
    have heq : dial = (0 : Int) := by grind
    simp at heq ; grind
  case _ dial h _ =>
    have hmodeq : (dialSize : Int) ∣ dial - 1 := by grind
    have hdial : dial = (1 : Int) := by grind
    rw [hdial] at h ; simp at h ; subst h
    contradiction
  case _ dial _ _ => grind

theorem stepIncremental_succ (c : Int)
  : 0 < c →
    stepIncremental (c + 1) =
    (· + ·) <$> stepIncremental c <*> stepIncremental 1 := by
  intro h
  ext : 2
  rw [stepIncremental_one]
  simp [stepIncremental, stepDial, stepAtomic, stepDial0]
  split <;> split <;> simp at * <;> grind

theorem stepIncremental_prec (c : Int)
  : 0 > c →
    stepIncremental (c - 1) =
    (· + ·) <$> stepIncremental c <*> stepIncremental (-1) := by
  intro h
  ext : 2
  rw [stepIncremental_minus_one]
  simp [stepIncremental, stepDial, stepAtomic, stepDial0]
  split <;> split <;> split <;> simp at * <;> try grind
  constructor
  case _ dial _ _ h =>
    simp at *
    generalize hdial0 : (dial + c) % dialSize = dial0 at *
    have hdial0' : dial0 = 1 := by grind
    subst hdial0'
    if h : dial + c <= 0 then grind else
    if h' : dial + (c - 1) <= 0 then
      have : dial = 0 := by grind
      subst dial
      simp at h
      omega
    else
      have : dial + c = 1 := by grind
      have : dial + (c - 1) = 0 := by grind
      grind
  case _ => grind

theorem eq_stepIncremental_stepIncrementalSlow (c : Int)
  : stepIncremental c = stepIncrementalSlow c := by
  induction c using Int.mag_rec
  · exact stepIncremental_zero
  · exact stepIncremental_one
  · exact stepIncremental_minus_one
  case succ n _ ih _ =>
    simp [Int.sign]
    split <;> simp at *
    · simp [stepIncremental_succ, stepIncrementalSlow_hom] <;> grind
    · rw [stepIncrementalSlow_hom, ← Int.sub_eq_add_neg, stepIncremental_prec]
        <;> first | simp | grind

end Day01
