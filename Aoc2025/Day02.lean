namespace Day02
open Day02

structure Interval where
  first : Nat
  last : Nat

instance : ToString Interval where
  toString ivl := s!"{ivl.first}-{ivl.last}"

def Nat.numDigits (n : Nat) : Nat := (Nat.toDigits 10 n).length
-- Shift n right by k decimal digits.
def Nat.shiftRight10 (n k : Nat) : Nat := n / (10 ^ k)
-- Shift n left by k decimal digits.
def Nat.shiftLeft10 (n k : Nat) : Nat := n * (10 ^ k)
-- Take the last k decimal digits of n.
def Nat.truncRight10 (n k : Nat) : Nat := n % (10 ^ k)

-- First half, shorter half if odd.
def Nat.firstHalfRD (n : Nat) : Nat := n.shiftRight10 $ (n.numDigits + 1) / 2
-- Second half, longer half if odd.
def Nat.secondHalfRU (n : Nat) : Nat := n.truncRight10 $ (n.numDigits + 1) / 2
-- First half, longer half if odd.
def Nat.firstHalfRU (n : Nat) : Nat := n.shiftRight10 $ n.numDigits / 2
-- Second half, shorter half if odd.
def Nat.secondHalfRD (n : Nat) : Nat := n.truncRight10 $ n.numDigits / 2

-- Convert any integer to an invalid ID by pasting it after itself.
def Nat.duplicateToInvalidID (n : Nat) : Nat :=
  n.shiftLeft10 n.numDigits + n

-- Prop for whether a number is an invalid ID.
abbrev Nat.isInvalidID (n : Nat) : Prop :=
  n.firstHalfRU = n.secondHalfRD

def List.inclusiveRange (first last : Nat) : List Nat :=
  List.range' first (last - first + 1)

-- Filter the invalid IDs in the interval's range. Too slow to be useful.
def Interval.filterInvalidIDsVeryNaive (ivl : Interval) : List Nat :=
  let fullRange := List.inclusiveRange ivl.first ivl.last
  fullRange.filter (·.isInvalidID)

abbrev Interval.contains (ivl : Interval) (n : Nat) : Prop :=
  ivl.first <= n ∧ n <= ivl.last

-- Look through the range of only the first half of the IDs.
def Interval.filterInvalidIDsNaive (ivl : Interval) : List Nat :=
  let halfRange := List.inclusiveRange ivl.first.firstHalfRD ivl.last.firstHalfRU
  let halfRangeInvalids := halfRange.map (·.duplicateToInvalidID)
  halfRangeInvalids.filter (ivl.contains)

def part1 (intervals : List Interval) : Nat :=
  (intervals.flatMap (·.filterInvalidIDsNaive)).sum

def part2 (_intervals : List Interval) : Nat := 0

def String.toNatIO (s : String) : IO Nat :=
  match s.toNat? with
  | some i => pure i
  | none => throw $ IO.userError s!"Not a number: {s}"

def Interval.parse (s : String) : IO Interval :=
  match s.splitOn "-" with
  | [first, last] => do pure $ ⟨<- first.toNatIO, <- last.toNatIO⟩
  | _ => throw $ IO.userError s!"Bad interval: {s}"

def parseIntervals (s : String) : IO (List Interval) :=
  (s.splitOn ",").mapM Interval.parse

-- def testIntervals := parseIntervals "986003-1032361"
-- #eval do return (part1' (<- testIntervals))
-- #eval do return (part1 (<- testIntervals))
-- #eval Interval.filterInvalidIDsVeryNaive ⟨986003,1032361⟩
-- #eval Interval.filterInvalidIDsNaive ⟨986003,1032361⟩

def parseInput : IO (List Interval) := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  let line := "".intercalate lines.toList
  parseIntervals line

end Day02
open Day02

def main : IO Unit := do
  let intervals <- parseInput
  IO.println s!"Intervals: {intervals}"
  IO.println s!"Part 1: {part1 intervals}"
  IO.println s!"Part 2: {part2 intervals}"
  return ()
