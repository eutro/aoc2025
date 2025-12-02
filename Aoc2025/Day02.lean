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
-- Take the first k decimal digits of n.
def Nat.truncLeft10 (n k : Nat) : Nat := n.shiftRight10 (n.numDigits - k)

-- First half, shorter half if odd.
def Nat.firstHalfRD (n : Nat) : Nat := n.shiftRight10 <| (n.numDigits + 1) / 2
-- Second half, longer half if odd.
def Nat.secondHalfRU (n : Nat) : Nat := n.truncRight10 <| (n.numDigits + 1) / 2
-- First half, longer half if odd.
def Nat.firstHalfRU (n : Nat) : Nat := n.shiftRight10 <| n.numDigits / 2
-- Second half, shorter half if odd.
def Nat.secondHalfRD (n : Nat) : Nat := n.truncRight10 <| n.numDigits / 2

-- Convert any natural to an invalid ID by pasting it after itself.
def Nat.duplicateToInvalidID (n : Nat) : Nat :=
  n.shiftLeft10 n.numDigits + n
-- Convert any natural to an invalid ID by repeatedly pasting it after itself.
def Nat.repeatToInvalidID (n : Nat) : Nat -> Nat
  | 0 => 0
  | k + 1 => (Nat.repeatToInvalidID n k).shiftLeft10 n.numDigits + n

-- Prop for whether a number is an invalid ID.
abbrev Nat.isInvalidID (n : Nat) : Prop :=
  n.firstHalfRU = n.secondHalfRD

def List.inclusiveRange (first last : Nat) : List Nat :=
  List.range' first (last - first + 1)
abbrev Interval.contains (ivl : Interval) (n : Nat) : Prop :=
  ivl.first <= n ∧ n <= ivl.last
def Interval.inclusiveRange (ivl : Interval) : List Nat :=
  List.inclusiveRange ivl.first ivl.last

-- Filter the invalid IDs in the interval's range. Too slow to be useful.
def Interval.filterInvalidIDsVeryNaive (ivl : Interval) : List Nat :=
  ivl.inclusiveRange.filter (·.isInvalidID)

-- Look through the range of only the first half of the IDs.
def Interval.filterInvalidIDs (ivl : Interval) : List Nat :=
  let halfRange := List.inclusiveRange ivl.first.firstHalfRD ivl.last.firstHalfRU
  let halfRangeInvalids := halfRange.map (·.duplicateToInvalidID)
  halfRangeInvalids.filter ivl.contains

-- Taken from Mathlib
def List.destutter' {α} (R : α → α → Prop) [DecidableRel R] : α → List α → List α
  | a, [] => [a]
  | a, h :: l => if R a h then a :: destutter' R h l else destutter' R a l
def List.destutter {α} (R : α → α → Prop) [DecidableRel R] : List α → List α
  | h :: l => destutter' R h l
  | [] => []
def List.deduplicate (ns : List Nat) := ns.mergeSort.destutter (· ≠ ·)

-- Look through the range of only the first k digits of the IDs.
def Interval.filterInvalidIDs' (ivl : Interval) : Id (List Nat) :=
  List.deduplicate <$>
  (List.inclusiveRange 2 ivl.last.numDigits).flatMapM fun k => do
  -- k is the number of repetitions we are doing
  (List.inclusiveRange ivl.first.numDigits ivl.last.numDigits).flatMapM fun ndigits => do
  -- c is the number of digits in the repetition
  unless k ∣ ndigits do return []
  let c := ndigits / k
  let partRange := List.inclusiveRange (10 ^ (c - 1)) (Nat.repeatToInvalidID 9 c)
  let partRangeInvalids := partRange.map (·.repeatToInvalidID k)
  return partRangeInvalids.filter ivl.contains

def part1 (intervals : List Interval) : Nat :=
  List.sum <| intervals.flatMap (·.filterInvalidIDs)

def part2 (intervals : List Interval) : Nat :=
  List.sum <| intervals.flatMap (·.filterInvalidIDs')

def String.toNatIO (s : String) : IO Nat :=
  match s.toNat? with
  | some i => pure i
  | none => throw <| IO.userError s!"Not a number: {s}"

def Interval.parse (s : String) : IO Interval :=
  match s.splitOn "-" with
  | [first, last] => do pure <| ⟨<- first.toNatIO, <- last.toNatIO⟩
  | _ => throw <| IO.userError s!"Bad interval: {s}"

def parseIntervals (s : String) : IO (List Interval) :=
  (s.splitOn ",").mapM Interval.parse

-- def testIntervals := parseIntervals "986003-1032361"
-- #eval do return (part1' (<- testIntervals))
-- #eval do return (part1 (<- testIntervals))
-- #eval Interval.filterInvalidIDsVeryNaive ⟨986003,1032361⟩
-- #eval Interval.filterInvalidIDs' ⟨2121212118,2121212124⟩

def parseInput : IO (List Interval) := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  let line := "".intercalate lines.toList
  parseIntervals line

end Day02
open Day02

def main : IO Unit := do
  let intervals <- parseInput
  -- IO.println s!"Intervals: {intervals}"
  IO.println s!"Part 1: {part1 intervals}"
  IO.println s!"Part 2: {part2 intervals}"
  return ()
