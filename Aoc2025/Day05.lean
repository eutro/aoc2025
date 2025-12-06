import Aoc2025.Util
import Std.Data.TreeMap

structure IntervalSet where
  startToEnd : Std.TreeMap Nat Nat
deriving Repr

namespace IntervalSet

variable (set : IntervalSet)

structure WF : Prop where
  startToEnd_le : ∀ start (h : start ∈ set.startToEnd),
    start <= set.startToEnd[start]

def empty : IntervalSet := ⟨.empty⟩

def containingInterval (x : Nat) : Option Interval :=
  Interval.ofPair <$>
  ((set.startToEnd.getEntryLE? x
  ).filter (fun (_, last) => x <= last))

def memb (x : Nat) : Bool :=
  (set.containingInterval x).isSome

def Mem (x : Nat) :=
  ∃ first, ∃ (h : first ∈ set.startToEnd),
  first <= x ∧ x <= set.startToEnd[first]

variable {m : Std.TreeMap Nat Nat}
axiom getEntryLE?_le {x : Nat} {pair : Nat × Nat}
  : m.getEntryLE? x = some pair ->
    ∃ _ : pair.1 ∈ m, m[pair.1] = pair.2 ∧ pair.1 <= x

def Mem_of_containingInterval (x : Nat) {ivl : Interval} 
  : set.containingInterval x = some ivl -> 
    set.Mem x := by
  intro h
  simp [containingInterval] at h
  have ⟨first, last, ⟨⟨heqget, hle⟩, hivl⟩⟩ := h
  exists first
  have hle := getEntryLE?_le heqget
  grind

def nextInterval (last : Nat) : Option Interval :=
  Interval.ofPair <$> set.startToEnd.getEntryGT? last

-- Get all the intervals with start points in in (a, b] 
def intervalsAfterAux (ivl : Interval) (fuel : Nat) : List Interval :=
  match fuel, set.nextInterval ivl.first with
  | fuel' + 1, .some next =>
    if next.first <= ivl.last + 1 then
      next :: intervalsAfterAux ⟨next.last, ivl.last⟩ fuel'
    else []
  | _, _ => []

def intervalsAfter (ivl : Interval) : List Interval :=
  set.intervalsAfterAux ivl set.startToEnd.size

theorem WF.erase {set} {first} : WF set -> WF ⟨set.startToEnd.erase first⟩ := by
  intro ⟨hwf⟩
  constructor <;> simp
  · grind

theorem WF.insert {set} {first last} :
  first <= last ->
  WF set ->
  WF ⟨set.startToEnd.insert first last⟩ := by
  intro hle ⟨hwf⟩
  constructor <;> simp
  · grind

def insert (ivl : Interval) : IntervalSet := Id.run do
  if ¬ivl.first <= ivl.last then return set
  let mut set' := set
  let mut toInsert := ivl
  let initial := set'.containingInterval (ivl.first - 1)
  let trailing := set'.intervalsAfter ⟨ivl.first - 1, ivl.last⟩
  match initial with
  | .some before =>
    toInsert := ⟨before.first, max before.last toInsert.last⟩
    set' := ⟨set'.startToEnd.erase before.first⟩
    pure ()
  | .none => pure ()
  for intersecting in trailing do
    set' := ⟨set'.startToEnd.erase intersecting.first⟩
  match trailing.getLast? with
  | .some after =>
    toInsert := ⟨toInsert.first, max after.last toInsert.last⟩
    pure ()
  | .none => pure ()
  ⟨set'.startToEnd.insert toInsert.first toInsert.last⟩

def allIntervals : List Interval :=
  (fun ⟨first, last⟩ => ⟨first, last⟩) <$> set.startToEnd.toList

instance : Repr IntervalSet where
  reprPrec m prec := Repr.addAppParen ("IntervalSet.ofList " ++ repr m.allIntervals) prec

def size : Nat :=
  (set.allIntervals.map Interval.size).sum

def ofList (ivl : List Interval) : IntervalSet := ivl.foldl .insert .empty
def ofArray (ivl : Array Interval) : IntervalSet := ivl.foldl .insert .empty

end IntervalSet

namespace Day04
open Day04

def parseInput : IO (Array Interval × Array Nat) := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  let splitIdx <- match lines.finIdxOf? "" with
    | .some i => pure i
    | .none => throw <| IO.userError "No empty line"
  let intervals <- (lines.take splitIdx).mapM Interval.parse
  let numbers <- (lines.drop (splitIdx + 1)).mapM String.toNatIO
  return (intervals, numbers)

def part1Naive (set : Array Interval) (numbers : Array Nat) : Nat :=
  numbers.countP (fun n => set.any (·.contains n))
def part1 (set : IntervalSet) (numbers : Array Nat) : Nat :=
  numbers.countP set.memb

def part2 (set : IntervalSet) : Nat :=
  set.size

end Day04
open Day04

def main : IO Unit := do
  let (intervals, numbers) <- parseInput
  let set := IntervalSet.ofArray intervals
  IO.println s!"Part 1: {part1 set numbers}"
  IO.println s!"Part 2: {part2 set}"
  return ()
