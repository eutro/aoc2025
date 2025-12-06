import Aoc2025.Util.Parse

@[ext]
structure Interval where
  first : Nat
  last : Nat
deriving DecidableEq, Hashable, Inhabited, Nonempty, Repr, TypeName

def List.inclusiveRange (first last : Nat) : List Nat :=
  List.range' first (last - first + 1)

namespace Interval

variable (ivl : Interval)

instance : ToString Interval where
  toString ivl := s!"{ivl.first}-{ivl.last}"

def parse (s : String) : IO Interval :=
  match s.splitOn "-" with
  | [first, last] => do pure <| ⟨<- first.toNatIO, <- last.toNatIO⟩
  | _ => throw <| IO.userError s!"Bad interval: {s}"

abbrev contains (n : Nat) : Prop :=
  ivl.first <= n ∧ n <= ivl.last

def inclusiveRange : List Nat :=
  List.inclusiveRange ivl.first ivl.last

def size : Nat :=
  ivl.last - ivl.first + 1

abbrev ofPair : (Nat × Nat) -> Interval
  | (first, last) => ⟨first, last⟩

end Interval
