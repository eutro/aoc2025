namespace String

def toNatIO (s : String) : IO Nat :=
  match s.toNat? with
  | some i => pure i
  | none => throw <| IO.userError s!"Not a number: {s}"

end String
