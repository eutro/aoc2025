namespace String

def toNatIO (s : String) : IO Nat :=
  match s.toNat? with
  | some i => pure i
  | none => throw <| IO.userError s!"Not a number: {s}"

def toIntIO (s : String) : IO Int :=
  match s.toInt? with
  | some i => pure i
  | none => throw <| IO.userError s!"Not a number: {s}"

end String

namespace Option
variable {α : Type}

def getIO (opt : Option α) : IO α :=
  match opt with
  | some x => pure x
  | none => throw <| IO.userError s!"Empty option"

end Option
