namespace Day03
open Day03

abbrev Digit := Fin 10
abbrev Bank := List Digit

def Bank.parse (line : String) : IO Bank := do
  List.mapM (fun c =>
   if c.isDigit
   then pure <| Fin.ofNat _ (c.toNat - '0'.toNat)
   else throw <| IO.userError s!"Bad battery: {c}") line.toList

def parseInput : IO (List Bank) := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  lines.toList.mapM Bank.parse

def List.foldDigits (digits : List Digit) : Nat :=
  List.foldl (10 * · + ·.toNat) 0 digits

def Bank.isJoltage (bank : Bank) (n : Nat) :=
  ∃ l : Bank,
  l.Sublist bank → 
  l.length = 2 → 
  l.foldDigits = n

def Bank.allJoltageLists2 (bank : Bank) : List Bank :=
  let rec loop (bank : Bank) : List (Digit × Digit) :=
    match bank with
    | [] | [_] => []
    | [x, y] => [(x, y)]
    | x :: tail => List.map (fun y => (x, y)) tail ++ loop tail
  List.map (fun (x, y) => [x, y]) (loop bank)

def Bank.largestJoltage2 (bank : Bank) : Nat :=
  let allJoltages := bank.allJoltageLists2.map List.foldDigits
  if h : allJoltages = [] then 0 else allJoltages.max h

def Bank.largestJoltage (bank : Bank) (len : Nat) (hlen : 0 < len) : Nat :=
  -- LJ[i, n] = "largest joltage at list length i with n batteries"
  -- LJ[0,     n    ] = 0
  -- LJ[i + 1, 0    ] = (max_{0≤j≤i} LJ[j, 0]) +
  -- LJ[i + 1, n + 1] = (max_{0≤j≤i} 10 * i + LJ[j, n]) +
  --                    (max_{0≤j≤i} LJ[j, n + 1])
  let rec loop (bank : Bank) : Σ' l : List (Vector Nat (len + 1)), l ≠ [] :=
    match bank with
    | [] => ⟨[Vector.replicate _ 0], (by grind)⟩
    | d :: bank' =>
      let ⟨dp, hdp⟩ := loop bank'
      let row :=
        (Vector.replicate _ ()).mapFinIdx (fun n () hn =>
          let cols := List.map (fun row =>
            let useNext := row.get ⟨n, hn⟩
            match n, hn with
            | 0, _ => useNext
            | n' + 1, hn' =>
              let useThis := 10 * (row.get ⟨n', _⟩) + d.toNat
              max useNext useThis)
            dp
          have hcols : cols ≠ [] := by
            intro heq
            apply hdp
            apply List.map_eq_nil_iff.mp heq
            omega
          cols.max hcols)
      ⟨row :: dp, (List.cons_ne_nil _ _)⟩
  let ⟨dp, hdp⟩ := loop bank.reverse
  let row := dp.head hdp
  row.get (Fin.mk len (by omega))

def part1 (banks : List Bank) : Nat :=
  List.sum <| banks.map Bank.largestJoltage2

def part2 (banks : List Bank) : Nat :=
  List.sum <| banks.map (·.largestJoltage 12 (by omega))

end Day03
open Day03

def main : IO Unit := do
  let banks <- parseInput
  IO.println s!"Part 1: {part1 banks}"
  IO.println s!"Part 2: {part2 banks}"
  return ()

