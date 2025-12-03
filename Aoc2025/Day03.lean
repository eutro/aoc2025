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

-- LJ[l, n] = "largest joltage at list l with n batteries"
-- LJ[[],    n    ] = 0
-- LJ[d::l', 0    ] = LJ[l', 0]
-- LJ[d::l', n + 1] = max(LJ[l', n + 1], 10 * d + LJ[l', n])
def Bank.largestJoltageRev (bankRev : Bank) (len : Nat)
  : Vector Nat (len + 1) :=
  match bankRev with
  | [] => Vector.replicate _ 0
  | d :: bankRev' =>
    let dp := largestJoltageRev bankRev' len
    let row :=
      (Vector.replicate _ ()).mapFinIdx (fun n () hn =>
        match n, hn with
        | 0,      h0   => dp[0]
        | n' + 1, hn'  => max dp[n' + 1] (10 * dp[n'] + d))
    row

def Bank.largestJoltage (bank : Bank) (len : Nat) : Nat :=
  (Bank.largestJoltageRev bank.reverse len)[len]

def part1 (banks : List Bank) : Nat :=
  List.sum <| banks.map (·.largestJoltage 2)

def part2 (banks : List Bank) : Nat :=
  List.sum <| banks.map (·.largestJoltage 12)

end Day03
open Day03

def main : IO Unit := do
  let banks <- parseInput
  IO.println s!"Part 1: {part1 banks}"
  IO.println s!"Part 2: {part2 banks}"
  return ()

-- Proofs
namespace Day03
open Day03

-- Simple digits -> number
def List.foldDigits (digits : List Digit) : Nat :=
  List.foldl (10 * · + ·.toNat) 0 digits

example : List.foldDigits [1, 2, 3] = 123 := by rfl
example : List.foldDigits [] = 0 := by rfl

@[simp]
theorem List.foldDigits_nil : List.foldDigits [] = 0 := by rfl
@[simp]
theorem List.foldDigits_append (d : Digit) (digits : List Digit)
  : List.foldDigits (digits ++ [d]) =
    10 * List.foldDigits digits + d := by
  simp [List.foldDigits]

-- n is a joltage that can be obtained by turning on the given subbank, which is
-- at most len long.
structure Bank.IsJoltage (subbank bank : Bank) (len : Nat) (n : Nat) : Prop where
  -- The sequence to obtain n is indeed in bank.
  subbank_Sublist : subbank.Sublist bank
  -- The subsequence has the correct length. (The question requests
  -- *exactly* n batteries on, but that always holds for the largest
  -- joltage (proof not formalised).)
  subbank_length : subbank.length ≤ len
  -- The subsequence does add up to n.
  subbank_foldDigits_eq : subbank.foldDigits = n

-- A given joltage is the largest if it is at least as large as any other joltage.
def Bank.joltageIsLargest (subbank bank : Bank) (len : Nat) (n : Nat) :=
  ∀ n' : Nat, subbank.IsJoltage bank len n' → n' ≤ n

-- The largest joltage is the joltage which is larger than any other.
structure Bank.LargestJoltage (subbank bank : Bank) (len : Nat) (n : Nat) : Prop where
  -- This is a joltage.
  isJoltage : subbank.IsJoltage bank len n
  -- This is larger than any other joltage.
  isLargest (subbank' : Bank) : subbank'.joltageIsLargest bank len n

theorem Bank.IsJoltage.nil {w : Bank} {len : Nat} {n : Nat}
  : IsJoltage w [] len n -> n = 0 := by
  intro ⟨hw, _, heq⟩
  have hw' : w = [] := List.eq_nil_of_sublist_nil hw
  rw [hw'] at heq
  simp at heq
  rw [heq]

theorem Bank.IsJoltage.of_nil {len : Nat}
  : IsJoltage [] [] len 0 := by
  constructor <;> simp

theorem Bank.LargestJoltage.of_nil {len : Nat}
  : LargestJoltage [] [] len 0 := by
  constructor
  · exact IsJoltage.of_nil
  · intro _ n' hn' ; rw [hn'.nil] ; omega

theorem Bank.IsJoltage.zero {w bank : Bank} {n : Nat}
  : IsJoltage w bank 0 n -> n = 0 := by
  intro ⟨_, hw, heq⟩
  have hwnil : w = [] := by grind [List.length_eq_zero_iff]
  rw [← heq, hwnil] ; simp

theorem Bank.IsJoltage.of_zero {bank : Bank}
  : IsJoltage [] bank 0 0 := by
  apply mk <;> simp

-- Obtain another joltage by not turning this battery on.
theorem Bank.IsJoltage.of_cons_drop {d : Digit} {w bank : Bank} {len n : Nat}
  : IsJoltage w bank len n -> IsJoltage w (bank ++ [d]) len n := by
  intro ⟨_, _, _⟩
  apply mk <;> grind

-- Obtain another joltage by turning the next battery on.
theorem Bank.IsJoltage.of_cons_keep {d : Digit} {w bank : Bank} {len n : Nat}
  : IsJoltage w bank len n -> IsJoltage (w ++ [d]) (bank ++ [d]) (len + 1) (10 * n + d) := by
  intro ⟨_, _, _⟩
  apply mk <;> (simp ; grind)

-- Any joltage is obtained either by leaving the current battery off
-- (left), or turning the next one on (right).
theorem Bank.IsJoltage.cons_or_drop {d : Digit} {w bank : Bank} {len n : Nat}
  : IsJoltage w (bank ++ [d]) (len + 1) n ->
    (IsJoltage w bank (len + 1) n) ∨
    (∃ w' n',
      w = w' ++ [d] ∧
      n = 10 * n' + d ∧
      IsJoltage w' bank len n') := by
  generalize hbank' : bank ++ [d] = bank'
  intro ⟨hsl, hlen, heq⟩
  have hslrev := hsl.reverse
  generalize hwrev : w.reverse = wrev at hslrev
  generalize hbank'rev : bank'.reverse = bank'rev at hslrev
  cases hslrev
  case _ => exfalso; grind
  case _ rbank d' hsl' =>
    left
    have hrbank : bank.reverse = rbank := by grind
    constructor <;> grind
  case _ rw rbank d' hsl' =>
    right
    have hrbank : bank = rbank.reverse := by grind
    have hrw : w = rw.reverse ++ [d] := by grind
    exists rw.reverse
    exists rw.reverse.foldDigits
    constructor ; grind
    constructor ; rw [← heq, hrw] ; simp
    constructor <;> grind

theorem Bank.LargestJoltage.of_zero {bank : Bank}
  : LargestJoltage [] bank 0 0 := by
  constructor
  · exact IsJoltage.of_zero
  · intro _ n' hn' ; rw [hn'.zero] ; omega

@[simp] theorem Bank.largestJoltageRev_nil
    (len : Nat) (n : Nat) (hn : n < len + 1)
  : (largestJoltageRev [] len)[n] = 0 := by
  simp [largestJoltageRev]

theorem Bank.largestJoltageRev_cons_zero
    (bankRev : Bank) (d : Digit) (len : Nat)
  : (largestJoltageRev (d::bankRev) len)[0] =
    (largestJoltageRev bankRev len)[0] := by
  simp [largestJoltageRev]

@[simp] theorem Bank.largestJoltageRev_zero
    (bankRev : Bank) (len : Nat)
  : (largestJoltageRev bankRev len)[0] = 0 := by
  induction bankRev
  case nil => simp
  case cons _ ih =>
    simp [Bank.largestJoltageRev_cons_zero]
    exact ih

@[simp] theorem Bank.largestJoltageRev_cons_succ
    (bankRev : Bank) (d : Digit) (len : Nat) (n : Nat) (hn : n + 1 < len + 1)
  : (largestJoltageRev (d::bankRev) len)[n + 1] =
    max (largestJoltageRev bankRev len)[n + 1]
        (10 * (largestJoltageRev bankRev len)[n] + d) := by
  simp [largestJoltageRev]

-- largestJoltageRev does get the largest joltage of the reverse bank
-- This also constructs the witness subsequence, for fun.
def Bank.largestJoltageRev_isLargestJoltage
    (bankRev : Bank) (len : Nat) (n : Nat) (hn : n < len + 1)
  : Σ' w, LargestJoltage w bankRev.reverse n (largestJoltageRev bankRev len)[n] := by
  cases bankRev
  case nil => exists [] ; simp ; exact LargestJoltage.of_nil
  case cons d bankRev' =>
    cases n
    case zero => exists [] ; simp ; exact LargestJoltage.of_zero
    case succ n' =>
      simp
      have leftj := largestJoltageRev_isLargestJoltage
        bankRev' len (n' + 1) hn
      have rightj := largestJoltageRev_isLargestJoltage
        bankRev' len n' (by omega)
      -- At the inductive step we choose either to drop the battery or turn it on,
      -- whichever is better is the maximum of these two.
      let dropThis := (largestJoltageRev bankRev' len)[n' + 1]
      let useThis := 10 * (largestJoltageRev bankRev' len)[n'] + ↑d
      have hmax := Std.max_eq_or (a := dropThis) (b := useThis)
      -- This is morally just `cases hmax`
      if hleft : max dropThis useThis = dropThis
      then rw [hleft]
           exists leftj.1
           constructor
           · apply IsJoltage.of_cons_drop leftj.2.1
           · intro w' j' hj'
             cases hj'.cons_or_drop
             case _ hj' => apply leftj.2.2 w' j' hj'
             case _ hj' =>
               have ⟨_, ⟨_, ⟨_, ⟨_, hj'⟩⟩⟩⟩ := hj'
               have _ := rightj.2.2 _ _ hj'
               omega
      else have hright : max dropThis useThis = useThis := by
             cases hmax <;> grind
           rw [hright]
           exists (rightj.1 ++ [d])
           constructor
           · apply IsJoltage.of_cons_keep rightj.2.1
           · intro w' j' hj'
             cases hj'.cons_or_drop
             case _ hj' =>
               have _ := leftj.2.2 w' j' hj'
               omega
             case _ hj' =>
               have ⟨_, ⟨_, ⟨_, ⟨_, hj'⟩⟩⟩⟩ := hj'
               have _ := rightj.2.2 _ _ hj'
               omega

-- largestJoltage does in fact return the largest joltage of the given length
theorem Bank.LargestJoltage_largestJoltage (bank : Bank) (len : Nat)
  : ∃ w, Bank.LargestJoltage w bank len (bank.largestJoltage len) := by
  unfold largestJoltage
  have h := largestJoltageRev_isLargestJoltage bank.reverse len len (by omega)
  rw [List.reverse_reverse] at h
  exact ⟨h.1, h.2⟩

end Day03
