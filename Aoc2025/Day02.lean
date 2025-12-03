import Batteries.Data.Nat.Digits

namespace Day02
open Day02

structure Interval where
  first : Nat
  last : Nat

instance : ToString Interval where
  toString ivl := s!"{ivl.first}-{ivl.last}"

def Nat.toNatDigitsRev (n b : Nat) : List Nat :=
  let b' := b; have hb' : b = b' := by rfl;
  match b with
  | 0 | 1 => []
  | _ + 2 =>
  n % b :: if _ : n < b then [] else
    have : n / b < n := by
      apply Nat.div_lt_self <;> omega
    toNatDigitsRev (n / b) b
def Nat.toNatDigits (n b : Nat) : List Nat :=
  List.reverse <| toNatDigitsRev n b

theorem Nat.toNatDigits_nonempty (n b : Nat)
  : 1 < b → n.toNatDigitsRev b ≠ [] := by
  intro h; unfold toNatDigitsRev; simp
  split <;> grind

@[simp]
theorem Nat.toNatDigitsRev_lt_base (n b : Nat)
  : 1 < b →
    n < b →
    toNatDigitsRev n b = [n] := by
  intro hb hn
  unfold toNatDigitsRev; simp; split <;> try(omega)
  rw [Nat.mod_eq_of_lt hn]
  split <;> rfl

@[simp]
theorem Nat.toNatDigitsRev_cons_toNatDigitsRev (n n' b : Nat)
  : 1 < b →
    0 < n →
    n' < b →
    toNatDigitsRev (b * n + n') b =
    n' :: toNatDigitsRev n b := by
  intro hb hn_one hn'
  have _ : b <= b * n := by
    conv => left; rw [← Nat.mul_one b]
    apply Nat.mul_le_mul_left
    omega
  have hbn : b <= b * n + n' := by omega
  have hn : (b * n + n') / b = n := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_right, Nat.div_eq_of_lt]
    all_goals omega
  conv => left; unfold toNatDigitsRev; simp
  split <;> try(omega)
  rw [Nat.mod_eq_of_lt hn', hn]
  split
  · omega
  · rfl

theorem Nat.baseInduction (b : Nat) {P : Nat → Prop} :
  1 < b →
  (digit : ∀ n, n < b → P n) →
  (cons : ∀ n n', 0 < n → n' < b → P n → P (b * n + n')) →
  ∀ n, P n :=
  fun hb h_lt_base h_gt_base =>
    -- this is irreducible :(
    let rec loop n := by
      if h : n < b
      then apply h_lt_base n h
      else
        have hn : n = b * (n / b) + (n % b) := by
          rw [Nat.div_add_mod]
        rw [hn]
        apply h_gt_base (n / b) (n % b)
        · apply Nat.div_pos <;> omega
        · apply Nat.mod_lt; omega
        · have : n / b < n := by
            apply Nat.div_lt_self <;> omega
          apply loop (n / b)
    loop

@[simp]
theorem Nat.toNatDigits_lt_base (n b : Nat)
  : 1 < b → n < b →
    toNatDigits n b = [n] := by
  intros; simp [toNatDigits]
  grind [toNatDigitsRev_lt_base]

@[simp]
theorem Nat.toNatDigits_append_toNatDigits (n n' b : Nat)
  : 1 < b → 0 < n → n' < b →
    toNatDigits (b * n + n') b =
    toNatDigits n b ++ [n'] := by
  intros; simp [toNatDigits]
  grind [toNatDigitsRev_cons_toNatDigitsRev]

def Nat.ofNatDigits (b : Nat) (digits : List Nat) :=
  List.foldl (b * · + ·) 0 digits

@[simp]
theorem Nat.ofNatDigits_base (n b : Nat)
  : ofNatDigits b [n] = n := by simp [ofNatDigits]
@[simp]
theorem Nat.ofNatDigits_append (n b : Nat) (digits : List Nat)
  : ofNatDigits b (digits ++ [n]) = b * ofNatDigits b digits + n := by
  unfold ofNatDigits
  rw [List.foldl_append]
  simp

-- This proves that (ofNatDigits b ·) ∘ (toNatDigits b ·) = id
theorem Nat.ofNatDigits_toNatDigits (n b : Nat) 
  : 1 < b →
    Nat.ofNatDigits b (n.toNatDigits b) = n := by
  intro hb
  induction n using baseInduction b hb
  case digit =>
    rw [Nat.toNatDigits_lt_base]
    simp; all_goals assumption
  case cons =>
    rw [Nat.toNatDigits_append_toNatDigits]
    simp; all_goals grind

-- This proves that my toNatDigits function is equivalent to the
-- toDigits function that Lean implements.
theorem Nat.toNatDigits_toDigits (n b : Nat)
  : 1 < b →
    Nat.toDigits b n =
    List.map (·.digitChar) (toNatDigits n b) := by
  intro hb
  induction n using baseInduction b hb
  case digit =>
    rw [Nat.toDigits_of_lt_base, Nat.toNatDigits_lt_base]
    simp; all_goals assumption
  case cons n n' _ _ ih =>
    rw [← Nat.toDigits_append_toDigits, Nat.toDigits_of_lt_base (n:=n'), Nat.toNatDigits_append_toNatDigits]
    simp; all_goals assumption

def Nat.numDigits (n : Nat) : Nat := (Nat.toNatDigitsRev n 10).length
-- Shift n right by k decimal digits.
def Nat.shiftRight10 (n k : Nat) : Nat := n / (10 ^ k)
-- Shift n left by k decimal digits.
def Nat.shiftLeft10 (n k : Nat) : Nat := n * (10 ^ k)
-- Take the last k decimal digits of n.
def Nat.truncRight10 (n k : Nat) : Nat := n % (10 ^ k)
-- Take the first k decimal digits of n.
def Nat.truncLeft10 (n k : Nat) : Nat := n.shiftRight10 (n.numDigits - k)

theorem Nat.numDigits_lt_ten (n : Nat)
  : n < 10 → n.numDigits = 1 := by
  intros
  unfold numDigits
  grind [toNatDigitsRev_lt_base]
theorem Nat.numDigits_succ (n n' : Nat)
  : 0 < n → n' < 10 →
    (10 * n + n').numDigits = n.numDigits + 1 := by
  intros
  unfold numDigits
  rw [toNatDigitsRev_cons_toNatDigitsRev]
  all_goals grind

@[simp] theorem Nat.shiftRight10_zero (n : Nat)
  : n.shiftRight10 0 = n := by grind [Nat.shiftRight10]
@[simp] theorem Nat.shiftRight10_succ (n k : Nat)
  : n.shiftRight10 (k + 1) = n.shiftRight10 k / 10 := by
  simp [Nat.shiftRight10, Nat.pow_add_one, Nat.div_div_eq_div_mul]
@[simp] theorem Nat.zero_shiftRight10 (k : Nat)
  : shiftRight10 0 k = 0 := by
  induction k <;> simp; grind

@[simp] theorem Nat.shiftLeft10_zero (n : Nat)
  : n.shiftLeft10 0 = n := by grind [Nat.shiftLeft10]
@[simp] theorem Nat.shiftLeft10_succ (n k : Nat)
  : n.shiftLeft10 (k + 1) = 10 * n.shiftLeft10 k := by grind [Nat.shiftLeft10]
@[simp] theorem Nat.zero_shiftLeft10 (k : Nat)
  : shiftLeft10 0 k = 0 := by
  induction k <;> simp; grind

theorem List.replicate_comm {α} (n : Nat) (a : α)
  : List.replicate n a ++ [a] = a :: List.replicate n a := by
  induction n
  case zero => simp
  case succ n' ih => simp [List.replicate, ih]

theorem Nat.zero_lt_pow (n a : Nat)
  : 0 < n → 0 < n ^ a := by
  intro h
  cases a
  · simp
  · apply @Nat.lt_of_lt_of_le 0 1 _
    · omega
    · apply Nat.one_le_pow _ _ h

theorem Nat.shiftLeft10_toDigits (n k : Nat)
  : 0 < n →
    toNatDigits (n.shiftLeft10 k) 10 =
    toNatDigits n 10 ++ List.replicate k 0 := by
  intro h_zero
  induction k
  case zero => simp
  case succ k' ih =>
    conv => enter [1, 1]; simp; rw [← Nat.add_zero (10 * _)]
    rw [Nat.toNatDigits_append_toNatDigits, ih]
    simp [List.replicate]
    all_goals try (omega)
    · apply List.replicate_comm
    · unfold shiftLeft10
      suffices 0 * 10 ^ k' < n * 10 ^ k' by omega
      apply Nat.mul_lt_mul_of_pos_right
      · omega
      · grind [Nat.zero_lt_pow]

-- First half, shorter half if odd.
def Nat.firstHalfRD (n : Nat) : Nat := n.shiftRight10 <| (n.numDigits + 1) / 2
-- Second half, longer half if odd.
def Nat.secondHalfRU (n : Nat) : Nat := n.truncRight10 <| (n.numDigits + 1) / 2
-- First half, longer half if odd.
def Nat.firstHalfRU (n : Nat) : Nat := n.shiftRight10 <| n.numDigits / 2
-- Second half, shorter half if odd.
def Nat.secondHalfRD (n : Nat) : Nat := n.truncRight10 <| n.numDigits / 2

def Nat.concatDecimal (n n' : Nat) : Nat :=
  n.shiftLeft10 n'.numDigits + n'

@[simp]
def Nat.concatDecimal_zero_left (n : Nat)
  : concatDecimal 0 n = n := by simp [concatDecimal]

theorem Nat.concatDecimal_positive_right (n n' : Nat)
  : 0 < n' → 0 < concatDecimal n n' := by
  intro hn; unfold concatDecimal; omega

-- This proves that (toNatDigits · 10) is a semigroup homomorphism
-- (ℕ⁺, concatDecimal) → (List ℕ, ++)
theorem Nat.toNatDigits_concatDecimal (n n' : Nat)
  : 0 < n →
    toNatDigits (concatDecimal n n') 10 =
    toNatDigits n 10 ++ toNatDigits n' 10 := by
  intro h_zero
  unfold concatDecimal
  induction n' using baseInduction 10 (by omega)
  case digit n' hn' =>
    rw [toNatDigits_lt_base n', ← toNatDigits_append_toNatDigits, numDigits_lt_ten]
    simp; all_goals grind
  case cons n n' _ _ ih =>
    conv =>
      enter [1, 1]
      rw [numDigits_succ, shiftLeft10_succ, ← Nat.add_assoc, ← Nat.mul_add 10]
      · skip
      · tactic => assumption
      · tactic => assumption
    repeat rw [toNatDigits_append_toNatDigits]
    rw [ih]
    all_goals grind

-- Convert any natural to an invalid ID by pasting it after itself.
@[simp]
def Nat.duplicateToInvalidID (n : Nat) : Nat :=
  n.concatDecimal n
-- Convert any natural to an invalid ID by repeatedly pasting it after itself.
def Nat.repeatToInvalidID (n : Nat) : Nat -> Nat
  | 0 => 0
  | k + 1 => (Nat.repeatToInvalidID n k).concatDecimal n

theorem Nat.duplicateToInvalidID_eq_repeatToInvalidID_2 (n : Nat)
  : n.duplicateToInvalidID = n.repeatToInvalidID 2 := by
  simp [repeatToInvalidID]

@[simp]
theorem Nat.repeatToInvalidID_zero_left (k : Nat)
  : repeatToInvalidID 0 k = 0 := by
  induction k <;> simp [repeatToInvalidID]
  case succ n ih => rw [ih]; simp
@[simp]
theorem Nat.repeatToInvalidID_zero_right (n : Nat)
  : repeatToInvalidID n 0 = 0 := by
  simp [repeatToInvalidID]

theorem Nat.repeatToInvalidID_positive (n k : Nat)
  : 0 < n → 0 < k →
    0 < n.repeatToInvalidID k := by
  intro hn hk
  induction k
  case zero => contradiction
  case succ =>
    unfold repeatToInvalidID
    apply Nat.concatDecimal_positive_right
    grind

theorem Nat.repeatToInvalidID_zero_iff (n k : Nat)
  : n.repeatToInvalidID k = 0 ↔ n = 0 ∨ k = 0 := by
  constructor <;> intro h
  case mp =>
    false_or_by_contra
    suffices _ : 0 < n.repeatToInvalidID k by omega
    apply repeatToInvalidID_positive <;> grind
  case mpr =>
    cases h
    case inl h => rw [h]; simp
    case inr h => rw [h]; simp

theorem Nat.repeatToInvalidID_toNatDigits (n k : Nat)
  : 0 < n → 0 < k →
    (n.repeatToInvalidID k).toNatDigits 10 =
    (List.replicate k n).flatMap (toNatDigits · 10) := by
  intro hn hk
  cases k
  case zero => contradiction
  case succ k' =>
    clear hk
    induction k'
    case zero => simp [repeatToInvalidID]
    case succ k' ih =>
      rw [← List.replicate_append_replicate, List.flatMap_append, ← ih]
      simp
      conv => left; unfold repeatToInvalidID
      rw [toNatDigits_concatDecimal]
      apply Nat.repeatToInvalidID_positive <;> grind

-- Prop for whether a number is an invalid ID.
abbrev Nat.isInvalidID (n : Nat) : Prop :=
  n.firstHalfRU = n.secondHalfRD

-- Prop for whether a number is an invalid ID with repetition length k.
abbrev Nat.isInvalidID' (n k : Nat) : Prop :=
  ∃ n' : Nat, n'.repeatToInvalidID k = n

theorem Nat.isInvalidID_of_repeatToInvalidID (n k : Nat)
  : isInvalidID' (n.repeatToInvalidID k) k := by
  exists n

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

def parseInput : IO (List Interval) := do
  let stdin <- IO.getStdin
  let lines <- stdin.lines
  let line := "".intercalate lines.toList
  parseIntervals line

end Day02
open Day02

def main : IO Unit := do
  let intervals <- parseInput
  IO.println s!"Part 1: {part1 intervals}"
  IO.println s!"Part 2: {part2 intervals}"
  return ()
