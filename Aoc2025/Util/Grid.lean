import Aoc2025.Util.Coord
import Batteries.Data.List.Lemmas

structure Grid (α : Type) where
  width : Nat
  height : Nat
  rows : Vector (Vector α width) height
deriving DecidableEq, Inhabited, Repr

namespace Grid

variable {α : Type} (grid : Grid α)

instance : Inhabited (Grid α) := ⟨⟨0, 0, #v[]⟩⟩
instance : ∀ [ToString α], ToString (Grid α) where
  toString grid :=
    ("\n".intercalate ·.toList) <|
      grid.rows.map (fun row => "".intercalate (row.map toString).toList)

def fromLines {m : Type -> Type}
  [Monad m] [Inhabited (m α)]
  (lines : Array String) (cell : Char -> m α)
  : m (Grid α) := do
  let height := lines.size
  let width := Array.foldl max 0 (lines.map (·.length))
  let rows <- lines.toVector.mapM fun row =>
    let row := row.toList.toArray
    Vector.ofFnM fun i => do
      if h : i.toNat < row.size
      then cell row[i.toNat]
      else default
  return mk width height rows

theorem Array.max_length_le (rows : Array (Array α))
  : ∀ row ∈ rows, row.size <= Array.foldl max 0 (rows.map (·.size)) := by
  have ⟨rows⟩ := rows
  simp
  intro row hrow
  rw [← List.foldr_eq_foldl]
  induction rows <;> simp
  case nil => contradiction
  case cons hd tl ih =>
    cases hrow
    case head => omega
    case tail h =>
      have := ih h
      omega

def ofRows (rows : Array (Array α)) [Inhabited α] : Grid α :=
  let height := rows.size
  let width := Array.foldl max 0 (rows.map (·.size))
  let rows := rows.toVector.map fun row =>
    if h : row.size = width
    then Vector.mk row h
    else if h' : row.size <= width then
      let row' := row ++ Array.replicate (width - row.size) default
      Vector.mk row' (by grind)
    -- This never happens
    else Vector.mk (row.take width) (by grind)
  mk width height rows

def toRows : Array (Array α) := grid.rows.map (·.toArray) |>.toArray

def transpose : Grid α :=
  Grid.mk grid.height grid.width <|
    Vector.ofFn fun x =>
      Vector.ofFn fun y =>
        grid.rows[y][x]

abbrev inBoundsXY (x y : Int) :=
  0 <= x ∧ x < grid.width ∧ 0 <= y ∧ y < grid.height
abbrev inBounds (pos : Coord) :=
  grid.inBoundsXY pos.x pos.y

@[simp, grind =]
instance : GetElem (Grid α) Coord α inBounds where
  getElem grid pos h := grid.rows[pos.y.toNat][pos.x.toNat]

-- Replace grid[pos] with (f grid[pos]), linearly.
def modify? (pos : Coord) (f : α -> α) : Grid α :=
  let ⟨width, height, ⟨rows, hrows⟩⟩ := grid
  let rows' := ⟨rows.modify pos.y.toNat (fun ⟨row, hrow⟩ =>
      ⟨row.modify pos.x.toNat f, (by grind)⟩),
      (by grind)⟩
  Grid.mk width height rows'

-- Replace grid[pos] with value, linearly.
def set? (pos : Coord) (value : α) : Grid α :=
  grid.modify? pos (fun _ => value)

@[simp, grind =]
theorem modify?_inBounds {grid : Grid α} {pos : Coord} {f : α -> α}
  : (grid.modify? pos f).inBounds pos ↔ grid.inBounds pos := by
  unfold modify? ; simp

end Grid
