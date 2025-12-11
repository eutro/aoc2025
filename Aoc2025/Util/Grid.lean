import Aoc2025.Util.Coord
import Batteries.Data.List.Lemmas

abbrev FixedGrid (α : Type) (width height : Nat) :=
  Vector (Vector α width) height

namespace FixedGrid
variable {α : Type} {width height : Nat} (grid : FixedGrid α width height)

abbrev inBoundsXY (_grid : FixedGrid α width height) (x y : Int) :=
  0 <= x ∧ x < width ∧ 0 <= y ∧ y < height
abbrev inBounds (pos : Coord) :=
  grid.inBoundsXY pos.x pos.y

@[simp, grind =]
instance : GetElem (FixedGrid α width height) Coord α inBounds where
  getElem grid pos h := grid[pos.y.toNat][pos.x.toNat]

-- Replace grid[pos] with (f grid[pos]), linearly.
def modify? (pos : Coord) (f : α -> α) : FixedGrid α width height :=
  let ⟨rows, hrows⟩ := grid
  let rows' := ⟨rows.modify pos.y.toNat (fun ⟨row, hrow⟩ =>
      ⟨row.modify pos.x.toNat f, (by grind)⟩),
      (by grind)⟩
  rows'

-- Replace grid[pos] with value, linearly.
def set? (pos : Coord) (value : α) : FixedGrid α width height :=
  grid.modify? pos (fun _ => value)

end FixedGrid

structure Grid (α : Type) where
  width : Nat
  height : Nat
  rows : FixedGrid α width height
deriving DecidableEq, Inhabited, Repr

namespace Grid
variable {α : Type} (grid : Grid α)

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
  Grid.mk grid.width grid.height (grid.rows.modify? pos f)

@[simp, grind =]
theorem modify?_width {grid : Grid α} {pos : Coord} {f : α -> α}
  : (modify? grid pos f).width = grid.width := by
  simp [modify?]

@[simp, grind =]
theorem modify?_height {grid : Grid α} {pos : Coord} {f : α -> α}
  : (modify? grid pos f).height = grid.height := by
  simp [modify?]

@[simp, grind =]
theorem modify?_inBounds {grid : Grid α} {pos : Coord} {f : α -> α}
  : (grid.modify? pos f).inBounds pos ↔ grid.inBounds pos := by
  simp

-- Replace grid[pos] with value, linearly.
def set? (pos : Coord) (value : α) : Grid α :=
  grid.modify? pos (fun _ => value)

@[simp, grind =]
theorem set?_width {grid : Grid α} {pos : Coord} {x : α}
  : (set? grid pos x).width = grid.width := by
  simp [set?]

@[simp, grind =]
theorem set?_height {grid : Grid α} {pos : Coord} {x : α}
  : (set? grid pos x).height = grid.height := by
  simp [set?]

@[simp, grind =]
theorem set?_inBounds {grid : Grid α} {pos : Coord} {x : α}
  : (grid.set? pos x).inBounds pos ↔ grid.inBounds pos := by
  simp

end Grid
