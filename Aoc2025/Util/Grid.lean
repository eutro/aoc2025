import Aoc2025.Util.Coord

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
  let rows <- (Vector.mapM · lines.toVector) fun row =>
    let row := row.toList.toArray
    Vector.ofFnM fun i => do
      if h : i < row.size
      then cell row[i]
      else default
  return mk width height rows

abbrev inBoundsXY (x y : Int) :=
  0 <= x ∧ x < grid.width ∧ 0 <= y ∧ y < grid.height
abbrev inBounds (pos : Coord) :=
  grid.inBoundsXY pos.x pos.y

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

end Grid
