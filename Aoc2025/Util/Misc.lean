namespace List

universe u v
variable {α : Type u} {β : Type v}

@[specialize]
def mapRevMem (xs : List α) (f : (x : α) -> x ∈ xs -> β) (tail : List β := []) : List β :=
  match xs with
  | [] => tail
  | x :: xs' => mapRevMem xs'
    (fun y h => f y (h.tail x))
    (f x (.head _) :: tail)

def mapMem (xs : List α) (f : (x : α) -> x ∈ xs -> β) : List β :=
  xs.mapRevMem f |>.reverse

def parallelFoldOnceRev 
  (f : α -> α -> α)
  (xs : List (Task α))
  (tail : List (Task α) := [])
  : List (Task α) :=
  match xs with
  | [] => tail
  | [x] => x :: tail
  | x::y::xs' =>
    parallelFoldOnceRev f xs'
    ((x.bind fun x => y.map fun y => f x y) :: tail)

def parallelFold (f : α -> α -> α) (identity : α) (xs : List (Task α)) : Task α :=
  let rec loop fuel xs :=
    match fuel, xs with
    | _, [] | 0, _ => Task.pure identity
    | _, [x] => x
    | fuel + 1, _ => loop fuel (parallelFoldOnceRev f xs)
  loop (xs.length * xs.length) xs

end List
