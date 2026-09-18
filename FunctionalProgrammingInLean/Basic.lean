def hello := "world"

class HPlus (α : Type) (β : Type) (γ : Type) where
    hPlus : α → β → γ

@[default_instance]
instance [Add α] : HPlus α α α where
    hPlus := Add.add

#check HPlus.hPlus (3 : Nat) (5 : Nat)

structure NonEmptyList (α : Type) : Type where
    head : α
    tail : List α

def idahoSpiders : NonEmptyList String := {
    head := "Banded Garden Spider",
    tail := [
        "Lon-legged Sac Spider",
        "Wolf Spider",
        "Hobo Spider",
        "Cat-faced Spider"
    ]
}


--def NonEmptyList.get? : NonEmptyList α  → Nat → Option α
--  | xs, 0 => some xs.head
--  | {head := _, tail := []}, _ + 1 => none
--  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail[n]?

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by decide

def NonEmptyList.get (xs : NonEmptyList α)
  (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

--class GetElem
--  (coll : Type)
--  (idx : Type)
--  (item : outParam Type)
--  (inBounds : outParam (coll → idx → Prop)) where
--  getElem : (c : coll) → (i : idx) → inBounds c i → item

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

structure PPoint (α : Type) : Type where
  x : α
  y : α

instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y

structure Pos : Type where
  x : Nat
  y : Nat

instance : LT Pos where
  lt p1 p2 := LT.lt p1.x p2.x

instance : LE Pos where
  le p1 p2 := LE.le p1.x p2.x

instance {p1 : Pos} {p2 : Pos} : Decidable (p1 < p2) :=
  (inferInstance : Decidable (p1.x < p2.x))

instance {p1 : Pos} {p2 : Pos} : Decidable (p1 ≤ p2) :=
  (inferInstance : Decidable (p1.x ≤ p2.x))

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)
