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
