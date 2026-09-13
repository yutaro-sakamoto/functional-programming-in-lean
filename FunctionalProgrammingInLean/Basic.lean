def hello := "world"

class HPlus (α : Type) (β : Type) (γ : Type) where
    hPlus : α → β → γ

instance [Add α] : HPlus α α α where
    hPlus := Add.add

#check HPlus.hPlus (3 : Nat) (5 : Nat)
