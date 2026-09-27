def last  : (xs : List α) -> Option α 
  | [] => none
  | [x] => x
  | _ :: xs => last xs
#eval last [1,2,3]
#eval last [1,2]
#eval last ([]:List Nat)

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | x :: xs => if predicate x then x else findFirst? xs predicate
#eval [1,2,3].findFirst? (· % 2 == 0)

def Prod.switch {α β : Type} (pair : α × β) : β × α := 
  ⟨pair.snd, pair.fst⟩
#eval Prod.switch ⟨1, 2⟩

def PetName : Type := String ⊕ String

inductive PetName' : Type where
  | dog (name : String)
  | cat (name : String)

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys
#eval zip [1,2,3] ["a", "b"]

def take  (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | 0, _ => [] 
  | _, [] => []
  | n + 1, x :: xs => x :: take n xs
#eval take 2 [1,2,3,4]

def distribute : (α × (β ⊕ γ)) → (α × β) ⊕ (α × γ) 
  | ⟨a, s⟩ =>
    match s with
      | Sum.inl b => Sum.inl ⟨a, b⟩
      | Sum.inr g => Sum.inr ⟨a, g⟩

def twoMul : Bool × α → α ⊕ α 
  | ⟨b, a⟩ => if b then Sum.inr a else Sum.inl a


