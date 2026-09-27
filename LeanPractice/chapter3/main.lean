theorem twoPlusThreeIsFive : 2 + 3 = 5 := by rfl
theorem fifteenMinusEightIsSeven : 15 - 8 = 7 := by rfl
theorem helloWorld : "Hello, ".append "world" = "Hello, world" := by rfl

theorem twoPlusThreeIsFive' : 2 + 3 = 5 := by decide
theorem fifteenMinusEightIsSeven' : 15 - 8 = 7 := by decide
theorem helloWorld' : "Hello, ".append "world" = "Hello, world" := by decide
theorem fiveLtEighteen : 5 < 18 := by decide

def fifth (xs : List α) (ok : xs.length > 4) : α := xs[4]

#eval fifth [5,4,3,2,1] (by decide)

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Add Pos where
  add := Pos.plus
def fourteen : Pos := seven + seven

--def posToString (atTop : Bool) (p : Pos) : String :=
--  let paren s := if atTop then s else "(" ++ s ++ ")"
--  match p with
--  | Pos.one => "Pos.one"
--  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

def posToString (p : Pos) : String :=
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ p'@Pos.one => s!"Pos.succ {posToString p'}"
  | Pos.succ p' => s!"Pos.succ ({posToString p'})"

instance : ToString Pos where
  toString := posToString 

#eval s!"There are {seven}"

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}"

instance : One Pos where
  one := Pos.one

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8
-- def zero : Pos := 0

inductive LT4 where
  | zero
  | one
  | two
  | three
instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three
#check (3 : LT4)

-- exercise 3.1.6.1
namespace anotherPos
structure Pos where
  succ ::
  pred : Nat

def seven : Pos := Pos.succ 6

def Pos.plus  (op1 : Pos)  (op2 : Pos) :  Pos :=
  Pos.succ (op1.pred + op2.pred + 1)

instance : Add Pos where
  add := Pos.plus
  
def posToString (p : Pos) : String :=
  toString (p.pred + 1)

def Pos.mul  (op1 : Pos)  (op2 : Pos) :  Pos :=
  Pos.succ ((op1.pred+1) * (op2.pred+1) - 1)

instance : Mul Pos where
  mul := Pos.mul

instance : OfNat Pos (n + 1) where
  ofNat := Pos.succ n

example : (1 : Pos) = Pos.succ 0 := rfl
example : (5 : Pos) = Pos.succ 4 := rfl
example : (2 + 3 : Pos) = Pos.succ 4 := rfl
example : (2 * 3 : Pos) = Pos.succ 5 := rfl
end anotherPos

-- exercise 3.1.6.2
namespace evenNumbers
inductive EvenNum : Type where
  | zero : EvenNum
  | succ : EvenNum → EvenNum

def two : EvenNum := EvenNum.succ EvenNum.zero
def four : EvenNum := EvenNum.succ two

def EvenNum.plus : EvenNum → EvenNum → EvenNum
  | .zero, k => k
  | .succ n, k => .succ (n.plus k)

instance : Add EvenNum where
  add := .plus

def EvenNum.mul : EvenNum → EvenNum → EvenNum
  | .zero, _ => .zero
  | .succ n, k => n.mul k + k + k

instance : Mul EvenNum where
  mul := .mul

def posToString (p : EvenNum) : String :=
  match p with
  | .zero => "EvenNum.zero"
  | .succ p'@.zero => s!"EvenNum.succ {posToString p'}"
  | .succ p' => s!"EvenNum.succ ({posToString p'})"

instance : ToString EvenNum where
  toString := posToString 

#eval two + four
def eight := two * four
#eval eight
#eval eight * four

instance : OfNat EvenNum 0 where
  ofNat := .zero

instance [OfNat EvenNum n] : OfNat EvenNum (n + 2) where
  ofNat := let two := .succ .zero
    (OfNat.ofNat n : EvenNum) + two
  
example : (2 : EvenNum) = EvenNum.succ 0 := rfl
example : (2 + 4 : EvenNum) = 6 := rfl
example : (2 * 6 : EvenNum) = 12 := rfl
end evenNumbers

-- exercise 3.1.6.3
namespace http

inductive Http : Type where
  | Get
  | Post
  | Patch


