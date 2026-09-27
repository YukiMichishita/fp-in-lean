import LeanPractice

def main : IO Unit :=
  IO.println "Hello, LeanPractice!"

inductive MyType (α : Type) : Type where
  | ctor : α → MyType α
