import Etch.Op

-- This file defines operations only used in CodeGen/

def Op.boolLit (b : Bool) : Op Bool where
  arity := 0
  argTypes := fun i => nomatch i
  spec := fun _ => b
  opName := "bool_lit(" ++ (bif b then "1" else "0") ++ ")"

def Op.intLit (i : ℤ) : Op Int where
  arity := 0
  argTypes := fun i => nomatch i
  spec := fun _ => i
  opName := "int_lit(" ++ (toString i) ++ ")"

def Op.natLit (i : ℕ) : Op ℕ where
  arity := 0
  argTypes := fun i => nomatch i
  spec := fun _ => i
  opName := "int_lit(" ++ (toString i) ++ ")"


def Op.arrAccess {α : Type _} [Inhabited α] : Op α where
  arity := 2
  argTypes := ![List α, ℕ]
  spec := fun a => List.getD (a 0) (a 1) default
  opName := "arr_access"
