inductive L1 | nil | cons : Nat → L1 → L1
inductive L2 | nil | cons : Nat → L2 → L2

def List.toL1 : List Nat → L1
| .nil => .nil
| .cons x xs => .cons x xs.toL1

set_option trace.compiler.ir true
def map1 : L1 → L1 :=
  let rec go1
  | x, .nil => x
  | x, .cons y xs => go1 (.cons y x) xs
  go1 .nil

def map2 : L1 → L2 :=
  let rec go2
  | x, .nil => x
  | x, .cons y xs => go2 (.cons y x) xs
  go2 .nil

def main : IO Unit := pure ()
