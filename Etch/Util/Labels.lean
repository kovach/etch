import Std

/-!
Defines a type that provides endless labels between any two labels.
-/

namespace Etch

/-
-- Implementation with standard Nat ordering, for testing

structure LabelIdx where
  data : Nat
  deriving BEq, Inhabited

instance : Ord LabelIdx := ⟨fun x y => compare x.data y.data⟩
instance : LT LabelIdx := ⟨fun x y => x.data < y.data⟩
instance (x y : LabelIdx) : Decidable (x < y) := inferInstanceAs <| Decidable (x.data < y.data)

def LabelIdx.nth (n : Nat) : LabelIdx := {data := n}
-/

/--
A label is a natural number with the "binary-revlex ordering".

The ordering is given by writing the binary representation with the least-significant bit first
as an infinite sequence and then doing lex ordering.
The number `0` is least in this order.
-/
structure LabelIdx where
  data : Nat
  deriving BEq

def LabelIdx.bitsAux (x : Nat) : List Nat :=
  if h : x = 0 then
    []
  else
    have : x / 2 < x := by omega
    (x % 2) :: LabelIdx.bitsAux (x / 2)

instance : Repr LabelIdx where
  reprPrec x _ :=
    let bits := LabelIdx.bitsAux x.data
    "LabelIdx(" ++ Lean.Format.joinSep bits ", " ++ ")"

def LabelIdx.compareAux (x y : Nat) : Ordering :=
  if h : x = y then .eq
  else
    have : x / 2 + y / 2 < x + y := by
      cases x <;> cases y <;> omega
    match compare (x % 2) (y % 2) with
    | .eq => compareAux (x / 2) (y / 2)
    | .lt => .lt
    | .gt => .gt
termination_by x + y

instance : Ord LabelIdx := ⟨fun x y => LabelIdx.compareAux x.data y.data⟩
instance : LT LabelIdx := ⟨fun x y => compare x y == .lt⟩

/-- Finds the first `0` with no `1`s after and sets it to `1`.
This is injective. -/
def LabelIdx.freshAfterAux (x : Nat) : Nat :=
  if h : x = 0 then
    1
  else
    have : x / 2 < x := by omega
    (x % 2) + 2 * LabelIdx.freshAfterAux (x / 2)

def LabelIdx.freshAfter (x : LabelIdx) : LabelIdx := LabelIdx.mk (freshAfterAux x.data)

def LabelIdx.freshBeforeAux (x y : Nat) : Nat :=
  if h : y = 0 then
    panic! "x < y not true in freshBeforeAux"
  else
    let xb := x % 2
    let yb := y % 2
    if xb = yb then
      have : y / 2 < y := by omega
      xb + 2 * freshBeforeAux (x / 2) (y / 2)
    else if xb < yb then
      2 * freshAfterAux (xb / 2)
    else
      panic! "x < y not true in freshBeforeAux"
termination_by y

/-- Gives a label that is between `x` and `y`, assuming that `x < y`. -/
def LabelIdx.freshBefore (x y : LabelIdx) : LabelIdx :=
  LabelIdx.mk <| LabelIdx.freshBeforeAux x.data y.data

/-- An injection from `Nat` into LabelIdxs. -/
def LabelIdx.nth (n : Nat) : LabelIdx :=
  LabelIdx.mk <| 2 ^ (n + 1) - 1

instance : Inhabited LabelIdx := ⟨LabelIdx.nth 0⟩

/-
#eval List.range 10 |>.map LabelIdx.nth
#eval List.range 10 |>.map fun n => LabelIdx.nextBefore (LabelIdx.nth n) (LabelIdx.nth (n + 1))
-/
