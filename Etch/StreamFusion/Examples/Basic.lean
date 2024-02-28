import Std.Data.RBMap
import Std.Data.HashMap
import Lean.Data.HashSet

import Etch.StreamFusion.Stream
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.Expand
import Etch.StreamFusion.Traversals
import Etch.StreamFusion.TestUtil

namespace Etch.Verification

open Std (RBMap RBSet HashMap)
open Lean (HashSet)
open Etch.Verification RB
open SStream ToStream

def_index_enum_group i,j,k,l

section Eg1
def filter [Ord ι] (p : ι → Bool) (t : TreeSet ι) := t.filter (fun k _ => p k)
def toArray [Ord ι] (t : TreeSet ι) := t.val.toArray.map Prod.fst

variable
  (locations : TreeSet String)
     (counts : HashMap String Nat)
  (predicate : String → Bool)
          (f : String → String)

-- Manually fused
def d1 : ℕ := Id.run $ do
    let mut result := 0
    for key in locations.keys do
      if predicate key then
        result ← result + counts.findD (f key) 0
    return result

-- Using filter, map, fold, findD(efault) combinators
def d2 : ℕ :=
  toArray (filter predicate locations)
  |>.map f |>.foldl (fun result fkey => result + counts.findD fkey 0) (init := 0)

-- Ours
example : ℕ := eval $ Σ i => predicate(i) * (f $[i] locations(i)) * counts(i)

def d3 : ℕ := eval $
  Σ i => predicate(i) * (f $[i] locations(i)) * counts(i)

#eval d1
  (locations := TreeSet.ofArray #["Hi", "There"])
  (HashMap.ofList [("HI", 10), ("THERE", 3)])
  (predicate := fun str => str.length > 3)
  (f := String.toUpper)

end Eg1

section testEg1
def p1 : String → Bool := fun str : String => str.length > 3
def f1 := String.toUpper

def t1 := genCase' "test d1"
    (fun (l,c) => (l,c,p1,f1))
    (op := fun (l,c,p1,f1) => d1 l c p1 f1)
    (fun x : ℕ => x)

def t2 := genCase' "test d2"
    (fun (l,c) => (l,c,p1,f1))
    (op := fun (l,c,p1,f1) => d2 l c p1 f1)
    (fun x : ℕ => x)

def t3 := genCase' "test d3"
    (fun (l,c) => (l,c,p1,f1))
    (op := fun (l,c,p1,f1) => d3 l c p1 f1)
    (fun x : ℕ => x)

end testEg1

/- Game-flavored triangle query `locationOf(i,j) * contains(j,k) * canUse(i,k)` -/
section Eg2

def_index_enum_group entity, location, item

variable
  [LinearOrder Entity]
  [LinearOrder Location]
  [LinearOrder Item]
  (locatedAt : SparseArray Entity (ArraySet Location))
  (contains  : SparseArray Location (ArraySet Item))
  (canUse    : SparseArray Entity (ArraySet Item))


def tr3 : SparseArray Entity (SparseArray Location (ArraySet Item)) := eval $
  locatedAt(entity, location) * contains(location, item) * canUse(entity, item)

end Eg2

-- matrix slices: lower triangle * upper
section Eg3

@[inline] def matMul {α J} [LinearOrder J] [Mul α] [Scalar α] (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) :=
  Σ j => a(i,j) * b(j,k)

infixl:35 " @. " => matMul

variable
  [Semiring α]
  [Scalar α]
  (dim : ℕ)
  (mat : ℕ → ℕ → α)

def upper := (range 0 dim).mapWithIndex (fun row _ => range 0 (dim - row))
def lower := (range 0 dim).mapWithIndex (fun row _ => range 0 (row+1))

#eval ((eval $ SStream.range 0 10) : ArraySet Nat)
#eval ((eval $ upper 3) : SparseArray Nat (ArraySet Nat))
#eval ((eval $ lower 3) : SparseArray Nat (ArraySet Nat))

def mul3 : DenseArray dim (HashMap Nat α) := eval $
  -- lower triangle of 1's
  let lowerMask := (range 0 dim).mapWithIndex (fun row _ => range 0 (row + 1))
  -- upper triangle of 1's
  let upperMask := (range 0 dim).mapWithIndex (fun row _ => range 0 (dim - row))
  let m1 := upperMask(i,j) * mat(i,j)
  let m2 := lowerMask(j,k) * mat(j,k)
  m1 @. m2

end Eg3

def randStrings (num : Nat) : IO (Array String) := do
  let mut result := #[]
  for _ in [0:num] do
    let n ← IO.rand 1 (num*2)
    result := result.push n
  pure $ result.qsort (·<·) |>.deduplicateSorted |>.map toString

def tests (num : Nat) : IO Unit := do
  let s1 ← randStrings num
  let s2 ← randStrings num
  let strs := TreeSet.ofArray s1
  let counts := HashMap.ofList (s2.map fun str => (str, 1)).toList

  t1 (strs, counts)
  t2 (strs, counts)
  t3 (strs, counts)

def _root_.main (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  tests num

end Etch.Verification
