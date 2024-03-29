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

def filter [Ord ι] (p : ι → Bool) (t : TreeSet ι) := t.filter (fun k _ => p k)
def toArray [Ord ι] (t : TreeSet ι) := t.val.toArray.map Prod.fst

namespace Eg1'

variable
  (locations : ArraySet String)
  (counts    : HashMap String Nat)
  (predicate : String → Bool)
  (f         : String → String)

-- Manually fused
def d1 : ℕ := Id.run $ do
    let mut result := 0
    for key in locations do
      if predicate key then
        result ← result + counts.findD (f key) 0
    return result

-- Using filter, map, fold, findD(efault) combinators
def d2 : ℕ :=
  (locations.filter predicate).map f
  |>.foldl (init := 0) (fun result fkey => result + counts.findD fkey 0)

-- With stream combinators
example : ℕ := eval $ Σ i => (f $[i] predicate(i) * locations(i)) * counts(i)

--example : ℕ := eval $ Σ i => predicate(i) * (f $[i] locations(i)) * counts(i)
def d3 : ℕ := eval $ Σ i => (f $[i] predicate(i) * (ArraySet.toSeqStream locations)(i)) * counts(i)

#eval d1
  (locations := #["Hi", "There"])
  (HashMap.ofList [("HI", 10), ("THERE", 3)])
  (predicate := fun str => str.length > 3)
  (f := String.toUpper)

end Eg1'

namespace Eg1

variable
  (locations : TreeSet String)
  (counts    : HashMap String Nat)
  (predicate : String → Bool)
  (f         : String → String)

-- Manually fused
def d1 : ℕ := Id.run $ do
    let mut result := 0
    for key in locations.keys do
      if predicate key then
        result ← result + counts.findD (f key) 0
    return result

-- Using filter, map, fold, findD(efault) combinators
def d2 : ℕ :=
  (filter predicate locations).foldl
    (init := 0) (fun result key =>
    result + counts.findD (f key) 0)

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

def filterFile := "plot1.csv"
open Eg1'

def t1 := fun d file => recordTestCase file "loop"
    (fun (l,c) => (l,c,p1,f1))
    (op := fun (l,c,p1,f1) => d1 l c p1 f1)
    (fun x : ℕ => x)
    d

def t2 := fun d file => recordTestCase file "fold"
    (fun (l,c) => (l,c,p1,f1))
    (op := fun (l,c,p1,f1) => d2 l c p1 f1)
    (fun x : ℕ => x)
    d

def t3 := fun d file => recordTestCase file "us"
    (fun (l,c) => (l,c,p1,f1))
    (op := fun (l,c,p1,f1) => d3 l c p1 f1)
    (fun x : ℕ => x)
    d

end testEg1

/- Game-flavored triangle query `locationOf(i,j) * contains(j,k) * canUse(i,k)` -/
section Eg2

def_index_enum_group entity, location, item

variable
  {Entity Location Item : Type}
  (locatedAt : SparseArray Entity   (ArraySet Location))
  (contains  : SparseArray Location (ArraySet Item))
  (canUse    : SparseArray Entity   (ArraySet Item))

variable
  [LinearOrder Entity]
  [LinearOrder Location]
  [LinearOrder Item]

example : SparseArray Entity (SparseArray Location (ArraySet Item)) := eval $
  locatedAt(entity, location) * contains(location, item) * canUse(entity, item)

-- not working/not idiomatic
def tr1
    (locatedAt : SparseArray       Entity   (ArraySet Location))
    (contains  : SparseArrayLookup Location (ArraySet Item))
    (canUse    : SparseArrayLookup Entity   (ArraySet Item))
    : F Entity (F Location (ArraySet Item))
    := eval $
  locatedAt(entity, location) * contains(location, item) * canUse(entity, item)

def tr2
    [Hashable Location]
    [Hashable Entity]
    [BEq Location]
    [BEq Entity]
    (locatedAt : SparseArray       Entity   (ArraySet Location))
    (contains  : HashMap Location (ArraySet Item))
    (canUse    : HashMap Entity   (ArraySet Item))
    : F Entity (F Location (ArraySet Item))
    := eval $
  locatedAt(entity, location) * contains(location, item) * canUse(entity, item)

def tr3' : F Entity (F Location (ArraySet Item)) := eval $
  (memo SparseArray Entity (SparseArray Location (ArraySet Item)) from
   locatedAt(entity, location) * contains(location, item)) * canUse(entity, item)

def tr3 : F Entity (F Location (ArraySet Item)) := eval $
  locatedAt(entity, location) * contains(location, item) * canUse(entity, item)

end Eg2

-- matrix slices: lower triangle * upper
section Eg3

variable
{α J} [LinearOrder J]

variable
  [Semiring α] [Scalar α]
  (dim : ℕ) (mat : ℕ → ℕ → α)

@[inline] def matMul (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) :=
  Σ j => a(i,j) * b(j,k)
infixl:35 " @. " => matMul

abbrev DenseMat r c α := DenseArray r (DenseArray c α)

example : DenseArray dim (DenseArray dim α) := eval $
  -- lower triangle of 1's
  let lowerMask : ℕ →ₛ ℕ →ₛ Bool :=
    (range 0 dim).mapWithIndex (fun row _ => range 0 (row + 1))
  -- upper triangle of 1's
  let upperMask : ℕ →ₛ ℕ →ₛ Bool :=
    (range 0 dim).mapWithIndex (fun row _ => range 0 (dim - row))
  let m1 := upperMask(i,j) * mat(i,j)
  let m2 := lowerMask(j,k) * mat(j,k)
  m1 @. m2

def mul3 : DenseArray dim (DenseArray dim α) := eval $
  -- lower triangle of 1's
  let lowerMask := (range 0 dim).mapWithIndex (fun row _ => range 0 (row + 1))
  -- upper triangle of 1's
  let upperMask := (range 0 dim).mapWithIndex (fun row _ => range 0 (dim - row))
  let m1 := upperMask(i,j) * mat(i,j)
  let m2 := lowerMask(j,k) * mat(j,k)
  m1 @. m2

@[macro_inline] def mat1 : ℕ → ℕ → Nat := fun i j => i + j

structure foo where
  a : SparseArray String (ArraySet String)
  b : SparseArray String (ArraySet String)
  c : SparseArray String (ArraySet String)

structure foo' where
  a : SparseArray String (ArraySet String)
  b : HashMap String (ArraySet String)
  c : HashMap String (ArraySet String)

def eg2.t2 := fun d file => recordTestCase file "tri.hash"
    (fun s : foo' => s)
    (op := fun ⟨a,b,c⟩ => tr2 a b c)
    (fun x :  F String (F String (ArraySet String))=> (x.1.size))
    d

def eg2.t3_unfused := fun d file => recordTestCase file "tri.unfused"
    (fun s : foo => s)
    (op := fun ⟨a,b,c⟩ => tr3' a b c)
    (fun x :  F String (F String (ArraySet String))=> (x.1.size))
    d

def eg2.t3_fused := fun d file => recordTestCase file "tri.fused"
    (fun s : foo => s)
    (op := fun ⟨a,b,c⟩ => tr3 a b c)
    (fun x :  F String (F String (ArraySet String))=> (x.1.size))
    d

end Eg3

end Etch.Verification
