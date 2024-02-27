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
open SStream OfStream ToStream

def_index_enum_group i,j,k,l

--@[inline] def keys [Ord α] (t : TreeMap α β) : RBMap.Keys α β Ord.compare := t


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

/- Triangle iterator `locationOf(i,j) * contains(j,k) * canUse(i,k)` -/
section Eg2

def_index_enum_group entity, location, item

variable
  (Entity Location Item : Type)
  [LinearOrder Entity]
  [LinearOrder Location]
  [LinearOrder Item]
  (locatedAt : SparseArray Entity (ArraySet Location))
  (contains  : SparseArray Location (ArraySet Item))
  (canUse    : SparseArray Entity (ArraySet Item))


def tr3 : SparseArray Entity (SparseArray Location (ArraySet Item)) := eval $
  locatedAt(entity, location) * contains(location, item) * canUse(entity, item)

end Eg2

section Eg3


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
