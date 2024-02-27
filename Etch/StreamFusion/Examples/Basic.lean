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

@[inline] def keys [Ord α] (t : TreeMap α β) : RBMap.Keys α β Ord.compare := t

variable
  (locations : TreeSet String)
     (counts : HashMap String Nat)
  (predicate : String → Bool)
          (f : String → String)

example : Nat := Id.run $ do
    let mut result := 0
    for key in locations.keys do
      if predicate key then
        result ← result + counts.findD (f key) 0
    return result

def filter [Ord ι] (p : ι → Bool) (t : TreeSet ι) := t.filter (fun k _ => p k)
def toArray [Ord ι] (t : TreeSet ι) := t.val.toArray.map Prod.fst

-- todo: cleanup if we get direct traversal of RBSet

-- using filter, map, fold, findD(efault)
example : Nat :=
  toArray (filter predicate locations)
  |>.map f |>.foldl (fun result fkey => result + counts.findD fkey 0) (init := 0)

example : ℕ := eval $
  --let locations := ((stream locations).imap' f)(i) --otherwise we need this :(
  Σ i => predicate(i) * locations(i).imap' f * counts(i)

end Etch.Verification
