/- very WIP tutorial for the library -/

import Etch.StreamFusion.Stream
import Etch.StreamFusion.Expand
import Etch.StreamFusion.TestUtil

import Std.Data.RBMap
import Std.Data.HashMap

open Std (RBMap RBSet HashMap)

namespace Etch.Verification.SStream

open ToStream

variable {I J K L α β : Type}
[LinearOrder I] [LinearOrder J] [LinearOrder K] [LinearOrder L]
[Scalar α] [Mul α] [Zero α] [Add α]

abbrev i : ℕ := 0
abbrev j : ℕ := 1
abbrev k : ℕ := 2
abbrev l : ℕ := 3

/-
Some coercion examples
-/

def mul_fns [ToStream t (I → J → α)] [ToStream t' (J → K → α)] (a : t) (b : t')
    : i~I → j~J → k~K → α :=
  a(i,j) * b(j,k)

def mul_fns' [ToStream t (I → J → α)] [ToStream t' (J → K → α)] (a : t) (b : t') :=
  a(i,j) * b(j,k)

section
--set_option trace.Meta.synthInstance true
#synth ExpressionTree.EnsureBroadcast [(0, I), (1, J), (2, K)] α (j~J → k~K →ₛ α) _
end

-- Notice, no Broadcast helper class, it was unfolded
#print mul_fns'

def testContractElab (A : I →ₛ J →ₛ α) (v : J →ₛ α) := Σ j : (Σ i: A(i,j)) * v(j)
-- i~Unit →ₛ j~Unit →ₛ α

/- Some examples of notation

  notes:
    - a shape is a list of (Nat, Type) pairs
    - a collection needs to have a ToStream instance
    - indices are index names encoded as natural numbers for now
-/

@[inline] def vecSum (v : I →ₛ α) := Σ i: v(i)
@[inline] def matSum (m : I →ₛ J →ₛ α) (v : J →ₛ α) := Σ i, j: m(i, j) * v(j)

@[inline] def matMul_ijjk (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) :=
  Σ j: a(i,j) * b(j,k)

-- todo: investigate these definitions and other approaches
@[inline] def ABC
  (a : I →ₛ J →ₛ α)
  (b : J →ₛ K →ₛ α)
  (c : K →ₛ L →ₛ α)
   : i~I →ₛ Unit →ₛ l~L →ₛ α :=
  let m1 :=  a(i,j)
  let m2 :=  b(j,k)
  let m3 :=  c(k,l)
  let x : ArrayMap I (ArrayMap K α) := eval $ Σ j: m1 * m2
  let m  := (stream x)(i,k) * m3
  Σ k: m

@[inline] def ABC' (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) (c : K →ₛ L →ₛ α) :=
  let ijk := [(i,I),(j,J),(k,K)]
  let ikl := [(i,I),(k,K),(l,L)]
  let m1 := ijk ⇑ a(i,j)
  let m3 := ikl ⇑ c(k,l)
  let m : i~I →ₛ k~K →ₛ α := m1.map fun (row : j~J →ₛ k~K → α) =>
             memo (ArrayMap K α) (Σ j: row * b(j,k))
  let m  := ikl ⇑ m * m3
  Σ k: m

def matMul1 (num : ℕ) : IO Unit := do
  let m := stream $ mat' num
  let x := matMul_ijjk m m
  time "matrix 1'" fun _ =>
    for _ in [0:10] do
      let x : HMap ℕ (HMap ℕ ℕ) := eval x
      IO.println s!"{x.1.size}"

def matMul1' (num : ℕ) : IO Unit := do
  let m := stream $ mat' num
  let x := Σ i, k: matMul_ijjk m m
  time "matrix 1'" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval x
      IO.println s!"{x}"

def testABC (num : ℕ) : IO Unit := do
  let m := stream $ mat' num
  time "matrix abc" fun _ =>
    for _ in [0:10] do
      let x : ArrayMap ℕ (HMap ℕ ℕ) := eval $ ABC m m m
      IO.println s!"{x.1.size}"

def testABC' (num : ℕ) : IO Unit := do
  let m := stream $ mat' num
  time "matrix abc'" fun _ =>
    for _ in [0:10] do
      let x : ArrayMap ℕ (HMap ℕ ℕ) := eval $ ABC' m m m
      IO.println s!"{x.1.size}"

/- Exercise: add a test that invokes matMul_ikjk, otherwise identical to matMul1 -/
def matMul2 (num : ℕ) : IO Unit := sorry

/- Exercise: add a test that invokes vecSum -/

def _root_.main (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"
  --matMul1 num
  --matMul1' num
  testABC num
  testABC' num

open ToStream

instance [Ord ι] : ToStream (RBSet ι Ord.compare) (ι →ₛ Bool) := ⟨sorry⟩
instance [Ord ι] : ToStream (RBMap ι α Ord.compare) (ι →ₛ α) := ⟨sorry⟩

variable
  (locations : RBSet String Ord.compare)
  (predicate : String → Bool)
     (counts : RBMap String Nat Ord.compare)

example : Nat := Id.run $ do
    let mut result := 0
    for key in locations do
      if predicate key then
        result ← result + counts.findD ("prefix_" ++ key) 0
    return result

example : Nat := eval $
  let locations := (imap ("prefix_" ++ .) sorry (stream locations))(i)
  let counts := (stream counts)(i)
  Σ i: predicate(i) * locations * counts

end Etch.Verification.SStream
