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

def_index_enum_group i,j,k,l

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

--def testContractElab (A : I →ₛ J →ₛ α) (B : J →ₛ K →ₛ α) := Σ j k => (Σ i => A(i,j)) * B(j,k)
-- i~Unit →ₛ j~Unit →ₛ k~K →ₛ α
--#print testContractElab
/-
Contract.contract j
    (Contract.contract i ([(i, I), (j, J), (k, K)] ⇑ Label.label [i, j] A) *
      [(i, Unit), (j, J), (k, K)] ⇑ Label.label [j, k] B)
-/

@[inline] def testSelect (m : I →ₛ J →ₛ α) (v : J →ₛ α) := memo(select i => m(i, j) * v(j) with SparseArray I α)
-- I →ₛ α

/- Some examples of notation

  notes:
    - a shape is a list of (Nat, Type) pairs
    - a collection needs to have a ToStream instance
    - indices are index names encoded as natural numbers for now
-/

@[inline] def vecSum (v : I →ₛ α) := Σ i => v(i)
@[inline] def matSum (m : I →ₛ J →ₛ α) (v : J →ₛ α) := Σ i j => m(i, j) * v(j)


@[inline] def matMul_ijjk (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) :=
  Σ j => a(i,j) * b(j,k)

variable [Hashable K]
-- todo: investigate these definitions and other approaches
@[inline] def ABC
    (a : I →ₛ J →ₛ α)
    (b : J →ₛ K →ₛ α)
    (c : K →ₛ L →ₛ α) :=
  let m1 :=  a(i,j)
  let m2 :=  b(j,k)
  let m3 :=  c(k,l)
  let x : SparseArray I (HashMap K α) := eval $ Σ j => m1 * m2
  let m  := (stream x)(i,k) * m3
  Σ k => m

@[inline] def ABC' (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) (c : K →ₛ L →ₛ α) :=
  let ijk := [(i,I),(j,J),(k,K)]
  let m1 := ijk ⇑ a(i,j)
  let m := m1.map fun row =>
             memo(Σ j => row * b(j,k) with HashMap K α)
  let m  := m(i,k) * c(k,l)
  Σ k => m

def mat' (num : ℕ) := sparseMat num.sqrt

def matMul1 (num : ℕ) : IO Unit := do
  let m := stream $ mat' num
  let x := matMul_ijjk m m
  time "matrix 1'" fun _ =>
    for _ in [0:10] do
      let x : HashMap ℕ (HashMap ℕ ℕ) := eval x
      IO.println s!"{x.1.size}"

def matMul1' (num : ℕ) : IO Unit := do
  let m := stream $ mat' num
  let x := matMul_ijjk m m
  let x := Σ i k => matMul_ijjk m m
  time "matrix 1'" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval x
      IO.println s!"{x}"

def testABC (num : ℕ) : IO Unit := do
  let m := stream $ mat' num
  time "matrix abc" fun _ =>
    for _ in [0:10] do
      let x : SparseArray ℕ (HashMap ℕ ℕ) := eval $ ABC m m m
      IO.println s!"{x.1.size}"

def testABC' (num : ℕ) : IO Unit := do
  let m := stream $ mat' num
  time "matrix abc'" fun _ =>
    for _ in [0:10] do
      let x : SparseArray ℕ (HashMap ℕ ℕ) := eval $ ABC' m m m
      IO.println s!"{x.1.size}"

def _root_.main (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"
  --matMul1 num
  --matMul1' num
  testABC num
  testABC' num

open ToStream
