import Std.Data.RBMap
import Std.Data.HashMap

import Etch.StreamFusion.Basic
import Etch.StreamFusion.Stream
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.Expand
import Etch.StreamFusion.Traversals
import Etch.StreamFusion.TestUtil

open Std (RBMap RBSet HashMap)
open Etch.Verification
open SStream RB
--open OfStream
open ToStream

namespace test

-- these tests need to be separate defs for profile legibility
def baseline (num : Nat) : IO Unit := do
  IO.println "-----------"
  let arr_ := Array.range num
  --let arr := arr_ |>.map fun n => (n,n)
  time "baseline (forIn) vec sum" fun _ =>
    for _ in [0:10] do
      let mut m := 0
      for i in arr_ do
        m := m + i
      IO.println s!"{m}"

/-
def vecBoolMul : Nat → IO Unit := genCase
  "vec mul filter 2"
  (setup := fun num => do
    let b := boolStream num
    b * (vecStream num))
  (print := fun x : SparseArray ℕ ℕ => s!"{x.1.size}")

def vecBoolMul3 : Nat → IO Unit := genCase
  "vec mul filter 3"
  (setup := fun num => do
    let b := boolStream num
    b * (b * vecStream num))
  (print := fun x : SparseArray ℕ ℕ => x.1.size)
-/

--def testFloat (num : Nat) : IO Unit := do
--  IO.println "-----------"
--  let s := contract $ floatVecStream num
--  time "float stream" fun _ =>
--    for _ in [0:10] do
--      let x : Float := eval s
--      IO.println s!"{x}"

def vecMul_rb (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream num
  let s := v * (v.map fun _ => 1)
  time "vec mul rb" fun _ =>
    for _ in [0:10] do
      let x : RBMap ℕ ℕ Ord.compare := eval s
      IO.println s!"{x.1.size}"
  pure ()

def vecMul_hash (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream num
  let v' := vecStream num |>.map fun _ => 1
  let s := v * v'
  time "vec mul hash" fun _ =>
    for _ in [0:10] do
      let x : HashMap ℕ ℕ := eval s
      IO.println s!"{x.1.size}"
  pure ()

def_index_enum_group i,j

def summationFile := "plot4.csv"

def vecSum'' := genCase' summationFile "vec"
  (fun x => x)
  (fun (vec : (n : Nat) × DenseArray n ℕ) => let vec := vec.2; eval $ Σ i => (SequentialStream.DenseArray.toSeqStream vec)(i))
  (fun x : ℕ => x)

def matSum := genCase' summationFile "matrix"
  id
  (fun (mat : SparseArrayMat ℕ ℕ ℕ) => eval $ select => mat(i,j))
  (fun x : ℕ => x)

def baseline' := genCase' summationFile "baseline"
  id
  (fun arr : Array ℕ => Id.run $ do
      let mut m := 0
      for i in arr do
        m := m + i
      pure m)
  (fun x : ℕ => x)

end test
open test

def double (a : β) := (a,a)

def tests (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  let v := sparseVec num
  let v1 := sparseVecRB num
  let v2 := sparseVecRB num
  let m := sparseMat $ num.sqrt + 1
  let rb := RBMap.ofList (List.range num |>.map double) Ord.compare

  resetFile summationFile
  test.baseline' (Array.range num) -- 91
  test.vecSum'' ⟨v.n, v.vs.val⟩ -- 138
  test.matSum m -- 129

def main := tests
