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
open OfStream ToStream

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

--set_option trace.compiler.ir.result true in
--set_option trace.compiler.stage2 true in
def vecSum' : ℕ → IO Unit := genCase "vec sum"
  (fun num => let v := vecStream num; contract v)
  (fun x : ℕ => x)

def vecSum := genCase "vec sum"
  (fun (vec : SparseArray ℕ ℕ) => contract $ stream vec)
  (fun x : ℕ => x)

def vecCopy : ℕ → IO Unit := genCase "vec copy"
  (fun num => let v := vecStream num; v)
  (fun x : F ℕ ℕ => x.1.size)

def_index_enum_group i, j

def matSum := genCase "matrix sum"
  (fun (mat : SparseArrayMat ℕ ℕ ℕ) => select => mat(0,1))
  (fun x : ℕ => x)

def matSumRows := genCase "matrix sum rows"
  (fun (mat : SparseArrayMat ℕ ℕ ℕ) => select 1 => mat(0,1))
  (fun x : HashMap ℕ ℕ => x.1.size)

def matSumCols := genCase "matrix sum cols"
  (fun (mat : SparseArrayMat ℕ ℕ ℕ) => select 0 => mat(0,1))
  (fun x : F ℕ ℕ => x.1.size)

open RB

def rbVecSumBaseline := genCase' "baseline rb sum"
  (fun (mat : TreeMap ℕ ℕ) => mat)
  (op := fun mat => mat.foldl (fun acc _ v => acc + v.value) 0)
  (fun x : ℕ => x)

def rbVecSum := genCase "rbVec sum"
  (fun (mat : TreeMap ℕ ℕ) => Σ 0 => mat(0))
  (fun x : ℕ => x)

def mul_SA_rb := genCase "sa * rb"
  (fun (⟨v₁, v₂⟩ : SparseArray ℕ ℕ × TreeMap ℕ ℕ) =>
    let v₁ := stream v₁
    let v₂ := stream v₂
    let x := v₁ * v₂
    let _ : F ℕ ℕ := eval x
    x)
  (fun (x : F ℕ ℕ) => x.1.size)
  (reps := 1)

def mul_SA_rb_baseline := genCase' "baseline: sa * rb"
  (fun (p : SparseArray ℕ ℕ × RBMap ℕ ℕ Ord.compare) => p)
  (op := fun (a,b) => Id.run do
    let mut is : Array ℕ := #[]
    let mut vs : Array ℕ := #[]
    for i in [0:a.is.val.size] do
      let i := a.is.val[i]!
      match b.find? i with
      | none => pure ()
      | some v => do
        is := is.push i
        vs := vs.push $ a.vs.val[i]! * v
    pure (is, vs)
  )
  (fun (x : F ℕ ℕ) => x.1.size)
  (reps := 1)

--set_option trace.compiler.ir.reset_reuse true in
def vecMulSum : ℕ → IO Unit := genCase "vec mul sum"
  (fun num =>
    let v := vecStream num
    let v' := vecStream num |>.map fun _ => 1
    contract $ v * v')
  (fun x : ℕ => x)

-- todo: vecMul' performs additional allocation in the inner loop
--set_option trace.compiler.ir.result true in
def vecMul : ℕ → IO Unit := genCase "vec mul"
    (fun num =>
      let v := vecStream num;
      let v' := vecStream num |>.map fun _ => 1;
      v * v')
    (fun x : F ℕ ℕ => x.1.size)

--set_option trace.compiler.ir.reset_reuse true in
--set_option trace.compiler.stage2 true in
def vecMulSum3 : ℕ → IO Unit := genCase "vec mul 3 sum"
  (fun num =>
    let v  := vecStream num
    let v₁ := vecStream num |>.map fun _ => 1
    let v₂ := vecStream num |>.map fun _ => 1
    contract $ v * (v₁ * v₂))
  (fun x : ℕ => x)

--def vecMul' (num : Nat) : IO Unit := do
--  IO.println "-----------"
--  let v := vecStream num
--  let v' := vecStream num |>.map fun _ => 1
--  let s := v * v'
--  time "vec mul" fun _ =>
--    for _ in [0:10] do
--      let x : SparseArray ℕ ℕ := eval s
--      IO.println s!"{x.1.size}"
--  pure ()

--set_option trace.compiler.ir.reset_reuse true in
def vecMul3 : ℕ → IO Unit := genCase "vec mul 3"
  (fun num =>
    let v  := vecStream num
    let v₁ := vecStream num |>.map fun _ => 1
    let v₂ := vecStream num |>.map fun _ => 1
    v * (v₁ * v₂))
  (fun x : F ℕ ℕ => x.1.size)

def _root_.Nat.cubeRoot (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter n (n / 2)
where
  iter (n guess : Nat) : Nat :=
    let next := (2*guess + n / (guess * guess)) / 3
    if _h : next < guess then
      iter n next
    else
      guess
termination_by iter guess => guess

end test

def double (a : β) := (a,a)

def tests (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  let v := sparseVec num
  let v1 := sparseVecRB num
  let v2 := sparseVecRB num
  let m := sparseMat num.sqrt
  let rb := RBMap.ofList (List.range num |>.map double) Ord.compare

  test.baseline num
  test.vecSum v
  --test.rbVecSum v1 -- about 10x slower
  --test.rbVecSumBaseline v2

  test.mul_SA_rb (v, v1)
  test.mul_SA_rb_baseline (v,rb)
  test.matSum m
  test.matSumRows m
  test.matSumCols m

  --test.vecCopy num
  ----test.vecBoolMul num
  ----test.vecBoolMul3 num
  --test.vecMulSum num
  --test.vecMul num
  --test.vecMul3 num
  ----test.vecMulSum3 num

def main := tests
