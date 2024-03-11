-- Tests should be in separate defs for better profile legibility

import Etch.StreamFusion.Examples.Basic

namespace Etch.Verification

open Std (RBMap RBSet HashMap)
open Lean (HashSet)
open Etch.Verification RB
open SStream ToStream

-- todo, cli flag
def namePrefix := ""
--def namePrefix := "alt_"

namespace memoTest

variable {I J K L α β : Type}
[LinearOrder I] [LinearOrder J] [LinearOrder K] [LinearOrder L]
[Hashable K]
[Scalar α] [Mul α] [Zero α] [Add α]
{dim : Nat}
(a : DenseArray dim (SparseArray Nat α))
(b : DenseArray dim (SparseArray Nat α))
(c : DenseArray dim (SparseArray Nat α))

def_index_enum_group i,j,k,l

namespace no
def ABC_memo (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) (c : K →ₛ L →ₛ α) :=
  Σ k => (memo SparseArray I (HashMap K α) from Σ j => a(i,j) * b(j,k)) * c(k,l)
end no

@[inline] def ABC : DenseArray dim (HashMap Nat α) := eval $
  Σ j k => a(i,j)*b(j,k)*c(k,l)

@[inline] def ABC_memo : DenseArray dim (HashMap Nat α) := eval $
  let ab := (memo SparseArray Nat (HashMap Nat α) from Σ j => a(i,j) * b(j,k))
  Σ k => ab * c(k,l)

@[inline] def ABC_memo_old (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) (c : K →ₛ L →ₛ α) :=
  let ijk := [(i,I),(j,J),(k,K)]
  let m1 := ijk ⇑ a(i,j)
  let m := m1.map fun row =>
             (memo HashMap K α from Σ j => row * b(j,k))
  let m  := m(i,k) * c(k,l)
  Σ k => m

structure foo := (dim : Nat) (a b c : DenseArray dim (SparseArray Nat Nat))

def t1 x := fun d file => recordTestCase file ("mul" ++ x)
    (fun p : foo => p)
    (op := fun ⟨_, a, b, c⟩ => ABC a b c)
    (fun x => (x.size))
    d

def t2 x := fun d file => recordTestCase file ("memo" ++ x)
    (fun p : foo => p)
    (op := fun ⟨_, a, b, c⟩ => ABC_memo a b c)
    (fun x => (x.size))
    d

end memoTest

def simpleTest (num : Nat) : IO Unit := do
  let s1 ← randStrings num
  let s2 ← randStrings num
  let _ := TreeSet.ofArray s1
  let strs := s1
  let counts := HashMap.ofList (s2.map fun str => (str, 1)).toList

  recordTestCases (namePrefix ++ "plot1.csv")
    [ t1 (strs, counts)
    , t2 (strs, counts)
    , t3 (strs, counts) ]

def triQueryTest (num : Nat) : IO Unit := do
  let s1 ← randStrings num
  let s2 ← randStrings num
  let s3 ← randStrings num

  let a : SparseArray String (ArraySet String) := SparseArray.mk_unsafe s1 $ s1.map fun _ => s2
  let b : SparseArray String (ArraySet String) := SparseArray.mk_unsafe s2 $ s2.map fun _ => s3
  let c : SparseArray String (ArraySet String) := SparseArray.mk_unsafe s1 $ s1.map fun _ => s3
  let b' : HashMap String (ArraySet String) := HashMap.ofList $ s2.toList.zip (s2.map fun _ => s3).toList
  let c' : HashMap String (ArraySet String) := HashMap.ofList $ s1.toList.zip (s1.map fun _ => s3).toList

  recordTestCases (namePrefix ++ "plot2.csv")
    [ eg2.t2 ⟨a,b',c'⟩
    , eg2.t3_unfused ⟨a,b,c⟩
    , eg2.t3_fused ⟨a,b,c⟩ ]

def memoTest (num1 num2 : Nat) : IO Unit := do
  let gen num := Array.range num |>.mapM fun _ => (do
    let nats ← randNats 10
    pure $ SparseArray.mk_unsafe nats (.range nats.size))
  let genR num := Array.range num |>.mapM fun _ => (do
    let nats ← randNats $ (num*2)
    pure $ SparseArray.mk_unsafe nats (.range nats.size))
  let genL num := Array.range (num*2) |>.mapM fun _ => (do
    let nats ← randNats $ num
    pure $ SparseArray.mk_unsafe nats (.range nats.size))
  let a1 ← gen num1
  let b1 ← gen num1
  let c1 ← gen num1
  let a2 ← genR num2
  let b2 ← genL num2
  let c2 ← genR num2
  recordTestCases (namePrefix ++ "plot3.csv")
    -- 1 = fused is faster; 2 = memo is faster
    [ memoTest.t1 "1" ⟨num1,a1,b1,c1⟩
    , memoTest.t2 "1" ⟨num1,a1,b1,c1⟩
    , memoTest.t1 "2" ⟨num2,a2,b2,c2⟩
    , memoTest.t2 "2" ⟨num2,a2,b2,c2⟩ ]

namespace baseline
def vecSum := fun d file => recordTestCase file "vec"
  (fun x => x)
  (fun (vec : (n : Nat) × DenseArray n ℕ) => let vec := vec.2; eval $ Σ i => (SequentialStream.DenseArray.toSeqStream vec)(i))
  (fun x : ℕ => x)
  d

--set_option trace.compiler.inline true
def matSum := fun d file => recordTestCase file "matrix"
  id
  (fun (mat : SparseArrayMat ℕ ℕ ℕ) => eval $ select => mat(i,j))
  (fun x : ℕ => x)
  d

def baseline := fun d file => recordTestCase file "baseline"
  id
  (fun arr : Array ℕ => Id.run $ do
      let mut m := 0
      for i in arr do
        m := m + i
      pure m)
  (fun x : ℕ => x)
  d
end baseline

def baselineTest (num : Nat) : IO Unit := do
  let v := sparseVec num
  let m := sparseMat $ num.sqrt + 1
  recordTestCases (namePrefix ++ "plot4.csv")
    [ baseline.baseline (Array.range num) -- 91
    , baseline.vecSum ⟨v.n, v.vs.val⟩ -- 138
    , baseline.matSum m -- 129
    ]

section mul
abbrev S := SparseArray ℕ ℕ × SparseArray ℕ ℕ
abbrev S' := SparseArrayMat ℕ ℕ ℕ × SparseArrayMat ℕ ℕ ℕ
abbrev S3 := SparseArray ℕ ℕ × SparseArray ℕ ℕ × SparseArray ℕ ℕ

def vecMulSum := fun d file => recordTestCase file "vecMulSum"
  id
  (fun (x : S) => eval $ select => x.1(i) * x.2(i))
  (fun x : ℕ => x)
  (reps := 2)
  d

def vecMul := fun d file => recordTestCase file "vecMul"
  id
  (fun (x : S) => eval $ x.1(i) * x.2(i))
  (fun x : SparseArray ℕ ℕ => x.n)
  d

def vecMul3 := fun d file => recordTestCase file "vecMul3"
  id
  (fun ((a,b,c) : S3) => eval $ a(i) * b(i) * c(i))
  (fun x : SparseArray ℕ ℕ => x.n)
  d


def matElemMulSum := fun d file => recordTestCase file "matrixElemMulSum"
  id
  (fun (x : S') => eval $ select => x.1(i,j) * x.2(i,j))
  (fun x : ℕ => x)
  d

def mulTests (num : Nat) : IO Unit := do
  let s1 := (sparseVec num, sparseVec num |>.mapVals fun _ => 1)
  let s2 := (sparseMat num.sqrt, sparseMatFn num.sqrt (f := fun _ _ => 1))
  let s3 := (sparseVec num, sparseVec num |>.mapVals fun _ => 1, sparseVec num |>.mapVals fun _ => 1)
  recordTestCases (namePrefix ++ "plot5.csv")
    [ baseline.baseline (Array.range num)
    , vecMul s1
    , vecMul3 s3
    , vecMulSum s1
    , matElemMulSum s2
    ]
end mul

def tests (_num : Nat) := do
  mulTests _num
  baselineTest 5000000
  simpleTest 100000
  triQueryTest 100
  memoTest 400 40

def _root_.main (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"
  IO.println s!"starting (IGNORING [num={num}])"

  tests num

end Etch.Verification
