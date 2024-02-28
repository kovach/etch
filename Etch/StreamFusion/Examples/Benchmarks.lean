import Etch.StreamFusion.Examples.Basic

namespace Etch.Verification

open Std (RBMap RBSet HashMap)
open Lean (HashSet)
open Etch.Verification RB
open SStream ToStream

namespace memo'

variable {I J K L α β : Type}
[LinearOrder I] [LinearOrder J] [LinearOrder K] [LinearOrder L]
[Hashable K]
[Scalar α] [Mul α] [Zero α] [Add α]
{dim : Nat}
(a : DenseArray dim (SparseArray Nat α))
(b : DenseArray dim (SparseArray Nat α))
(c : DenseArray dim (SparseArray Nat α))

def_index_enum_group i,j,k,l

@[inline] def ABC' (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) (c : K →ₛ L →ₛ α) :=
  Σ j k => a(i,j)*b(j,k)*c(k,l)

@[inline] def ABC : DenseArray dim (SparseArray Nat α) := eval $
  Σ j k => a(i,j)*b(j,k)*c(k,l)
  -- select i, l => a(i,j)*b(j,k)*c(k,l)

--@[inline] def ABC_memo' (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) (c : K →ₛ L →ₛ α) :=
--  Σ k => memo(Σ j=> a(i,j)*b(j,k) with SparseArray I (HashMap K α)) * c(k,l)

@[inline] def ABC_memo_old (a : I →ₛ J →ₛ α) (b : J →ₛ K →ₛ α) (c : K →ₛ L →ₛ α) :=
  let ijk := [(i,I),(j,J),(k,K)]
  let m1 := ijk ⇑ a(i,j)
  let m := m1.map fun row =>
             (memo HashMap K α from Σ j => row * b(j,k))
  let m  := m(i,k) * c(k,l)
  Σ k => m

@[inline] def ABC_memo : DenseArray dim (HashMap Nat α) := eval $
  let m := a(i,j).map fun row =>
             (memo HashMap Nat α from Σ j => row(j) * b(j,k))
  let m  := m(i,k) * c(k,l)
  Σ k => m

structure foo where
  dim : Nat
  (a : DenseArray dim (SparseArray Nat Nat))
  (b : DenseArray dim (SparseArray Nat Nat))
  (c : DenseArray dim (SparseArray Nat Nat))

def t1 := genCase' "ABC fused"
    (fun p : foo => p)
    (op := fun ⟨_, a, b, c⟩ => ABC a b c)
    (fun x => (x.size))

def t2 := genCase' "ABC memo"
    (fun p : foo => p)
    (op := fun ⟨_, a, b, c⟩ => ABC_memo a b c)
    (fun x => (x.size))

end memo'

def randStrings (num : Nat) : IO (Array String) := do
  let mut result := #[]
  for _ in [0:num] do
    let n ← IO.rand 1 (num*2)
    result := result.push n
  pure $ result.qsort (·<·) |>.deduplicateSorted |>.map toString

def randNats (num : Nat) : IO (Array Nat) := do
  let mut result := #[]
  for _ in [0:num] do
    let n ← IO.rand 1 (num*2)
    result := result.push n
  pure $ result.qsort (·<·) |>.deduplicateSorted

def tests1 (num : Nat) : IO Unit := do
  let s1 ← randStrings num
  let s2 ← randStrings num
  let _ := TreeSet.ofArray s1
  let strs := s1
  let counts := HashMap.ofList (s2.map fun str => (str, 1)).toList

  t1 (strs, counts)
  t2 (strs, counts)
  t3 (strs, counts)
  --t4 num

-- 317 vs 290
def tests2 (num : Nat) : IO Unit := do
  let s1 ← randStrings num
  let s2 ← randStrings num
  let s3 ← randStrings num

  let a : SparseArray String (ArraySet String) :=
     SparseArray.mk_unsafe s1 $ s1.map fun s => s2
  let b : SparseArray String (ArraySet String) :=
     SparseArray.mk_unsafe s2 $ s2.map fun s => s3
  let c : SparseArray String (ArraySet String) :=
     SparseArray.mk_unsafe s1 $ s1.map fun s => s3

  let b' : HashMap String (ArraySet String) :=
     HashMap.ofList $ s2.toList.zip (s2.map fun s => s3).toList
  let c' : HashMap String (ArraySet String) :=
     HashMap.ofList $ s1.toList.zip (s1.map fun s => s3).toList

  --eg2.t1 ⟨a,b,c⟩
  eg2.t2 ⟨a,b',c'⟩
  eg2.t3 ⟨a,b,c⟩


def tests3 (num : Nat) : IO Unit := do
  let s1 ← randStrings num
  let s2 ← randStrings num
  let _ := TreeSet.ofArray s1
  let strs := s1
  let counts := HashMap.ofList (s2.map fun str => (str, 1)).toList
  t4 num

def tests4 (num : Nat) : IO Unit := do
  let gen _ := Array.range num |>.mapM fun _ => (do
    let nats ← randNats 10
    pure $ SparseArray.mk_unsafe nats (.range nats.size))
  let a ← gen ()
  let b ← gen ()
  let c ← gen ()
  memo'.t1 ⟨num,a,b,c⟩
  memo'.t2 ⟨num,a,b,c⟩

def tests4' (num : Nat) : IO Unit := do
  let genR _ := Array.range num |>.mapM fun _ => (do
    let nats ← randNats $ (num*2)
    pure $ SparseArray.mk_unsafe nats (.range nats.size))
  let genL _ := Array.range (num*2) |>.mapM fun _ => (do
    let nats ← randNats $ num
    pure $ SparseArray.mk_unsafe nats (.range nats.size))
  let a ← genR ()
  let b ← genL ()
  let c ← genR ()
  memo'.t1 ⟨num,a,b,c⟩
  memo'.t2 ⟨num,a,b,c⟩

def tests (_num : Nat) := do
  --tests1 100000 -- 21 20 26
  --tests2 100    -- 317 290
  --tests4 1000    -- 48 663 -- 1000 * 10
  tests4' 100   -- 463 145  -- 100 * 200

def _root_.main (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"
  IO.println s!"starting (IGNORING [num={num}])"

  tests num

end Etch.Verification
