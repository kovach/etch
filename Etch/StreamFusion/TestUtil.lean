import Etch.StreamFusion.Stream
import Etch.StreamFusion.Traversals

def csvHeader := "time,test\n"

def time (s : String) (m : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  IO.println s!"[{s}] time: {t1-t0}"
  pure v

def time' (s : String) (m : Unit → IO α) : IO (α × ℕ) := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  pure (v, t1-t0)

open Etch.Verification
open SStream
open OfStream ToStream

variable
{ι ι' : Type}
[LinearOrder ι] [LinearOrder ι']

@[inline] def sparseVec (num : Nat) :=
  let v  : Vec ℕ num := ⟨Array.range num, Array.size_range⟩
  SparseArray.mk v v

@[inline] def sparseVecRB (num : Nat) :=
  RB.TreeMap.ofArray $ (Array.range num).map fun n => (n,n)

@[inline] def vecStream (num : Nat) :=
  let v  : Vec ℕ num := ⟨Array.range num, Array.size_range⟩
  stream $ SparseArray.mk v v

@[inline]
def SparseArray.range (num : Nat) : SparseArray ℕ ℕ :=
  let v := Vec.range num; SparseArray.mk v v

@[inline] def sparseMat (num : Nat) :=
  let v := SparseArray.range num
  v.mapVals fun _ => SparseArray.range num

@[inline, specialize] def sparseMatFn (f : ℕ → ℕ → α) (num : Nat) :=
  let v := SparseArray.range num
  v.mapVals fun i => (SparseArray.range num |>.mapVals fun j => f i j)

@[inline] def boolStream (num : Nat) : ℕ →ₛ Bool:=
  stream $ Array.range num

-- todo investigate perf differences
@[specialize]
def genCase [OfStream α β] [Zero β] (label : String) (setup : init → α) [ToString β'] (print : β → β') (num : init) (reps := 10) : IO Unit := do
  IO.println s!"reps: {reps}-----"
  let s := setup num
  time label fun _ => do
    for i in [0:reps] do
      let x := SStream.eval s
      if i % 1000000 = 0 then
        IO.println s!"{print x}"

@[specialize]
def genCase'' (label : String) (setup : init → α) (op : α → β) [ToString β'] (print : β → β') (num : init) (reps := 10) : IO Unit := do
  IO.println s!"reps: {reps}-----"
  let s := setup num
  time label fun _ => do
    for i in [0:reps] do
      let x := op s
      if i % 1000000 = 0 then
        IO.println s!"{print x}"


def appendFile (fname : System.FilePath) (content : String) : IO Unit := do
  let h ← IO.FS.Handle.mk fname IO.FS.Mode.append
  h.putStr content

def resetFile (f : System.FilePath) := IO.FS.writeFile f csvHeader

def recordTestCases (file : System.FilePath) (cases : List (System.FilePath → IO Unit)) : IO Unit := do
  resetFile file
  cases.forM fun case => case file

@[specialize]
def recordTestCase (file : System.FilePath) (label : String) (setup : init → α) (op : α → β)
    [ToString β'] (print : β → β') (data : init) (reps := 10) : IO Unit := do
  IO.println s!"--- test case: {file}:{label} ---"
  let s := setup data
  let go := fun () => time' label fun _ => pure (op s)
  for _ in [0:5] do _ ← go () -- warmup
  let mut result := ""
  for _ in [0:reps] do -- test
    let (x, t) ← go ()
    result := result ++ s!"{t},{label}\n"
    IO.println s!"{print x}"
  appendFile file result

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
