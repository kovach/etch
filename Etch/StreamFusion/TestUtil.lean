import Etch.StreamFusion.Stream

def time (s : String) (m : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  IO.println s!"[{s}] time: {t1-t0}"
  pure v

open Etch.Verification
open SStream
open OfStream ToStream

variable
{ι ι' : Type}
[LinearOrder ι] [LinearOrder ι']

@[inline]
def ofMat [Scalar α] (is : Array (ι × Array ι')) (vs : ι → ι' → α) : ι →ₛ ι' →ₛ α :=
  stream $ is.map fun (row, cs) => (row, cs.map fun col => (col, vs row col))

@[inline]
def ofMat' [Scalar α] (is : Array (ℕ × Array ℕ)) (vs : ℕ → ℕ → α) :=
  is.map fun (row, cs) => (row, cs.map fun col => (col, vs row col))

-- adjusts size so that there are ~num non-zero entries
@[macro_inline] -- macro_inline needed!
def mat (num : ℕ) :=
  let is : Array (ℕ × Array ℕ) :=
    Array.range (2*num).sqrt |>.map id |>.map $ fun n => (n, Array.range num)
  ofMat is fun _ _ => 1

@[macro_inline] -- macro_inline needed!
def mat' (num : ℕ) :=
  let is : Array (ℕ × Array ℕ) :=
    Array.range (2*num).sqrt |>.map id |>.map $ fun n => (n, Array.range num)
  ofMat' is fun _ _ => 1

@[macro_inline] -- macro_inline needed!
def str_mat (num : ℕ) :=
  let is : Array (String × Array String) :=
    Array.range (2*num).sqrt |>.map toString |>.map $ fun n => (n, Array.range num |>.map toString)
  ofMat is fun _ _ => 1
