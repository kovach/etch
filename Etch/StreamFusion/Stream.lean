import Mathlib.Data.Prod.Lex
import Mathlib.Data.String.Basic
import Init.Data.Array.Basic
import Std.Data.RBMap
import Std.Data.HashMap

import Etch.StreamFusion.Basic
import Etch.StreamFusion.SequentialStream

open Std (RBMap HashMap)

/-
This file implements a prototype of indexed stream fusion,
  an optimization to speed up programs that manipulate (nested) associative arrays.

Authors: Scott Kovach
-/

/- General notes:
  Stream.fold generates the top-level loop.
    For performance, we want this to include no calls to lean_apply_[n] and minimal allocations
      (so far there are still some tuples allocated for multiplication states)
    Some care is needed to ensure everything is inlined.

  Stream.mul is the key combinator.
    It multiplies the non-zero values of two streams by merging their index values.
-/

namespace Etch.Verification

@[ext]
structure Stream (ι : Type) (α : Type u) where
  σ : Type
  valid : σ → Bool
  index : {x // valid x} → ι
  seek  : {x // valid x} → ι ×ₗ Bool → σ
  ready : {x // valid x} → Bool
  value : {x // ready x} → α

-- stream plus a state
structure SStream (ι : Type) (α : Type u) extends Stream ι α where
  q : σ

infixr:25 " →ₛ " => SStream

namespace Stream
variable {ι : Type} {α : Type _} [Mul α]

@[simps]
def imap_general (f : ι → ι') (g : ι → ι' → ι) (s : Stream ι α) : Stream ι' α := {
  s with
  index := fun x => f (s.index x)
  seek  := fun q (j, r) => s.seek q (g (s.index q) j, r)
}

@[simps, macro_inline]
def contract (s : Stream ι α) : Stream Unit α := {
  s with
    index := default,
    seek := fun q ((), r) => s.seek q (s.index q, r)
}

-- For some reason, this definition *definitely* needs to be macro_inline for performance.
--   todo: explain why
-- Most everything else I have checked is safe at @[inline].
@[macro_inline]
def next (s : Stream ι α) (q : {q // s.valid q}) (i : ι) (ready : Bool) : s.σ :=
  s.seek q (i, ready)

@[macro_inline]
def next' (s : Stream ι α) (q : {q // s.valid q}) (ready : Bool) : s.σ :=
  s.seek q (s.index q, ready)

-- todo: try no go?

/- (Important def) Converting a Stream into data
   This definition follows the same inline/specialize pattern as Array.forInUnsafe
-/
@[inline] partial def fold (f : β → ι → α → β) (s : Stream ι α) (q : s.σ) (acc : β) : β :=
  let rec @[specialize] go {σ} (f : β → ι → α → β)
        (valid : σ → Bool)
        (ready : {x // valid x} → Bool)
        (index : {x // valid x} → ι)
        (value : {x // ready x} → α)
        (next  : {x // valid x} → ι → Bool → σ)
        (acc : β) (q : σ) : β :=
      if hv : valid q then
        let q := ⟨q, hv⟩
        let i := index q
        let hr := ready q
        let acc' := if hr : hr then f acc i (value ⟨q, hr⟩) else acc
        let q' := next q i hr
        go f valid ready index value next acc' q'
    else acc
  go f s.valid s.ready s.index s.value s.next acc q

/-
@[inline] partial def fold_old (f : β → ι → α → β) (s : Stream ι α) (q : s.σ) (acc : β) : β :=
  let rec @[specialize] go f
      (valid : s.σ → Bool) (ready : (x : s.σ) → valid x → Bool)
      (index : (x : s.σ) → valid x → ι) (value : (x : s.σ) → (h : valid x) → ready x h → α)
      (next : (x : s.σ) → valid x → Bool → s.σ)
      (acc : β) (q : s.σ) :=
    if hv : valid q then
      if hr : ready q hv
           then go f valid ready index value next (f acc (index q hv) (value q hv hr)) (next q hv true)
           else go f valid ready index value next acc (next q hv false)
    else acc
  go f s.valid (fun q h => s.ready ⟨q,h⟩) (fun q h => s.index ⟨q,h⟩) (fun q v r => s.value ⟨⟨q,v⟩,r⟩) s.next acc q
-/

@[simps]
def map (f : α → β) (s : Stream ι α) : Stream ι β :=
  { s with value := fun h => f (s.value h) }

@[simp] lemma map_id (s : Stream ι α) : s.map id = s := rfl

@[simp] lemma map_id' (s : Stream ι α) : s.map (fun x => x) = s := s.map_id

@[simp] lemma map_map (f : α → β) (g : β → γ) (s : Stream ι α) : (s.map f).map g = s.map (g ∘ f) := rfl

@[inline]
def zero : Stream ι α where
  σ := Unit; valid _ := false; ready _ := false;
  index := fun ⟨_, h⟩ => nomatch h; value := fun ⟨_, h⟩ => nomatch h;
  seek _ _ := ();

instance : Zero (Stream ι α) := ⟨zero⟩
@[simp] lemma zero_σ : (0 : Stream ι α).σ = Unit := rfl
@[simp] lemma zero_valid (q) : (0 : Stream ι α).valid q = false := rfl
@[simp] lemma zero_ready (q) : (0 : Stream ι α).ready q = false := rfl

end Stream

def FloatVec n := { x : FloatArray // x.size = n }

class OfStream (α : Type*) (β : Type*) where
  eval : α → β → β
  -- todo: (⟦ a ⟧ => eval a) notation?

class ToStream (α : Type u) (β : outParam $ Type v) where
  stream : α → β

namespace SStream

variable {ι : Type} [LinearOrder ι] {α : Type u}

@[inline]
def map (f : α → β) (s : ι →ₛ α) : ι →ₛ β := {
  s with value := fun x => f (s.value x)
}

@[macro_inline]
def mapWithIndex (f : ι → α → β) (s : ι →ₛ α) : ι →ₛ β := {
  s with value := fun q => f (s.index q.1) (s.value q)
}

@[simp] lemma map_eq_map (f : α → β) (s : ι →ₛ α) :
  (map f s).toStream = s.toStream.map f := rfl

@[simp] lemma map_q (f : α → β) (s : ι →ₛ α) :
  (map f s).q = s.q := rfl

instance : Functor (ι →ₛ .) where
  map := map

-- todo check this gen code
@[inline] def imap [LinearOrder ι'] (f : ι ≃o ι') (s : ι →ₛ α) : ι' →ₛ α := {
  s with
  index := fun x => f (s.index x)
  seek  := fun q (i, r) => s.seek q (f.symm i, r)
}

/- Converting data into a SStream -/

@[simps!]
instance : Zero (ι →ₛ α) := ⟨⟨0, ()⟩⟩


@[inline] def range (lo hi : ℕ) : ℕ →ₛ Bool where
  σ := ℕ
  q := lo
  valid q := q < hi
  ready _ := true
  index q := q
  value _ := true
  seek q := fun ⟨j, r⟩ =>
    if r then if q ≤ j then q+1 else q
         else if q < j then q+1 else q

@[inline] def DenseArray.toStream {n : ℕ} (arr : DenseArray n α) : Nat →ₛ α :=
  (range 0 n).mapWithIndex fun q _ => arr[q]'sorry

@[inline] def ArraySet.toStream (is : ArraySet ι) : ι →ₛ Bool where
  σ := ℕ
  q := 0
  valid q := q < is.size
  ready _ := true
  index q := (is[q.1]'(by simpa using q.2))
  value _ := true
  seek q := fun ⟨j, r⟩ =>
    let i := (is[q.1]'(by simpa using q.2))
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q

-- benefits from macro_inline (matrix sum)
@[macro_inline]
def SparseArray.toStream.linear.aux (n : Nat) (is : Vec ι n) (vs : Vec α n) : ι →ₛ α where
  σ := ℕ
  q := 0
  valid q := q < n
  ready _ := true
  index q := is.get q.1 (by simpa using q.2)
  value   := fun ⟨q, _⟩ => vs.get q.1 (by simpa using q.2)
  seek q  := fun (j, r) =>
    let i := is.get q.1 (by simpa using q.2)
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
@[macro_inline] def SparseArray.toStream.linear (arr : SparseArray ι α) : ι →ₛ α := SparseArray.toStream.linear.aux arr.n arr.is arr.vs

-- todo test
@[inline]
partial def SparseArray.lookup [Zero α] (arr : SparseArray ι α) : ι → α := fun i =>
  let rec @[specialize] go
  | n => if h : n < arr.n then
    let i' := arr.getI ⟨n, by simpa using h⟩
    (if i' < i then go (n+1) else if i' = i then arr.getV ⟨n, by simpa using h⟩ else 0) else 0
  (go 0)

@[macro_inline]
def SparseArray.toSeqStream (arr : SparseArray ι α) : ι →ₛ! α where
  σ := ℕ
  q := 0
  valid q := q < arr.n
  ready _ := true
  index q := arr.getI q
  value   := fun ⟨q, _⟩ => arr.getV q
  next q  := q + 1

@[inline] def ArraySet.toSeqStream (is : ArraySet ι) : ι →ₛ! Bool where
  σ := ℕ
  q := 0
  valid q := q < is.size
  ready _ := true
  index q := (is[q.1]'(by simpa using q.2))
  value _ := true
  next q := q + 1

-- todo
-- not tested yet
--@[macro_inline]
--def ofFloatArray (is : Array ι) (vs : FloatArray) (eq : is.size = vs.size) : SStream ι Float where
--  σ := ℕ
--  q := 0
--  valid q := q < is.size
--  ready q := q < is.size
--  index k h := (is[k]'(by simpa using h))
--  value k h := (vs[k]'(eq ▸ (by simpa using h)))
--  seek q hq := fun ⟨j, r⟩ =>
--    let i := is[q]'(by simpa using hq)
--    if r then if i ≤ j then q+1 else q
--         else if i < j then q+1 else q

-- Used as a base case for ToStream/OfStream
instance [Scalar α] : ToStream α α := ⟨id⟩

instance {α β} [Zero α] [ToStream α β] : ToStream (SparseArrayLookup ι α) (ι → β) where
  stream := (fun f => ToStream.stream ∘ f) ∘ SparseArray.lookup

-- todo
instance {α β} [ToStream α β] : ToStream (DenseArray n α) (Nat →ₛ β) where
  stream := map ToStream.stream ∘ DenseArray.toStream

instance {α β} [ToStream α β] : ToStream  (SparseArray ι α) (ι →ₛ β) where
  stream := map ToStream.stream ∘ SparseArray.toStream.linear

instance : ToStream  (ArraySet ι) (ι →ₛ Bool) where
  stream := ArraySet.toStream

/-- Convert a data structure to a "stream" function -/
@[inline] def ToStream.asFun {α β ι m} [ToStream α β] [Readable ι α m] : ToStream m (ι → β) where
  stream := fun m i => ToStream.stream (Readable.get m i)

instance {α β ι} [Hashable ι] [BEq ι] [Zero α] [ToStream α β] : ToStream  (HashMap ι α) (ι → β) :=
  ToStream.asFun

--instance : ToStream  (Vec ι n × FloatVec n) (SStream ι Float) where
--  stream := fun (a, b) => ofFloatArray a.1 b.1 (a.property.trans b.property.symm)

@[inline] def fold (f : β → ι → α → β) (s : ι →ₛ α) : β → β := s.toStream.fold f s.q

@[inline] def toSparseArray (s : ι →ₛ α) : SparseArray ι α → SparseArray ι α :=
  s.fold (fun ⟨n, a, b⟩ i v => ⟨n+1, a.push i, b.push v⟩)

@[inline] def toArrayPair (s : ι →ₛ α) : F ι α → F ι α :=
  s.fold (fun ⟨a, b⟩ i v => ⟨a.push i, b.push v⟩)

@[inline] def toArraySet (s : ι →ₛ Bool) : ArraySet ι → ArraySet ι :=
  s.fold (fun s i v => if v then s.push i else s)

instance : Modifiable Nat α (DenseArray n α) where
  update arr i v := arr.modify i v

section eval
open OfStream

instance instBase [Scalar α] [Add α] : OfStream α α where
  eval := Add.add

/- Note!! recursive application of `eval` needs to occur outside of any enclosing functions to achieve full inlining
   (see bad examples below)
-/

instance instContract [OfStream α β] : OfStream (Unit →ₛ α) β where
  eval := fold (fun a _ b => b a) ∘ map eval
  -- bad: fold (fun a _ b => eval b a)

instance instStep [OfStream α β] [Modifiable ι β m] : OfStream (ι →ₛ α) m where
  eval := fold Modifiable.update ∘ map eval
  -- bad: fold fun m k => Modifiable.update m k ∘ eval

-- `toSparseArray` doesn't support update of previous indices; assumes fully formed value is
--   inserted at each step (so pass 0 to recursive eval)
-- todo: pass accurate capacity estimate?
instance [OfStream α β] [Zero β]: OfStream (ι →ₛ α) (SparseArray ι β) where
  eval := fold (fun ⟨n, a, b⟩ i v => ⟨n+1, a.push i, b.push v⟩) ∘ map (eval . 0)

instance [OfStream α β] [Zero β]: OfStream (ι →ₛ α) (F ι β) where
  eval := toArrayPair ∘ map (eval . 0)

instance [OfStream α Bool] : OfStream (ι →ₛ α) (ArraySet ι) where
  eval := toArraySet ∘ map (eval . false)

end eval

@[macro_inline]
def contract (a : ι →ₛ α) : Unit →ₛ α := {
  a.toStream.contract with
  q := a.q
}

section -- todo remove these
@[inline] def expand (a : α) : ι → α := fun _ => a

@[inline] def contract2 : (ι →ₛ ι →ₛ α) → Unit →ₛ Unit →ₛ α := contract ∘ map contract
end

@[inline] def eval [Zero β] [OfStream α β] : α → β := (OfStream.eval . 0)

@[inline]
def memo (β) [Zero β] [OfStream α β] [ToStream β γ] : α → γ :=
  ToStream.stream ∘ (OfStream.eval . (0 : β))

-- indicator for indices ≥ t
def ge (t : ι) : ι →ₛ Bool where
  σ := ι
  q := t
  valid _ := true
  ready _q := true -- may need to be t ≤ _q
  index q := q.val
  value _ := true
  seek _ i := i.1 -- may need check

-- indicator for indices > t
def gt (t : ι) : ι →ₛ Bool where
  σ := ι
  q := t
  valid _ := true
  ready q := t < q
  index q := q.val
  value _ := true
  seek _ i := i.1 -- may need check

-- indicator for indices ≤ t
def le (t : ι) [Bot ι] : ι →ₛ Bool where
  σ := ι
  q := ⊥
  valid q := q ≤ t
  ready _q := true -- may need to be t ≤ _q
  index q := q.val
  value _ := true
  seek _ i := i.1 -- may need check

-- indicator for indices < t
def lt (t : ι) [Bot ι] : ι →ₛ Bool where
  σ := ι
  q := ⊥
  valid q := q < t
  ready _q := true -- may need to be t ≤ _q
  index q := q.val
  value _ := true
  seek _ i := i.1 -- may need check

-- indicator for index = t
def singleton (t : ι) : ι →ₛ Bool where
  σ := Bool; q := true
  valid q := q
  index   := fun | ⟨true, _⟩ => t
  seek _  := fun (i, ready) => (ready ∧ i < t) ∨ (¬ ready ∧ i ≤ t)
  ready _ := true
  value _ := true

@[inline] def imap' (f : ι → ι') (s : ι →ₛ α) : ι' →ₛ! α := {
  q := s.q
  valid := s.valid
  index := fun q => f (s.index q)
  next := fun q => s.seek q (s.index q, s.ready q)
  ready := s.ready
  value := s.value
}

@[inline] def downgrade (s : ι →ₛ α) : ι →ₛ! α := s.imap' id

end SStream

-- todo: Stream extend SequentialStream, default `next`
namespace SequentialStream

@[inline] def range (lo hi : ℕ) : ℕ →ₛ! Bool where
  σ := ℕ
  q := lo
  valid q := q < hi
  ready _ := true
  index q := q
  value _ := true
  next q := q+1

-- not working
@[inline] def range' (lo hi : USize) : USize →ₛ! Bool where
  σ := USize
  q := lo
  valid q := q < hi
  ready _ := true
  index q := q
  value _ := true
  next q := q+1

@[macro_inline]
def mapWithIndex (f : ι → α → β) (s : ι →ₛ! α) : ι →ₛ! β := {
  s with value := fun q => f (s.index q.1) (s.value q)
}

@[macro_inline]
def mapWithIndex' (s : ι →ₛ! α) (f : { q // s.valid q } → ι → α → β): ι →ₛ! β := {
  s with value := fun q => f q (s.index q.1) (s.value q)
}

@[inline] def DenseArray.toSeqStream {n : ℕ} (arr : DenseArray n α) : Nat →ₛ! α :=
  (range 0 n).mapWithIndex fun q _ => arr[q]'sorry

@[inline] def DenseArray.toSeqStream' {n : ℕ} (arr : DenseArray n α) : USize →ₛ! α :=
  (range' 0 (USize.ofNat n)).mapWithIndex fun q _ => arr.uget q sorry -- arr[q]'sorry

@[inline] def imap' (f : ι → ι') (s : ι →ₛ! α) : ι' →ₛ! α := {
  s with
  index := fun q => f (s.index q)
}

open OfStream

instance instContract [OfStream α β] : OfStream (Unit →ₛ! α) β where
  eval := fold (fun a _ b => b a) ∘ map eval

instance instStep [OfStream α β] [Modifiable ι β m] : OfStream (ι →ₛ! α) m where
  eval := fold Modifiable.update ∘ map eval

end SequentialStream

end Etch.Verification

-- todo: switch back to linear order
@[inline]
instance : LE String where
  le a b := match Ord.compare a b with | .gt => false | _ => true

@[inline]
instance : LT String where
  lt a b := match Ord.compare a b with | .lt => true | _ => false

-- inlines needed
@[inline]
instance : DecidableRel (. ≤ . : String → String → Prop) :=
  fun a b => match h : Ord.compare a b with
    | .gt => isFalse fun p => by simp [LE.le] at p; rw [h] at p; exact p;
    | .lt => isTrue $ by simp [LE.le, h];
    | .eq => isTrue $ by simp [LE.le, h];

@[inline]
instance : DecidableRel (. < . : String → String → Prop) :=
  fun a b => match h : Ord.compare a b with
    | .lt => isTrue $ by simp [LT.lt, h];
    | .gt => isFalse fun p => by simp [LT.lt] at p; rw [h] at p; exact p;
    | .eq => isFalse fun p => by simp [LT.lt] at p; rw [h] at p; exact p;

@[inline]
instance : Max String where
  max a b := if a < b then b else a
