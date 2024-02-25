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

import Mathlib.Data.Prod.Lex
 import Mathlib.Data.String.Basic
import Init.Data.Array.Basic
import Std.Data.RBMap
import Std.Data.HashMap
import Mathlib.Data.ByteArray

open Std (RBMap HashMap)

-- hack: redefine these instances to ensure they are inlined (see instDecidableLeToLEToPreorderToPartialOrder)
-- note: we are not relying on LinearOrder any more
section
variable [LinearOrder α]
@[inline] instance (a b : α) : Decidable (a < b) := LinearOrder.decidableLT a b
@[inline] instance (a b : α) : Decidable (a ≤ b) := LinearOrder.decidableLE a b
@[inline] instance (a b : α) : Decidable (a = b) := LinearOrder.decidableEq a b
end

namespace Std

@[inline]
def RBMap.toFn [Ord ι] [Zero α] (map : RBMap ι α Ord.compare) : ι → α := fun i => map.find? i |>.getD 0

@[inline]
def HashMap.modifyD [BEq α] [Hashable α] [Zero β] (self : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  self.insert a (f $ self.findD a 0)

@[inline]
def HashMap.modifyD' [BEq α] [Hashable α] [Zero β] (self : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  if self.contains a then self.modify a (fun _ => f) else self.insert a (f 0)

@[inline]
def RBMap.modifyD [Zero β] (self : RBMap α β h) (a : α) (f : β → β) : RBMap α β h :=
  self.insert a (f $ self.findD a 0)
  --self.alter a (fun | none => some 0 | some a => some (f a))
end Std

abbrev Map a [Ord a] b := RBMap a b Ord.compare
abbrev HMap a [BEq a] [Hashable a] b := HashMap a b

instance [EmptyCollection α] : Zero α := ⟨{}⟩

class Modifiable (k v : outParam Type*) (m : Type*) where
  update : m → k → (v → v) → m

instance [BEq α] [Hashable α] [Zero β] : Modifiable α β (HashMap α β) where
  update := HashMap.modifyD'

instance [Zero β] : Modifiable α β (RBMap α β h) where
  update := RBMap.modifyD

namespace Etch.Verification

-- add `next` as field with default implementation?
structure Stream (ι : Type) (α : Type u) where
  σ : Type
  valid : σ → Bool
  ready : {x // valid x} → Bool
  seek  : {x // valid x} → ι ×ₗ Bool → σ
  index : {x // valid x} → ι
  value : {x // ready x} → α

-- stream plus a state
structure SStream (ι : Type) (α : Type u) extends Stream ι α where
  q : σ

infixr:25 " →ₛ " => SStream

namespace Stream
variable {ι : Type} {α : Type _} [Mul α]

@[simps, macro_inline]
def contract (s : Stream ι α) : Stream Unit α where
  σ := s.σ
  valid := s.valid
  ready := s.ready
  index := default
  seek q := fun ((), r) => s.seek q (s.index q, r)
  value := s.value

-- todo: why ready

-- For some reason, this definition *definitely* needs to be macro_inline for performance.
--   todo: explain why
-- Most everything else I have checked is safe at @[inline].
@[macro_inline]
def next (s : Stream ι α) (q : {q // s.valid q}) (i : ι) (ready : Bool) : s.σ :=
  s.seek q (i, ready)

def next_ (s : Stream ι α) (q : s.σ) (h : s.valid q = true) (ready : Bool) : s.σ :=
  let q := ⟨q, h⟩; s.seek q (s.index q, ready)

@[macro_inline]
def next' (s : Stream ι α) (q : {q // s.valid q}) (ready : Bool) : s.σ :=
  s.seek q (s.index q, ready)



-- todo: try no go?

/- (Important def) Converting a Stream into data
   This definition follows the same inline/specialize pattern as Array.forInUnsafe
-/
-- todo: evaluate this vs other version
@[inline] partial def fold (f : β → ι → α → β) (s : Stream ι α) (q : s.σ) (acc : β) : β :=
  let rec @[specialize] go f
      (valid : s.σ → Bool) (ready : (x : s.σ) → valid x → Bool)
      (index : (x : s.σ) → valid x → ι) (value : (x : s.σ) → (h : valid x) → ready x h → α)
      (next : {x // valid x} → ι → Bool → s.σ)
      --(next : (x : s.σ) → valid x → Bool → s.σ)
      (acc : β) (q : s.σ) :=
    if hv : valid q then
      let i := index q hv
      let hr := ready q hv
      let acc' := if hr : hr then f acc i (value q hv hr) else acc
      let q' := next ⟨q, hv⟩ i hr
      go f valid ready index value next acc' q'
    else acc
  go f s.valid (fun q h => s.ready ⟨q,h⟩) (fun q h => s.index ⟨q,h⟩) (fun q v r => s.value ⟨⟨q,v⟩,r⟩) s.next
     acc q

-- this one is a little more uniform, and has better inlining behavior for products, but worse behavior for very simple examples
@[inline] partial def fold' (f : β → ι → α → β) (s : Stream ι α) (q : s.σ) (acc : β) : β :=
  let rec @[specialize] go f
      (valid : s.σ → Bool)
      (ready : {x // valid x} → Bool)
      (index : {x // valid x} → ι)
      (value : (x : {x // ready x}) → α)
      --(value : (x : {x // valid x}) → ready x → α)
      (next : {x // valid x} → Bool → s.σ)
      --(next : (x : s.σ) → valid x → Bool → s.σ)
      (acc : β) (q : s.σ) :=
    if hv : valid q then
      let q := ⟨q, hv⟩
      let i := index q
      let hr := ready q
      let acc' := if hr : hr then f acc i (value ⟨q, hr⟩) else acc
      let q' := next q hr
      go f valid ready index value next acc' q'
    else acc
  go f s.valid s.ready s.index s.value s.next' acc q

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

end Stream

def FloatVec n := { x : FloatArray // x.size = n }

class OfStream (α : Type*) (β : Type*) where
  eval : α → β → β
  -- todo: (⟦ a ⟧ => eval a) notation?

class ToStream (α : Type u) (β : outParam $ Type v) where
  stream : α → β

namespace SStream

variable {ι : Type} [LinearOrder ι] {α : Type u}

@[macro_inline]
def map (f : α → β) (s : ι →ₛ α) : ι →ₛ β := {
  s with value := f ∘ s.value
}

instance : Functor (ι →ₛ .) where
  map := map

@[inline]
-- todo check this gen code
def imap [LinearOrder ι'] (f : ι ≃o ι') (s : ι →ₛ α) : ι' →ₛ α := {
  s with
  index := f ∘ s.index
  seek  := fun q (i, r) => s.seek q (f.symm i, r)
}

variable [Inhabited ι]

/- Converting data into a SStream -/
@[inline]
def zero : ι →ₛ α where
  σ := Unit; q := (); valid _ := false; ready _ := false;
  index _ := default; value := fun ⟨_, h⟩ => nomatch h;
  seek _ _ := ();

instance : Zero (ι →ₛ α) := ⟨zero⟩

abbrev ArraySet ι := Array ι

@[inline]
def ofBoolArray (is : ArraySet ι) : ι →ₛ Bool where
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

def Vec α n := { x : Array α // x.size = n }
instance [Repr α] : Repr (Vec α n) := ⟨fun x n => Repr.reprPrec x.val n⟩

def Vec.range (num : ℕ) : Vec ℕ num:= ⟨Array.range num, Array.size_range⟩
def Vec.mkEmpty {a} (num : ℕ) : Vec a 0 := ⟨Array.mkEmpty num, by simp⟩

@[inline] def Vec.map (v : Vec α n) (f : α → β) : Vec β n := ⟨v.1.map f, by have := Array.size_map f v.1; simp [*, v.2]⟩
@[inline] def Vec.push (l : Vec α n) (v : α) : Vec α (n+1) :=
  ⟨l.1.push v, by have := Array.size_push l.1 v; simp only [this, l.2]⟩
--@[inline] def SparseArray.push (l : SparseArray ι α n) (i : ι) (v : α) : SparseArray ι α (n+1) :=
--  ⟨l.is.push i, l.vs.push v⟩

@[reducible]
structure SparseArray (ι : Type) (α : Type*) where
  mk' ::
    n : Nat
    is : Vec ι n
    vs : Vec α n

abbrev SparseArrayMat a b c := SparseArray a (SparseArray b c)

@[macro_inline] def SparseArray.mk {n} : Vec ι n → Vec α n → SparseArray ι α  := SparseArray.mk' n

@[macro_inline]
def SparseArray.getI (arr : SparseArray ι α) (q : {q // decide (q < arr.n) = true}) : ι :=
  arr.is.val[q.1]'(by simpa [arr.is.prop] using q.2)
@[macro_inline]
def SparseArray.getV (arr : SparseArray ι α) (q : {q // decide (q < arr.n) = true}) : α :=
  arr.vs.val[q.1]'(by simpa [arr.vs.prop] using q.2)

@[macro_inline]
def SparseArray.mapVals {ι} {α β : Type*} (arr : SparseArray ι α) (f : α → β) : SparseArray ι β :=
  let ⟨_, is, vs⟩ := arr
  ⟨_, is, vs.map f⟩

-- benefits from macro_inline (matrix sum)
@[macro_inline]
def SparseArray.linearToStream (arr : SparseArray ι α) : ι →ₛ α where
  σ := ℕ
  q := 0
  valid q := q < arr.n
  ready _ := true
  index q := arr.getI q
  value   := fun ⟨q, _⟩ => arr.getV q
  seek q  := fun (j, r) =>
    let i := arr.getI q
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q

instance : Zero (SparseArray ι α) := ⟨0, Vec.mkEmpty 1000000, Vec.mkEmpty 1000000⟩

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
class Scalar (α : Type u)
instance : Scalar ℕ := ⟨⟩
instance : Scalar Float := ⟨⟩
instance : Scalar Bool := ⟨⟩

instance [Scalar α] : ToStream α α := ⟨id⟩

instance {α β} [ToStream α β] : ToStream  (SparseArray ι α) (ι →ₛ β) where
  stream := map ToStream.stream ∘ SparseArray.linearToStream

instance : ToStream  (ArraySet ι) (ι →ₛ Bool) where
  stream := map ToStream.stream ∘ ofBoolArray

--instance : ToStream  (Vec ι n × FloatVec n) (SStream ι Float) where
--  stream := fun (a, b) => ofFloatArray a.1 b.1 (a.property.trans b.property.symm)

@[inline] def fold (f : β → ι → α → β) (s : ι →ₛ α) : β → β := s.toStream.fold f s.q

@[inline] def toSparseArray (s : ι →ₛ α) : SparseArray ι α → SparseArray ι α :=
  s.fold (fun ⟨_, a, b⟩ i v => ⟨_, a.push i, b.push v⟩)

-- todo: we would prefer to fix the weird perf issue with SparseArray.linearToStream
abbrev F α β := Array α × Array β

@[inline] def toArrayPair (s : ι →ₛ α) : F ι α → F ι α :=
  s.fold (fun ⟨a, b⟩ i v => ⟨a.push i, b.push v⟩)

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
  eval := toSparseArray ∘ map (eval . 0)

instance [OfStream α β] [Zero β]: OfStream (ι →ₛ α) (F ι β) where
  eval := toArrayPair ∘ map (eval . 0)

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

end SStream

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
