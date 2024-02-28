import Mathlib.Data.Prod.Lex
import Mathlib.Data.String.Basic
import Init.Data.Array.Basic
import Std.Data.RBMap
import Std.Data.HashMap
import Etch.Util.Labels

open Std (RBMap RBSet HashMap)

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

instance [Repr a] [Repr b] [Hashable a] [BEq a] : Repr (HashMap a b) where
  reprPrec x n := "h#" ++ reprPrec (x.toList) n

end Std

-- Canonical data structure names
--abbrev Map a [Ord a] b := RBMap a b Ord.compare
--abbrev HMap a [BEq a] [Hashable a] b := HashMap a b
abbrev ArraySet ι := Array ι
abbrev DenseArray (_n : Nat) α := Array α

instance [Zero α] : Zero (DenseArray n α) := ⟨(Array.range n).map fun _ => 0⟩

instance [EmptyCollection α] : Zero α := ⟨{}⟩

class Modifiable (k v : outParam Type*) (m : Type*) where
  update : m → k → (v → v) → m

class Readable (k v : outParam Type*) (m : Type*) where
  get : m → k → v  -- should choose a default "zero" value when key does not exist

instance [BEq α] [Hashable α] [Zero β] : Modifiable α β (HashMap α β) where
  update := HashMap.modifyD'

instance [BEq α] [Hashable α] [Zero β] : Readable α β (HashMap α β) where
  get := (HashMap.findD · · 0)

instance [Zero β] : Modifiable α β (RBMap α β h) where
  update := RBMap.modifyD

instance [Zero β] : Readable α β (RBMap α β h) where
  get := (RBMap.findD · · 0)

def Vec α n := { x : Array α // x.size = n }
instance [Repr α] : Repr (Vec α n) := ⟨fun x n => Repr.reprPrec x.val n⟩

def Vec.range (num : ℕ) : Vec ℕ num:= ⟨Array.range num, Array.size_range⟩
def Vec.mkEmpty {a} (num : ℕ) : Vec a 0 := ⟨Array.mkEmpty num, by simp⟩

@[inline] def Vec.map (v : Vec α n) (f : α → β) : Vec β n := ⟨v.1.map f, by have := Array.size_map f v.1; simp [*, v.2]⟩
@[inline] def Vec.push (l : Vec α n) (v : α) : Vec α (n+1) :=
  ⟨l.1.push v, by have := Array.size_push l.1 v; simp only [this, l.2]⟩

@[inline] def Vec.get (v : Vec α n) (i : ℕ) (h : i < n) : α :=
  v.val[i]'(by simpa [v.prop])

@[reducible]
structure SparseArray (ι : Type) (α : Type*) where
  mk' ::
    n : Nat
    is : Vec ι n
    vs : Vec α n
deriving Repr

abbrev SparseArrayMat a b c := SparseArray a (SparseArray b c)

@[macro_inline] def SparseArray.mk {n} : Vec ι n → Vec α n → SparseArray ι α  := SparseArray.mk' n

@[macro_inline]
def SparseArray.getI (arr : SparseArray ι α) (q : {q // decide (q < arr.n) = true}) : ι :=
  arr.is.get q.1 (by simpa using q.2) -- below proof didn't work ??
@[macro_inline]
def SparseArray.getV (arr : SparseArray ι α) (q : {q // decide (q < arr.n) = true}) : α :=
  arr.vs.val[q.1]'(by simpa only [arr.vs.prop, decide_eq_true_eq] using q.2)

@[macro_inline]
def SparseArray.mapVals {ι} {α β : Type*} (arr : SparseArray ι α) (f : α → β) : SparseArray ι β :=
  let ⟨_, is, vs⟩ := arr
  ⟨_, is, vs.map f⟩

@[inline] def SparseArray.push (l : SparseArray ι α) (i : ι) (v : α) : SparseArray ι α :=
  ⟨_, l.is.push i, l.vs.push v⟩

instance : Zero (SparseArray ι α) := ⟨0, Vec.mkEmpty 1000000, Vec.mkEmpty 1000000⟩

-- todo: we would prefer to fix the weird perf issue with SparseArray.linearToStream
abbrev F α β := Array α × Array β

class Scalar (α : Type u)
instance : Scalar ℕ := ⟨⟩
instance : Scalar Float := ⟨⟩
instance : Scalar Bool := ⟨⟩

/--
Boxing values is a mechanism to keep a stream from being considered to be a stream during elaboration.
-/
structure Boxed (α : Type u) where
  box ::
  unbox : α

notation "□←" => Boxed.box
notation "←□" => Boxed.unbox

instance : Scalar (Boxed α) := ⟨⟩
instance [Zero α] : Zero (Boxed α) := ⟨□← 0⟩
instance [One α] : One (Boxed α) := ⟨□← 1⟩
instance [Add α] : Add (Boxed α) := ⟨fun a b => □← (←□ a + ←□ b)⟩
instance [Sub α] : Sub (Boxed α) := ⟨fun a b => □← (←□ a - ←□ b)⟩
instance [Mul α] : Mul (Boxed α) := ⟨fun a b => □← (←□ a * ←□ b)⟩

namespace Etch.Verification

def LabeledIndex (_n : LabelIdx) (ι : Type) := ι
def LabeledIndex.mk (_n : LabelIdx) (i : ι) : LabeledIndex n ι := i

class Label (σ : List LabelIdx) (α : Type*) (β : outParam Type*) where
  label : α → β

class Contract (σ : LabelIdx) (α : Type*) (β : outParam Type*) where
  contract : α → β

class Expand (σ : List (LabelIdx × Type)) (α : Type*) (β : outParam Type*) where
  expand : α → β

class MapIndex (i : LabelIdx) (α β α' : Type*) (β' : outParam Type*) where
  map : (α → β) → α' → β'

class MapAtIndex (i : LabelIdx) (α β α' : Type*) (β' : outParam Type*) where
  map : (α → β) → α' → β'

instance : Zero Bool := ⟨false⟩
instance : One Bool := ⟨true⟩
instance : Add Bool := ⟨or⟩
instance : Mul Bool := ⟨and⟩

/--
Class to put decidable propositions into the typeclass inference.
It has a single instance, and it's like `[When p]` is satisfied when the `decide` tactic would prove `p`.
There are some differences, because `decide` refuses to prove propositions with free variables or metavariables.
-/
class When (p : Prop) [Decidable p] : Prop where
  isTrue : p

instance : @When p (.isTrue h) := @When.mk p (.isTrue h) h

abbrev NatLt (m n : ℕ) := When (m < n)
abbrev IdxLt (m n : LabelIdx) := When (m < n)

end Etch.Verification
