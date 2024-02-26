import Mathlib.Data.Prod.Lex
import Mathlib.Data.String.Basic
import Init.Data.Array.Basic
import Std.Data.RBMap
import Std.Data.HashMap

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
