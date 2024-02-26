import Mathlib.Init.Order.Defs
import Mathlib.Data.Nat.Basic
import Std.Data.RBMap

import Etch.StreamFusion.Basic
import Etch.StreamFusion.Stream

open Std (RBMap RBNode RBColor)

instance : Inhabited (RBNode α) := ⟨.nil⟩

-- for reference
#check Std.RBNode.lowerBound?
/-- `upperBound? cut` retrieves the smallest entry greater than or equal to `cut`, if it exists. -/
@[specialize] def _root_.Std.RBNode.upperBoundP? {α} (cut : α → Ordering) : RBNode α → Option α → Option α
  | .nil,          lb => lb
  | .node _ a y b, lb =>
    match cut y with
    | .gt => upperBoundP? cut a (some y)
    | .lt => upperBoundP? cut b lb
    | .eq => some y

-- for reference, RBNode: | node (c : RBColor) (l : RBNode α) (v : α) (r : RBNode α)
inductive Visitor (α : Type)
| done
| r (c : RBColor) (right : RBNode α) (value : α) (k : Visitor α)
| l (c : RBColor) (left : RBNode α)  (value : α) (k : Visitor α)

inductive Direction | up | down
  deriving Inhabited, Repr

variable (f : α → α) [Ord ι]

def Std.RBNode.look [Inhabited α] (t : RBNode α) : α :=
  match t with
  | .nil => default
  | .node _ _ v _ => v

namespace Etch.Verification
namespace RB

inductive From | no | r | l deriving Inhabited, Repr

structure Data (ι : Type) (α : Type*) (d : Type) where
  key : ι
  value : α
  label : d
deriving Repr

abbrev DirectedTree ι [Ord ι] (d : Type) (α : Type u) := RBNode (Data ι α d)
instance : Inhabited (DirectedTree ι l α) := ⟨.nil⟩

abbrev TreeMap     ι [Ord ι] (α : Type*) := DirectedTree ι From α
abbrev TreeContext ι [Ord ι] (α : Type*) := DirectedTree ι From α

-- TODO: fix this
--instance [Zero β] [Ord ι] : Modifiable ι β (TreeMap ι β) where
--  update := RBMap.modifyD

def _root_.Std.RBNode.pp [ToString x] : RBNode x → String
| .nil => "."
| .node _ l v r => s!"({l.pp} {toString v} {r.pp})"

instance : ToString (Data Nat Unit From) := ⟨fun x => s!"{x.key}"⟩
instance [ToString (Data ι α d)] : Repr (RBNode (Data ι α d)) := ⟨fun x _ => x.pp⟩

structure Cursor (ι : Type) [LinearOrder ι] (α : Type*) where
  t : TreeMap ι α
  k : TreeContext ι α
  d : Direction
  --last : ι
deriving Inhabited, Repr

variable {ι : Type} [LinearOrder ι] {α : Type u}
[Inhabited ι]

@[inline] def Cursor.valid (now : Cursor ι α) : Bool :=
  match now.t, now.k, now.d with
  | .nil, .nil, _ => false -- empty tree is done
  | _, .nil, .up => false
  | _, _, _ => true

@[inline] def Cursor.seek (now : Cursor ι α) (target : ι) (ready : Bool) : Cursor ι α :=
  let {t, k, d} := now
  match d with
  | .down =>
    match t with
    | .node c l ⟨i, x, _⟩ r =>
      match Ord.compare i target with
      | .eq => {now with t := l, k := .node c r ⟨i, x, .r⟩ k , d := .up} -- going straight `up` is an optimization
      | .gt => {now with t := l, k := .node c r ⟨i, x, .r⟩ k}
      | .lt => {now with t := r, k := .node c t ⟨i, x, .l⟩ k}
    | .nil   => {now with d := .up} -- .seek target ready
  | .up =>
    match k with
    | .nil => now
    | .node c r ⟨i, x, .r⟩ k =>
      let op : ι → ι → Bool  := if ready then (.<.) else (.≤.)
      if op target i then
        {now with t := t, k := .node c r ⟨i, x, .r⟩ k} --now
      else
        {now with t := r, k := .node c t ⟨i, x, .l⟩ k, d := .down}
    | .node c l ⟨i, x, .l⟩ k => { now with t := .node c l ⟨i, x, .no⟩ t, k}
    | .node .. => now -- impossible

theorem RBNode.min_isSome (h : t = RBNode.node c l d r) : t.min.isSome := by
  revert h
  induction t generalizing c l d r with
  | nil => intro h; cases h
  | node c l d r hl _ =>
    rintro ⟨_⟩
    cases h' : l with
    | nil => rfl | node _ _ _ _ => unfold RBNode.min; rw [← h']; exact hl h'

theorem RBNode.max_isSome (h : t = RBNode.node c l d r) : t.max.isSome := by
  revert h
  induction t generalizing c l d r with
  | nil => intro h; cases h;
  | node c _ d r _ hr =>
    rintro ⟨_⟩
    cases h' : r with
    | nil => rfl | node _ _ _ _ => unfold RBNode.max; rw [← h']; exact hr h';

@[inline] def Cursor.index [Zero ι] (now : Cursor ι α) (h : now.valid) : ι :=
  match now.d with
  | .up =>
    match now.t, h₂ : now.k with
    | t, .node _ _ ⟨i,_,_⟩ _ => max (t.max.map (·.key) |>.getD i) i
    | _, .nil => now.t.max |>.get (by
      cases ht : now.t <;> cases hd : now.d <;> unfold valid at h <;> simp [*] at h
      rw [← ht]
      apply RBNode.max_isSome ht) |>.key
  | .down =>
    match h₁ : now.t with
    | .node _ l _ _  => now.t.min.get (by apply RBNode.min_isSome h₁) |>.key
    | .nil =>
      match h₂ : now.k with
      | .node _ _ ⟨i,_,_⟩ _  => i
      | .nil => by exfalso; unfold valid at h; rw [h₁, h₂] at h; cases now.d <;> simp? at h;

@[inline] def Cursor.ready (now : Cursor ι α) : Bool :=
  match now.k, now.d with
  | .node _ _ ⟨_, _, .r⟩ _, .up => true
  | _, _ => false

@[inline] def Cursor.value [Zero ι] (now : Cursor ι α) (h : now.ready) : α :=
  match hk : now.k, hd : now.d, h with
  | .node _ _ ⟨_, v, .r⟩ _, .up, _ => v
  | .node _ _ ⟨_, v, .l⟩ _, .up, _ => by simp only [hk, hd, ready] at h
  | .node _ _ ⟨_, v, .no⟩ _, .up, _ => by simp only [hk, hd, ready] at h
  | .nil, .up, _ => by simp only [hk, hd, ready] at h
  | _, .down, _ => by simp only [hk, hd, ready] at h

def TreeMap.ofList (l : List (ι × α)) : TreeMap ι α :=
  RBMap.ofList l Ord.compare |>.1.map fun (i,v) => ⟨i, v, .no⟩

@[inline] def cursorInit [Zero ι] (m : TreeMap ι α) : Cursor ι α := ⟨m, .nil, .down⟩

def DirectedTree.isNil : DirectedTree ι From α → Bool
| .nil => true
| _ => false

def iterate {α} (f : α → α) (s0 : α) : ℕ → List α :=
  let rec go x acc : ℕ → List α
          | 0 => acc.reverse
          | n+1 => go (f x) (x :: acc) n
  go s0 []

def eg1 (n : Nat) :=
  let tree :=
    let l : List (Nat × Unit) := [2,3,4,5,6,7].map (fun i => (i*2, ()))
    let c := cursorInit (TreeMap.ofList l)
    c
  iterate (fun c => Cursor.seek c (c.index sorry) (c.ready)) tree n |>.map
  fun c => (c.t.pp, c.k.pp, c.d, c.index sorry, c.valid)

-- #eval eg1 25

open ToStream
open SStream

@[inline]
def TreeMap.toStream [Zero ι] {α : Type} (t : TreeMap ι α) : ι →ₛ α where
  σ := Cursor ι α
  q := cursorInit t
  valid := Cursor.valid
  ready := fun q => Cursor.ready q.1
  index := fun q => Cursor.index q.1 q.2
  value := fun q => Cursor.value q.1.1 q.2
  seek := fun q i => Cursor.seek q.1 i.1 i.2

instance {α β} [Zero ι] [ToStream α β] : ToStream (TreeMap ι α) (ι →ₛ β) where
  stream := map stream ∘ TreeMap.toStream

end Etch.Verification.RB
