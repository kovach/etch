import Etch.StreamFusion.Stream
import Etch.StreamFusion.Multiply
import Etch.Util.ExpressionTree

namespace Etch.Verification.SStream
open Etch.ExpressionTree

def LabeledIndex (n : Nat) (ι : Type) := ι
def LabeledIndex.mk (n : Nat) (i : ι) : LabeledIndex n ι := i

-- todo: decide on a nicer notation
notation n:30 "~" i:30 => LabeledIndex n i
--notation n:30 "//" i:30 => LabeledIndex n i
@[reducible] instance : HDiv ℕ Type Type := ⟨LabeledIndex⟩
--notation n:30 "/" i:30 => LabeledIndex n i
--macro_rules | `($label / $type)   => `(LabeledIndex $label $type)

variable (i : ℕ) (ι : Type)
@[inline] instance [LinearOrder ι] : LinearOrder (i~ι) := by change LinearOrder ι; exact inferInstance
@[inline] instance [Inhabited ι] : Inhabited (i~ι) := by change Inhabited ι; exact inferInstance

instance : TypeHasIndex (i~ι →ₛ β) i ι β where
instance : TypeHasIndex (i~ι → β) i ι β where

class Label (σ : List ℕ) (α : Type*) (β : outParam Type*) where
  label : α → β
instance [Scalar α]     : Label [] α α := ⟨id⟩
instance [Label is α β] : Label (i::is) (ι →ₛ α) (i~ι →ₛ β) := ⟨map (Label.label is)⟩
instance [Label is α β] : Label (i::is) (ι → α) (i~ι → β) := ⟨(Label.label is ∘ .)⟩

#check 0~Nat →ₛ 1~Nat →ₛ Nat

def idx (x : α) (shape : List ℕ) [Label shape α β] := Label.label shape x


/--
Class to put decidable propositions into the typeclass inference.
It has a single instance, and it's like `[When p]` is satisfied when the `decide` tactic would prove `p`.
There are some differences, because `decide` refuses to prove propositions with free variables or metavariables.
-/
class When (p : Prop) [Decidable p] : Prop where
  isTrue : p

instance : @When p (.isTrue h) := @When.mk p (.isTrue h) h

abbrev NatLt (m n : ℕ) := When (m < n)

-- this doesn't seem ideal
class MapIndex (i : ℕ) (α β α' : Type*) (β' : outParam Type*) where
  map : (α → β) → α' → β'

instance (I : Type) : MapIndex i α β (i~I →ₛ α) (i~I →ₛ β)where
  map f s := s.map f

instance (J : Type) [NatLt j i] [MapIndex i a b a' b'] : MapIndex i a b (j~J →ₛ a') (j~J →ₛ b') where
  map f s := s.map (MapIndex.map i f)

#synth MapIndex 0 Nat Nat (0~Nat →ₛ Nat) (0~Nat →ₛ Nat)

notation f " $[" i "] " t => MapIndex.map i f t

class Contract (σ : ℕ) (α : Type*) (β : outParam Type*) where
  contract : α → β
instance : Contract i (i~ι →ₛ α) (Unit →ₛ α) := ⟨fun s => contract s⟩
instance [Contract j α β] [NatLt i j] : Contract j (i~ι →ₛ α) (i~ι →ₛ β) := ⟨map (Contract.contract j)⟩
instance [Contract j α β]  : Contract j (Unit →ₛ α) (Unit →ₛ β) := ⟨map (Contract.contract j)⟩

--notation "Σ " j ", " t => Contract.contract j t
--notation "Σ " j ": " t => Contract.contract j t

syntax "Σ"  term,* ":" term : term
macro_rules
| `(Σ $is,* : $t) => do
  let t ← is.getElems.foldlM (init := (t : Lean.TSyntax `term)) fun acc i => `(Contract.contract $i $acc)
  pure t

class Expand (σ : List (ℕ × Type)) (α : Type*) (β : outParam Type*) where
  expand : α → β

section
variable {α β : Type*}
instance expBase                                                              : Expand [] α α                                 := ⟨id⟩
instance expScalar {ι : Type}   {i : ℕ} [Scalar α]  [Expand σ α β]            : Expand ((i,ι) :: σ) α           (i~ι → β)    := ⟨fun v _ => Expand.expand σ v⟩
instance expLt     {ι : Type} {i j : ℕ} [NatLt i j] [Expand σ (j~ι' →ₛ α) β] : Expand ((i,ι) :: σ) (j~ι' →ₛ α) (i~ι → β)   := ⟨fun v _ => Expand.expand σ v⟩
instance expGt     {ι : Type} {i j : ℕ} [NatLt j i] [Expand ((i,ι) :: σ) α β] : Expand ((i,ι) :: σ) (j~ι' →ₛ α) (j~ι' →ₛ β) := ⟨fun v => map (Expand.expand ((i,ι)::σ)) v⟩
instance expEq     {ι : Type}   {i : ℕ}             [Expand σ α β]            : Expand ((i,ι) :: σ) (i~ι  →ₛ α) (i~ι →ₛ β)  := ⟨fun v => map (Expand.expand σ) v⟩

instance expLtFun  {ι : Type} {i j : ℕ} [NatLt i j] [Expand σ (j~ι' → α) β] : Expand ((i,ι) :: σ) (j~ι' → α) (i~ι → β) := ⟨fun v _ => Expand.expand σ v⟩
instance expGtFun  {ι : Type} {i j : ℕ} [NatLt j i] [Expand ((i,ι) :: σ) α β] : Expand ((i,ι) :: σ) (j~ι' → α) (j~ι' → β)   := ⟨fun v => Expand.expand ((i,ι)::σ) ∘ v⟩
instance expEqFun  {ι : Type}   {i : ℕ}             [Expand σ α β]            : Expand ((i,ι) :: σ) (i~ι  → α)  (i~ι → β)   := ⟨fun v => (Expand.expand σ) ∘ v⟩
end

-- Ignoring `base` for now. It should be used for a coercion.
instance [Expand σ α β] : EnsureBroadcast σ base α β where
  broadcast := Expand.expand σ

instance [LinearOrder ι] [HMul α β γ] : HMul (i~ι →ₛ α) (i~ι →ₛ β) (i~ι →ₛ γ) := ⟨mul⟩
instance [HMul α β γ] : HMul (i~ι → α) (i~ι →ₛ β) (i~ι →ₛ γ) where
  hMul f x := { x with value := fun q => f (x.index q) * x.value q}
instance [HMul α β γ] : HMul (i~ι →ₛ α) (i~ι → β) (i~ι →ₛ γ) where
  hMul x f := { x with value := fun q => x.value q * f (x.index q) }
instance [HMul α β γ] : HMul (i~ι → α) (i~ι → β) (i~ι → γ) where
  hMul f g x := f x * g x

notation s:80 " ⇑ " x:80 => Expand.expand s x

@[inline]
def streamify (S : List (ℕ × Type)) (s : List ℕ) [ToStream α β] [Label s β γ] [Expand S γ δ] : α → δ :=
  Expand.expand S ∘ Label.label s (β := γ) ∘ ToStream.stream

@[inline]
def streamifyFun (S : List (ℕ × Type)) (s : List ℕ) [h : Label s β γ] [Expand S γ δ] : β → δ :=
  Expand.expand S ∘ Label.label s (β := γ)

syntax:max term noWs "(" term,* ")" : term
macro_rules
| `($t($ss,*)) => `(Label.label [$ss,*] $t)

#check ∀ (x : ℕ) (y : ℕ), True
/-- This instance helps `a(i,j)` notation work even if `a` isn't yet a stream that's labelable. -/
instance (priority := low) [ToStream α α'] [Label is α' β] : Label is α β := ⟨Label.label is ∘ ToStream.stream⟩

instance [OfStream (ι →ₛ α) β] : OfStream (i~ι →ₛ α) β := ⟨fun x : ι →ₛ α => OfStream.eval x⟩

-- kmill: the CoeTail instances below might be addressing this comment, at least approximately.
-- TODO(dsk):
-- maybe we can get `Coe` and binop to cast all subexpressions to the right shape? see:
--   abbrev LS' (_is : List (ℕ×Type)) (β : Type*) := β
--   instance [Expand is α β] : Coe α (LS' is β) := ⟨Expand.expand is⟩
-- but, requires: class Expand (σ : List (ℕ × Type)) (α : outParam Type*) (β : Type*)
-- which breaks it; there is ambiguity between expEqFun and expLt
--   (and same change to label)
-- ideas?

-- may also want:
--  abbrev LS (_is : List ℕ) (β : Type*) := β
--  instance coeLS [Label is α β] : Coe α (LS is β) := ⟨Label.label is⟩


-- Note(kmill): superceded by ExpressionTree
-- instance (priority := low) : CoeTail β (i/I → β) := ⟨fun v _ => v⟩
-- instance [CoeTail β β'] : CoeTail (i//I →ₛ β) (i//I →ₛ β') := ⟨map CoeTail.coe⟩
-- instance [CoeTail β β'] : CoeTail (i//I → β) (i//I → β') := ⟨(CoeTail.coe ∘ ·)⟩
-- instance [NatLt j i] [CoeTail (i//I →ₛ β) β'] : CoeTail (i//I →ₛ β) (j//J → β') := ⟨fun v _ => CoeTail.coe v⟩
-- instance [NatLt j i] [CoeTail (i//I → β) β'] : CoeTail (i//I → β) (j//J → β') := ⟨fun v _ => CoeTail.coe v⟩



-- Note(kmill): it's not clear how to write the HMul instances...

-- inductive IndexedFn (i : ℕ) (I : Type) (α : Type u) : Type (max u 1)
--   | fn (f : i//I → α)
--   | stream (s : i//I →ₛ α)

-- syntax:25 "(" ident "//" term ")" " =>ₛ " term:25 : term
-- macro_rules | `(($id:ident//$I) =>ₛ $α) => `(IndexedFn $id $I $α)

-- class DefEq' {x : α} {y : outParam α} where
--   eq : x = y
-- instance : @DefEq' _ x x := ⟨rfl⟩
-- abbrev DefEq (x y : α) := @DefEq' _ x y

-- class ToIndexedFn (α : Type u) (β : outParam <| Type v) :=
--   coe : α → β

-- instance (priority := low) : ToIndexedFn α α := ⟨fun x => x⟩
-- instance [ToIndexedFn α α'] : ToIndexedFn (i//I → α) ((i//I) =>ₛ α') := ⟨fun f => .fn (fun x => ToIndexedFn.coe (f x))⟩
-- instance [ToIndexedFn α α'] : ToIndexedFn (i//I →ₛ α) ((i//I) =>ₛ α') := ⟨fun s => .stream (map ToIndexedFn.coe s)⟩

--instance [HMul α β γ] : HMul ((i//I) =>ₛ α) ((j//J) =>ₛ β)

open Lean Elab PrettyPrinter Delaborator SubExpr in
def delabLabeledIndexFor (i : Nat) (name : Name) : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.getAppNumArgs = 2
  guard <| (← Meta.whnf e.appFn!.appArg!).natLit? = i
  let i ← withAppFn <| withAppArg do
    withTheReader SubExpr (fun s => {s with expr := .const name []}) do
      delab
  let ty ← withAppArg <| delab
  `($i~$ty)

syntax indexGroupDef := ident "~" ident " := " term
/--
Defines a collection of type abbreviations along with index variables that correspond to their positions.
-/
syntax "def_index_group " group(sepByIndentSemicolon(ppGroup(indexGroupDef))) : command

open Lean in
macro_rules
  | `(command| def_index_group $ds*) => do
    let cmds ← ds.getElems.mapIdxM fun i d => match d with
      | `(indexGroupDef| $idx~$id := $ty) => do
        let idxName := Lean.mkIdent idx.getId
        let delabName := Lean.mkIdent <| idx.getId ++ `delab
        let i := Lean.quote (i : Nat)
        `(abbrev $idx : Nat := $i
          @[delab $delabName] def $delabName := delabLabeledIndexFor $i ``$idxName
          abbrev $id := $ty)
      | _ => Macro.throwUnsupported
    return Lean.mkNullNode cmds

end Etch.Verification.SStream

-- not working
syntax "!_aux(" num ", " num ")" : term
syntax "!(" num ")" : term
open Lean in
macro_rules
| `(!_aux($count, $limit)) => do
  let count' := count.getNat + 1
  if count' < limit.getNat
  then `((($count : Nat), !_aux($(quote count'), $limit)))
  else `($count)
| `(!($limit)) => `(!_aux($(quote 0), $limit))
