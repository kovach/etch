import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.Have

import Etch.Basic
import Etch.Op

def Option.add : Option α → Option α → Option α
| some x, none => some x
| none, some x => some x
| none, none => none
| some x, some _ => some x

instance : Add (Option α) := ⟨Option.add⟩

section add_lemmas
variable (a b : α)
@[simp] def Option.some_add : x + none = x := by cases x<;> rfl
@[simp] def Option.add_some : none + x = x := by cases x<;> rfl
@[simp] def Option.none_add : (none : Option α) + none = none := rfl
end add_lemmas

def List.sum [Zero α] [Add α] (l : List α) : α := l.foldr (f := (. + .)) 0
@[simp] theorem List.sum_cons [Zero α] [Add α] (x : α) : (x :: xs).sum = x + xs.sum := rfl

section defs

abbrev Addr := ℕ
abbrev Val  := ℕ
abbrev Ident := ℕ
def Heap  := Addr → Option ℕ
instance : EmptyCollection Heap := ⟨ fun _ ↦ none ⟩
instance : Membership (ℕ × Val) Heap where mem p s := s p.1 = some p.2
instance (a b : Type) : Membership (a × b) (a → Option b) where mem p s := s p.1 = some p.2

def Heap.disjoint (h₁ h₂ : Heap) : Prop := ∀ a, h₁ a = none ∨ h₂ a = none
def Heap.append (h₁ h₂ : Heap) : Heap := fun a ↦ h₁ a |>.add (h₂ a)

def dom [DecidableEq α] : (α → Option β) → Set α := fun h ↦ { n | ∃ v, h n = some v }
lemma mem_dom_update [DecidableEq α] (h : α → Option β) : a ∈ dom (Function.update h a (some v)) := by simp [dom]

instance : Insert (Addr × ℕ) Heap := ⟨ fun p s ↦ Function.update s p.1 p.2 ⟩
instance : Singleton (Addr × ℕ) Heap := ⟨ fun p ↦ Function.update (∅ : Heap) p.1 p.2 ⟩
notation a " ↦ " b => (a, b)
--notation:max h "[" x " := " y "]" => Function.update h x (some y)

class VariableType (Var : Type) where type : Var → Type
attribute [reducible] VariableType.type
open VariableType

instance [VariableType α] [VariableType β] : VariableType (α ⊕ β) where
  type
  | .inl a => type a
  | .inr b => type b

variable (V) [VariableType V] [DecidableEq V]

@[ext]
structure TypedStore where
  val : (v : V) → type v

variable {V}

def TypedStore.update (st : TypedStore V) (x : V) (y : type x) : TypedStore V :=
⟨ Function.update st.val x y ⟩

notation:max h "[" x " := " y "]" => TypedStore.update h x y

infixr:35 " ∧ₕ " => fun a b h ↦ a h ∧ b h

-- todo move
@[simps, reducible]
def Op.nat (n : ℕ) : Op ℕ where
  argTypes := ![]
  spec := fun _ ↦ n
  opName := "nat_lit"

variable (V)
inductive E : Type → Type 1
| call {α} (op : Op α) (args : (i : Fin op.arity) → E (op.argTypes i)) : E α
| var    : (v : V) → E (type v)

section lift
variable {V}
variable {V'} [VariableType V'] [DecidableEq V']
def E.liftL [VariableType V'] : (E V α) → E (V ⊕ V') α
| .var v => .var (.inl v)
| .call op args => .call op fun a => (args a).liftL

def E.liftR [VariableType V'] : (E V α) → E (V' ⊕ V) α
| .var v => .var (.inr v)
| .call op args => .call op fun a => (args a).liftR

instance : Coe (E V α) (E (V ⊕ V') α) where coe := E.liftL
instance : Coe (E V α) (E (V' ⊕ V) α) where coe := E.liftR
example [Tagged α] [Add α] (a : E V α) (b : E V' α) : E (V ⊕ V') α := .call Op.add ![a, b]

end lift


variable {V}
def E.eval (st : TypedStore V) : {α : Type} → E V α → α
| _, var v => st.val v
| _, call op args => op.spec fun param ↦ (args param).eval st

@[simp] theorem TypedStore.val_update_ne (x y : V) (v : type x) (l : TypedStore V) (h : x ≠ y) : (l[x := v]).val y = l.val y := by
  simp [val, update, Function.update]
  intro h'
  exfalso
  apply h h'.symm

@[simp] theorem TypedStore.val_update_eq (x : V) (v : type x) (l : TypedStore V) [DecidableEq V] : (l[x := v]).val x = v := by
  simp [update, Function.update]

example (x y : V)  (v : type x) (l : TypedStore V) [DecidableEq V] (h : x ≠ y) : (l[x := v]).val y = l.val y := by simp [h]

variable (st : TypedStore V)

@[simp] theorem E.eval_nat : (E.call (.nat n) args).eval st = n := rfl
@[simp] theorem E.eval_neg : (E.call .neg ![arg]).eval st = !arg.eval st := rfl -- by simp [E.eval]
-- todo: this isn't automatically used by simp?
@[simp] theorem E.asdf (a b : E V α) [Tagged α] [DecidableEq α] : E.eval l (E.call Op.eq ![a, b]) = decide (a.eval l = b.eval l) := rfl
@[simp] theorem E.eval_lt {α} [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → _) ] (a b : E V α) : (E.call .lt ![a, b]).eval st = true ↔ a.eval st < b.eval st := by simp [E.eval, Op.lt]
@[simp] theorem E.eval_lt_false {α} [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → _) ] (a b : E V α) : (E.call .lt ![a, b]).eval st = false ↔ ¬ (a.eval st < b.eval st) := by simp [E.eval, Op.lt]

variable (V)
inductive P
| store {α} (lval : E V ℕ) (rval : E V α)
| load  (lval : E V ℕ) (y : V)
| put (x : V) (e : E V (type x))
| seq (c₁ c₂ : P) : P
| while (c : E V Bool) (body : P)
| skip
-- hmm
| emit (v : α)
| accum (lval : V) (body : P)
@[match_pattern] infixr:25 ";; " => P.seq

def Config := Heap × TypedStore V
def TypedConfigSet := Heap → TypedStore V → Prop

class AddressRepresents (α : Type _) where
  defines : Addr → α → Heap → Prop

class Storable (α : Type _) extends AddressRepresents α where
  store : Heap → Addr → α → Heap
  footprint : α → Addr → Set Addr
  valid (h a v) : defines a v (store h a v)
  frame (a loc v h) : a ∉ footprint v loc → (store h loc v) a = h a

class Represents (V) [VariableType V] (code : Type _) (α : Type _) where
  defines : code → α → Heap → TypedStore V → Prop

instance : Storable Val where
  defines addr v h := (addr, v) ∈ h
  store   h addr v := Function.update h addr v
  footprint _ addr := { addr }
  valid h a v := by simp [Membership.mem, Storable.store]
  frame a loc v h := by
    intro hf
    simp only [Membership.mem, Storable.store, Function.update]
    split
    . contradiction
    . rfl

instance [AddressRepresents α] : Represents V (E V Addr) α where
  defines a val h s := AddressRepresents.defines (a.eval s) val h

instance [AddressRepresents α] : Represents V Addr α where
  defines a val h _ := AddressRepresents.defines a val h

notation "⦃" addr " ↪ " val "⦄" => Represents.defines addr val

def List.defines [AddressRepresents α] (addr : Addr) : List α → Heap → Prop
| [] => fun _ ↦ True
| v :: vs => AddressRepresents.defines addr v ∧ₕ defines (addr + 1) vs

instance [AddressRepresents α] : AddressRepresents (List α) where defines a vec := vec.defines a
--instance [Representable α] : Representable (Vector α n) where defines vec addr heap := ∀ i, Representable.defines (vec.nth i) (addr + i) heap

--structure S (ι : Type _) (α : Type _) where
--  σ     : Type
--  next  : σ → E V ι → E V Bool → P V -- skip s i : if current index < i, must advance; may advance to first index ≥ i.
--  succ  : σ → E V ι → P V -- succ s i : if current index ≤ i, must advance; may advance to first index > i.
--  value : σ → α
--  ready : σ → E V Bool
--  index : σ → E V ι
--  valid : σ → E V Bool
--  init  : Name → P V × σ
--structure SExec (ι : Type _) (α : Type _) where
--  stream : S V ι α
--  state : stream.σ
--local infixr:25 " →se " => fun a b ↦ SExec V a b
--local infixr:25 " →ₛ " => fun a b ↦ S V a b

--structure Stream.defines [Zero β] [Add β]  (s : ι →se α) (val : β) (h : Heap) (st : TypedStore V) : Prop where
--  h1 : (s.stream.valid s.state).eval st = false → val = 0
--  h2 : (s.stream.valid s.state).eval st = true →

variable {V}

def TypedConfigSet.star (Q R : TypedConfigSet V) : TypedConfigSet V :=
fun h st ↦ ∃ h₁ h₂, h = h₁.append h₂ ∧ Q h₁ st ∧ R h₂ st

instance : Mul (TypedConfigSet V) := ⟨TypedConfigSet.star⟩

variable (α : Type) [Zero α] [Add α]

inductive Sem' : P V → (Heap → TypedStore V → List α → Prop) → Heap → TypedStore V → List α → Prop
| skip : Q h l t → Sem' .skip Q h l t
| emit : Q h l (v :: t) → Sem' (.emit v) Q h l t
| accum (v : α) (typeLoc : α = type loc) (h1 : Sem' c Q' h l t) (h2 : ∀ h' l' t', Q' h' l' t' → ∃ init, t' = init ++ t ∧ v = init.sum)
        : Q h l[loc := cast typeLoc v] t → Sem' (.accum loc c) Q h l t

inductive Sem  : P V → TypedConfigSet V → Heap → TypedStore V → Prop
| skip : Q h l → Sem .skip Q h l
| put  : Q h l[x := y.eval l] → Sem (.put x y) Q h l
| store {α} {rval : E V α} (hr : Storable α)
        (h1 : lval.eval l ∈ dom h)
        : Q (Storable.store h (lval.eval l) (rval.eval l)) l →
          Sem (.store lval rval) Q h l
| load (v : type y) {lval : E V ℕ} [hr : AddressRepresents (type y)]
       (hv : ⦃lval ↪ v⦄ h l)
       : Q h l[y := v] → Sem (.load lval y) Q h l
| seq : Sem c₁ (Sem c₂ Q) h l → Sem (c₁;; c₂) Q h l
| whileDone (condFalse : x.eval l = false)
            : Q h l → Sem (.while x c) Q h l
| whileLoop (condTrue  : x.eval l = true)
            : Sem c (Sem (.while x c) Q) h l →
              Sem (.while x c) Q h l

notation c " / " h ", " l " ⇓ " Q => Sem c Q h l

end defs

section instances
variable {V} [VariableType V] [DecidableEq V]
open VariableType

instance [Tagged α] [Add α] : Add (E V α) := ⟨ λ a b => E.call .add ![a, b] ⟩
instance [Tagged α] [Sub α] : Sub (E V α) := ⟨ λ a b => E.call .sub ![a, b] ⟩
instance [Tagged α] [Mul α] : Mul (E V α) := ⟨ λ a b => E.call .mul ![a, b] ⟩
instance [Tagged α] [OfNat α (nat_lit 1)] : OfNat (E V α) (nat_lit 1) := ⟨ E.call .one ![] ⟩
instance : OfNat (E V ℕ) n := ⟨ E.call (.nat n) ![] ⟩
abbrev zero : E V ℕ := 0
instance : Coe ℕ (E V ℕ) := ⟨ fun n => E.call (.nat n) ![] ⟩

@[simp] theorem E.eval_nat' : E.eval st (0 : E V ℕ) = 0 := rfl

infixr:40 " << " => λ a b => E.call Op.lt ![a, b]
infixr:40 " != " => λ a b => E.call Op.neg ![E.call Op.eq ![a, b]]

namespace example_tests

inductive V₁ | x | y deriving DecidableEq
@[reducible] instance : VariableType V₁ := ⟨ fun | .x => ℕ | .y => ℕ ⟩
def V₁.var : (v : V₁) → E V₁ (type v)  := E.var
open V₁

def l₁ : TypedStore V₁ := ⟨fun |.x => 2 |.y => 7⟩

example : (.store x.var y.var;; .skip) / {2 ↦ 0} , l₁ ⇓ (fun h _ ↦ ⦃2↪(7 : Val)⦄ h l₁) := by
  apply Sem.seq
  apply Sem.store
  . apply mem_dom_update
  . apply Sem.skip
    apply Storable.valid

example : (.store (x.var + 1) (y.var * 3);; .skip) / {3 ↦ 0} , l₁ ⇓ (fun h _ ↦ ⦃3↪21⦄ h l₁) := by
  apply Sem.seq
  apply Sem.store
  . apply mem_dom_update
  . apply Sem.skip
    apply Storable.valid

example : (P.while (x.var << (3 : E V₁ ℕ)) (.put x (x.var + 1))) /  {}, ⟨fun |x |y => (0 : ℕ)⟩ ⇓ fun _ _ ↦ True := by
  apply Sem.whileLoop
  . simp only
  repeat (
    apply Sem.put
    apply Sem.whileLoop
    . simp only
  )
  apply Sem.put
  apply Sem.whileDone
  . simp only
  trivial

lemma cong_locals (Q : TypedConfigSet V) (c : P V) (l₁ l₂) (hl : l₁ = l₂) : (c / h, l₁ ⇓ Q) ↔ (c / h, l₂ ⇓ Q) := by rw [hl]
example (k : ℕ) : (.while (x.var != zero) (.put x (x.var - 1))) /  {}, ⟨fun |x => k |y => (0 : ℕ)⟩ ⇓ fun _ l ↦ l.val x = (0 : ℕ) := by
  induction k
  . apply Sem.whileDone
    . simp
    . trivial
  case succ n ih =>
    apply Sem.whileLoop
    . rfl
    . apply Sem.put
      rw [cong_locals]
      . apply ih
      . ext z; cases z <;> rfl

end example_tests
end instances

namespace tests₂

open VariableType

inductive V | ctr | v | total | base deriving DecidableEq
@[reducible] instance V.VariableType : VariableType V := ⟨ fun | ctr => ℕ | base => ℕ | v => ℕ | total => ℕ ⟩

def V.var : (v : V) → E V (type v)  := E.var
def V.initial : TypedStore V := ⟨fun | ctr | v | total | base => (0 : ℕ)⟩
open V

-- see "bug?" below
@[simp] theorem duplicate_of_succ_sub_succ_eq_sub (l : List ℕ) : Nat.succ (List.length l) - 1 = (List.length l) := by simp

def loopSum : P V :=
.while (ctr.var != 0)
  (.load base.var v;; .put total (total.var + v.var);; .put base (base.var + 1);; .put ctr (ctr.var - 1))

example (l) (array : List ℕ) (hLen : ctr.var.eval l = array.length) (hArr : ⦃base.var ↪ array⦄ h l)
  : loopSum / h, l ⇓ fun _ l' ↦ total.var.eval l' = total.var.eval l + array.sum := by
  induction array generalizing l with
  | nil =>
    apply Sem.whileDone
    . simp [E.eval] at hLen; simp [E.eval, hLen]
    . trivial
  | cons x xs ih =>
    apply Sem.whileLoop
    . simp [E.eval] at hLen; simp [E.eval, hLen]
    . apply Sem.seq
      apply Sem.load
      . exact hArr.1
      apply Sem.seq; apply Sem.put
      apply Sem.seq; apply Sem.put
      apply Sem.put
      simp only [E.eval] at hLen
      simp [E.eval, TypedStore.val, hLen]
      rw [← add_assoc]
      generalize h : _ = l'
      convert_to loopSum / _, l' ⇓ _
      --set l' := l[v := x][total := TypedStore.val l total + x][base := TypedStore.val l base + 1][ctr := Nat.succ (List.length xs) - 1]
      have h' : l.val total + x = l'.val total := by simp [h.symm]
      rw [h']
      apply ih
      . simp [E.eval, ← h]
        rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] -- bug? simp doesn't use these here
      . rw [← h]; exact hArr.2

end tests₂

namespace tests₃
open VariableType
def V := ℕ
def V.mk : ℕ → V := id
@[reducible] instance V.VariableType : VariableType V := ⟨ fun | _ => ℕ ⟩

def V.var : (v : V) → E V (type v)  := E.var
def V.initial : TypedStore V := ⟨fun | _ => (0 : ℕ)⟩
open V

end tests₃


structure IndexedStream (ι : Type) (α : Type _) where
  σ : Type
  next : σ → σ
  i : σ → ι
  v : σ → α

structure SyntacticIndexedStream (V : Type) [VariableType V] (ι : Type) (α : Type _) where
  --σ : Type
  --V : Type
  --vt : VariableType V
  next : P V
  i : E V ι
  v : E V α

variable {V} [VariableType V] [DecidableEq V]

variable (V)
def TypedConfigSet.singleton (x : Heap) : TypedConfigSet V := fun h _ ↦ h = x

theorem Sem.frame_lemma (h : c / h₁, st ⇓ Q) (hDis : h₁.disjoint h₂) : c / (h₁.append h₂), st ⇓ (Q * TypedConfigSet.singleton V h₂) := by
  induction h
  case _ h =>
    apply Sem.skip
    exact ⟨_, _, rfl, h, rfl⟩
  case _ h =>
    apply Sem.put
    exact ⟨_, _, rfl, by assumption, rfl⟩
  case _ h =>
    apply Sem.store
    exact ⟨_, _, rfl, by assumption, rfl⟩
  case _ h =>
    apply Sem.load
    exact ⟨_, _, rfl, by assumption, rfl⟩
  case _ h =>
    apply Sem.seq
    exact ⟨_, _, rfl, by assumption, rfl⟩
  case _ h =>
    apply Sem.whileDone
    . simp [*]
    . exact ⟨_, _, rfl, by assumption, rfl⟩
  case _ h =>
    apply Sem.whileLoop
    . simp [*]
    exact ⟨_, _, rfl, by assumption, rfl⟩


  sorry

variable {V}
--structure streamRepresents (ss : SyntacticIndexedStream V ι α) (s : IndexedStream ι α) (h : Heap) (st : TypedStore V) : Type where
structure streamRepresents (ss : SyntacticIndexedStream V ι α) (s : IndexedStream ι α)  : Type where
  state : Config V → s.σ → Prop
  next : ∀ (conf : Config V) b, state conf b → ss.next / conf.1, conf.2 ⇓ (fun h' st' ↦ state (h', st') (s.next b))
  i : ∀ (conf : Config V) b, state conf b → ss.i.eval conf.2 = s.i b
  v : ∀ (conf : Config V) b, state conf b → ss.v.eval conf.2 = s.v b

abbrev UR := ℕ
@[reducible] instance : VariableType UR := ⟨ fun _ ↦ ℕ ⟩
instance : OfNat UR n := ⟨ n ⟩
open VariableType
@[reducible] instance [∀ (v : V), Inhabited (type v)] : Inhabited (TypedStore V) := ⟨⟨ fun _ ↦ default ⟩⟩

@[simps]
def range : SyntacticIndexedStream UR ℕ ℕ where
  next := .put 0 (E.var (0 : UR) + (E.call (.nat 1) ![] : E UR ℕ))
  i := .var 0
  v := .var 0

@[simps]
def S.range : IndexedStream ℕ ℕ where
  next := Nat.succ
  i := id
  v := id

example : streamRepresents range S.range where
  state := fun conf n ↦ (E.var (0 : UR)).eval conf.2 = n
  i _ _ rel := rel
  v _ _ rel := rel
  next conf n rel := by
    apply Sem.put
    simp [E.eval] at rel
    simp [E.eval, rel]
