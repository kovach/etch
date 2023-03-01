import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Set.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Pi
import Mathlib.Tactic.Set
import Mathlib.Tactic.Have
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

import Etch.Basic
import Etch.Op

def List.sum [Zero α] [Add α] (l : List α) : α := l.foldr (f := (. + .)) 0

instance : Add (Option α) := ⟨Option.merge fun a _ ↦ a⟩

section add_lemmas
variable (a b : α)
@[simp] def Option.some_add : x + none = x := by cases x<;> rfl
@[simp] def Option.add_some : none + x = x := by cases x<;> rfl
@[simp] def Option.none_add : (none : Option α) + none = none := rfl
end add_lemmas

@[simp] theorem List.sum_cons [Zero α] [Add α] (x : α) : (x :: xs).sum = x + xs.sum := rfl

section defs

abbrev Addr := ℕ
abbrev Val  := ℕ
abbrev Ident := ℕ
def Heap  := Addr → Option ℕ
instance : EmptyCollection Heap := ⟨ fun _ ↦ none ⟩
instance : Membership (ℕ × Val) Heap where mem p s := s p.1 = some p.2
instance (a b : Type) : Membership (a × b) (a → Option b) where mem p s := s p.1 = some p.2
instance : Insert (Addr × ℕ) Heap := ⟨ fun p s ↦ Function.update s p.1 p.2 ⟩
instance : Singleton (Addr × ℕ) Heap := ⟨ fun p ↦ Function.update (∅ : Heap) p.1 p.2 ⟩
notation a " ↦ " b => (a, b)

def Heap.disjoint (h₁ h₂ : Heap) : Prop := ∀ a, h₁ a = none ∨ h₂ a = none
def Heap.append (h₁ h₂ : Heap) : Heap := fun a ↦ h₁ a + h₂ a

def Function.dom [DecidableEq α] : (α → Option β) → Set α := fun h ↦ { n | (h n).isSome }
def Heap.dom (h : Heap) : Set Addr := Function.dom h
lemma mem_dom_update [DecidableEq α] (h : α → Option β) : a ∈ Function.dom (Function.update h a (some v)) := by simp [Function.dom]


@[simp] theorem disjoint_iff_dom_intersect_empty (h₁ h₂ : Heap) : h₁.disjoint h₂ ↔ h₁.dom ∩ h₂.dom = ∅ := by
  simp only [
    Heap.disjoint, Heap.dom, Function.dom,
    Set.inter_def, Set.eq_empty_iff_forall_not_mem,
    Set.mem_setOf_eq, not_and_or, not_exists, Option.not_isSome_iff_eq_none]

@[simp] theorem Heap.dom_empty : (∅ : Heap).dom = ∅ := by
  rw [Heap.dom, Function.dom]
  ext
  simp
  rfl

@[simp] def app_empty : (∅ : Heap) x = none := rfl
@[simp] theorem Heap.append_empty (h : Heap) : h.append ∅ = h := by simp [append]
@[simp] theorem Heap.empty_append (h : Heap) : (∅ : Heap).append h = h := by simp [append]

--notation:max h "[" x " := " y "]" => Function.update h x (some y)

class VariableType (Var : Type) where type : Var → Type
attribute [reducible] VariableType.type
open VariableType

@[reducible] instance [VariableType α] [VariableType β] : VariableType (α ⊕ β) where
  type | .inl a => type a | .inr b => type b

variable (V) [VariableType V]

@[ext] structure TypedStore where
  val : (v : V) → type v

variable {V} [DecidableEq V]

def TypedStore.update (st : TypedStore V) (x : V) (y : type x) : TypedStore V :=
⟨ Function.update st.val x y ⟩

notation:max h "[" x " := " y "]" => TypedStore.update h x y

infixr:35 " ∧ₕ " => fun a b h ↦ a h ∧ b h

variable (V)
inductive E : Type → Type 1
| call {α} (op : Op α) (args : (i : Fin op.arity) → E (op.argTypes i)) : E α
| var    : (v : V) → E (type v)

def EAddr := E V ℕ
def EAddr.mk {V} [VariableType V] : E V ℕ → EAddr V := id

section lift
variable {V}
variable {V'} [VariableType V'] [DecidableEq V']
def E.liftL [VariableType V'] : E V α → E (V ⊕ V') α
| .var v => .var (.inl v)
| .call op args => .call op fun a ↦ (args a).liftL

def E.liftR [VariableType V'] : E V α → E (V' ⊕ V) α
| .var v => .var (.inr v)
| .call op args => .call op fun a => (args a).liftR

instance : Coe (E V α) (E (V ⊕ V') α) where coe := E.liftL
instance : CoeTail (E V α) (E (V' ⊕ V) α) where coe := E.liftR
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
| load      (lval : E V ℕ) (y : V)
| put       (x : V) (e : E V (type x))
| seq       (c₁ c₂ : P) : P
| while     (c : E V Bool) (body : P)
| branch    (c : E V Bool) (t : P) (f : P)
| skip

-- hmm
--| emit (v : α)
--| accum (lval : V) (body : P)
variable {V}
@[match_pattern] infixr:25 ";; " => P.seq
@[match_pattern] def P.if1 : E V Bool → P V → P V := fun c x ↦ P.branch c x .skip
variable (V)

def Config := Heap × TypedStore V
--def TypedConfigSet := Config V → Prop
abbrev TypedConfigSet := Set (Config V)

instance : Inhabited Heap := ⟨ fun _ ↦ none ⟩

class AddressRepresents (α : Type _) where
  defines : Addr → α → Heap → Prop

class Storable (α : Type _) extends AddressRepresents α where
  store : Heap → Addr → α → Heap
  footprint : α → Addr → Set Addr
  valid (h a v) : defines a v (store h a v)
  frame (a loc v h) : a ∉ footprint v loc → (store h loc v) a = h a

class Represents (V) [VariableType V] (code : Type _) (α : Type _) where
  defines : code → α → TypedConfigSet V

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

-- todo
instance [AddressRepresents α] : Represents V (EAddr V) α where
  defines a val conf := AddressRepresents.defines (a.eval conf.2) val conf.1

instance [AddressRepresents α] : Represents V Addr α where
  defines a val conf := AddressRepresents.defines a val conf.1

-- todo check this
instance : Represents V (E V α) α where defines a val conf := a.eval conf.2 = val

notation (priority := high) "⦃" addr ", " val "⦄" => Represents.defines addr val


def _root_.List.defines [AddressRepresents α] (addr : Addr) : List α → Heap → Prop
| [] => fun _ ↦ True
| v :: vs => AddressRepresents.defines addr v ∧ₕ defines (addr + 1) vs

instance [AddressRepresents α] : AddressRepresents (List α) where
  defines a vec := vec.defines a

-- todo: use set more uniformly

variable {V}

def TypedConfigSet.star (Q R : TypedConfigSet V) : TypedConfigSet V :=
fun (h, st) ↦ ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.append h₂ ∧ Q (h₁, st) ∧ R (h₂, st)

--instance : Mul (TypedConfigSet V) := ⟨TypedConfigSet.star⟩
--instance : Mul (Set (Config V)) := ⟨TypedConfigSet.star⟩

-- ∗ = \ast
infixr:35 " ∗ " => TypedConfigSet.star

instance : Top (TypedConfigSet V) := ⟨ fun _ ↦ True ⟩
instance : Bot (TypedConfigSet V) := ⟨ fun _ ↦ False ⟩
def TypedConfigSet.empty : TypedConfigSet V := { conf | conf.1 = default }

def _root_.List.defines' [Represents V Addr α] (addr : Addr) : List α → Config V → Prop
| [] => TypedConfigSet.empty
| v :: vs => ⦃ addr, v ⦄ ∗ defines' (addr + 1) vs


instance : VariableType Empty := ⟨ (nomatch .) ⟩

example : [0,1].defines' 0 (({0 ↦ 0, 1 ↦ 1} : Heap), (⟨(nomatch .)⟩ : TypedStore Empty)) := by
  refine ⟨{0 ↦ 0}, {1 ↦ 1}, ?_⟩
  constructor
  intro a
  cases a
  . right
    rfl
  .left; rfl

  constructor
  . funext x
    cases x
    . rfl
    next _ _ n =>
      cases n
      . rfl
      . rfl

  constructor
  . rfl
  . refine ⟨{1 ↦ 1}, {}, ?_⟩

    constructor
    . simp
    . constructor
      . simp
      . constructor
        . rfl
        . rfl


--variable (α : Type) [Zero α] [Add α]

--inductive Sem' : P V → (Heap → TypedStore V → List α → Prop) → Heap → TypedStore V → List α → Prop
--| skip : Q h l t → Sem' .skip Q h l t
--| emit : Q h l (v :: t) → Sem' (.emit v) Q h l t
--| accum (v : α) (typeLoc : α = type loc) (h1 : Sem' c Q' h l t) (h2 : ∀ h' l' t', Q' h' l' t' → ∃ init, t' = init ++ t ∧ v = init.sum)
--        : Q h l[loc := cast typeLoc v] t → Sem' (.accum loc c) Q h l t

-- transforms a postcondition to the weakest precondition
inductive Sem  : P V → Set (Config V) → Config V → Prop -- → Set (Config V)
| skip : Q conf → Sem .skip Q conf

| put  : Q (heap, store[x := y.eval store]) → Sem (.put x y) Q (heap, store)

| store {α} {lval : E V Addr} {rval : E V α} (hr : Storable α)
        (h1 : lval.eval l ∈ h.dom)
        : Q (Storable.store h (lval.eval l) (rval.eval l), l) →
          Sem (.store lval rval) Q (h, l)

| load (v : type y) {lval : EAddr V} [hr : AddressRepresents (type y)]
       (hv : ⦃lval, v⦄ (h, l))
       : Q (h, l[y := v]) → Sem (.load lval y) Q (h, l)

| seq : Sem c₁ (Sem c₂ Q) conf → Sem (c₁;; c₂) Q conf

| whileDone (condFalse : x.eval conf.2 = false)
            : Q conf → Sem (.while x c) Q conf

| whileLoop (condTrue  : x.eval conf.2 = true)
            : Sem c (Sem (.while x c) Q) conf →
              Sem (.while x c) Q conf

| ifFalse (condFalse : x.eval conf.2 = false)
  : Sem f Q conf → Sem (.branch x _ f) Q conf

| ifTrue (condTrue : x.eval conf.2 = true)
  : Sem t Q conf → Sem (.branch x t _) Q conf

-- todo appease kyle: remove
notation c " / " h ", " l " ⇓ " Q => Sem c Q (h, l)
notation c " / " conf " ⇓ " Q => Sem c Q conf

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

inductive V₁ | x | y | z deriving DecidableEq
@[reducible] instance : VariableType V₁ := ⟨ fun | .x => ℕ | .y => ℕ | .z => String⟩
def V₁.var : (v : V₁) → E V₁ (type v)  := E.var
open V₁

def l₁ : TypedStore V₁ := ⟨fun |.x => 2 |.y => 7 | .z => "hi there"⟩

-- { P } c { Q }
-- ∀ conf, conf ∈ P → c / conf ⇓ Q
def proceeds (p : P V) (c : Config V) : Set (TypedConfigSet V) := { Q | Sem p Q c }

example : (.store x.var y.var) / {2 ↦ 0} , l₁ ⇓ ⦃2, (7 : ℕ)⦄ := by
  apply Sem.store
  . apply mem_dom_update
  . apply Storable.valid

example : (.store x.var y.var;; .skip) / {2 ↦ 0} , l₁ ⇓ ⦃2, (7 : ℕ)⦄ := by
  apply Sem.seq
  apply Sem.store
  . apply mem_dom_update
  . apply Sem.skip
    apply Storable.valid

example : (.store (x.var + 1) (y.var * 3);; .skip) / {3 ↦ 0} , l₁ ⇓ (fun p ↦ ⦃3,21⦄ p) := by
  apply Sem.seq
  apply Sem.store
  . apply mem_dom_update
  . apply Sem.skip
    apply Storable.valid

example : (P.while (x.var << (3 : E V₁ ℕ)) (.put x (x.var + 1))) /  {}, ⟨fun |z=>"" |x |y => (0 : ℕ)⟩ ⇓ ⊤ := by
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

example (k : ℕ) : (.while (x.var != zero) (.put x (x.var - 1))) /  {}, ⟨fun |z=>"" |x => k |y => (0 : ℕ)⟩ ⇓ fun ⟨_, l⟩ ↦ l.val x = (0 : ℕ) := by
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

-- todo: repeat (all_goals constructor), but only Sem
-- see matchConst
example (h l) (array : List ℕ) (hLen : ctr.var.eval l = array.length) (hArr : ⦃EAddr.mk base.var, array⦄ (h, l))
  : loopSum / h, l ⇓ fun conf' ↦ total.var.eval conf'.2 = total.var.eval l + array.sum := by
  induction array generalizing l with
  | nil =>
    apply Sem.whileDone
    . simp only [E.eval] at hLen; simp [E.eval, hLen]
    . rfl
  | cons x xs ih =>
    apply Sem.whileLoop
    . simp only [E.eval] at hLen; simp [E.eval, hLen]
    . --repeat constructor
      apply Sem.seq
      apply Sem.load
      . exact hArr.1
      --repeat constructor
      apply Sem.seq; apply Sem.put
      apply Sem.seq; apply Sem.put
      apply Sem.put
      simp only [E.eval] at hLen
      simp [E.eval, TypedStore.val, hLen]
      rw [← add_assoc]
      --convert_to loopSum / _, _ ⇓ _
      --convert ih ?_ ?_ ?_
      --simp
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

namespace tests3
open VariableType
def V := ℕ
def V.mk : ℕ → V := id
@[reducible] instance V.VariableType : VariableType V := ⟨ fun | _ => ℕ ⟩

def V.var : (v : V) → E V (type v)  := E.var
def V.initial : TypedStore V := ⟨fun | _ => (0 : ℕ)⟩
open V

end tests3

variable {V} [VariableType V] [DecidableEq V]
@[simp] def Config.append : Config V → Heap → Config V := fun ⟨h₁, st⟩ h₂ ↦ ⟨h₁.append h₂, st⟩

def TypedConfigSet.singleton (x : Heap) : TypedConfigSet V := fun ⟨h, _⟩ ↦ h = x

--theorem Sem.frame_lemma (h : c / h₁, st ⇓ Q) (hDis : h₁.disjoint h₂) : c / (h₁.append h₂), st ⇓ (Q * TypedConfigSet.singleton V h₂) := by
--theorem Sem.frame_lemma (h : c / ⟨h₁, st⟩ ⇓ Q) (hDis : h₁.disjoint h₂) : c / (h₁.append h₂), st ⇓ (Q * TypedConfigSet.singleton V h₂) := by
theorem Sem.frame_lemma (conf : Config V) (h : c / conf ⇓ Q) (hDis : conf.1.disjoint h₂)
  : c / (conf.append h₂) ⇓ Q ∗ TypedConfigSet.singleton h₂ := by
  induction h
  case _ h =>
    apply Sem.skip
    refine ⟨_, _, by assumption, rfl, h, rfl⟩
  case _ h =>
    apply Sem.put
    exact ⟨_, _, by assumption, rfl, by assumption, rfl⟩
  case _ h =>
    apply Sem.store <;> sorry
  case _ h =>
    apply Sem.load <;> sorry
  case _ h =>
    apply Sem.seq
    sorry
  case _ b a h =>
    cases b
    apply Sem.whileDone
    . simpa [*] using a
    . exact ⟨_, _, by assumption, rfl, by assumption, rfl⟩
  case _ b a _ h =>
    cases b
    apply Sem.whileLoop
    . simpa [*] using a
    sorry
  sorry
  sorry

structure IndexedStream (ι : Type) (α : Type _) where
  σ : Type
  valid : σ → Prop
  ready : σ → Prop
  next  : (st : σ) → valid st → σ
  index : (st : σ) → valid st → ι
  value : (st : σ) → ready st → α

  measure : σ → ℕ
  decreasing : ∀ (st st' : σ) (h : valid st), next st h = st' → measure st > measure st'

instance : Functor (IndexedStream ι) where map f s := { s with value := fun st v ↦ f $ s.value st v }

section wf

variable {ι : Type} {α : Type _} [DecidableEq ι] (s : IndexedStream ι α)

def IndexedStream.wf_rel : s.σ → s.σ → Prop := fun b a ↦ ∃ h, s.next a h = b
def IndexedStream.wf := InvImage.wf s.measure Nat.lt_wfRel.wf
def IndexedStream.subrel : s.wf_rel b a → s.measure b < s.measure a := by
  intro h; obtain ⟨valid, h'⟩ := h; exact s.decreasing a b valid h'
def IndexedStream.next_wf : WellFounded s.wf_rel := Subrelation.wf s.subrel s.wf

def IndexedStream.induction_on {motive : s.σ → Prop} (st : s.σ)
    (ind : (∀ st, (∀ h, motive (s.next st h)) → motive st)) : motive st :=
s.next_wf.recursion st fun st h ↦ ind st fun valid ↦ h _ ⟨valid, rfl⟩

--def IndexedStream.induction_on {motive : s.σ → Prop} (st : s.σ) (h : ∀ st, motive (s.next st) → motive st) : motive st :=
--s.induction_on' st fun st' h' ↦ h st' (h' _ rfl)
--def IndexedStream.induction (motive : s.σ → Prop) (h : ∀ st, motive (s.next st) → motive st) (st : s.σ) : motive st :=
--s.induction_on st h

end wf

structure IndexedStreamExec (ι : Type) (α : Type _) extends IndexedStream ι α where state : σ
instance : Functor (IndexedStreamExec ι) where map f s := { s with value := fun st v ↦ f $ s.value st v }

noncomputable section eval

namespace IndexedStream

variable
  {ι : Type}
  [DecidableEq ι]
  {α : Type _} [AddZeroClass α]
  (s : IndexedStream ι α)
  [∀ st : s.σ, Decidable (s.ready st)]
  [∀ st : s.σ, Decidable (s.valid st)]
--def IndexedStream.value₀ (st : s.σ)  : α :=
--if h : s.ready st then s.value st h else 0 -- match s.value st with | none => 0 | some v => v

def eval₀ (st : s.σ) (val : s.valid st) : ι → α :=
if ready : s.ready st then Function.singleton (s.index st val) (s.value st ready) else 0

def eval₀' (st : s.σ) : ι → α := if valid : s.valid st then s.eval₀ st valid else 0

def eval : s.σ → ι → α := fun st ↦
if h : s.valid st then
  have : s.measure (s.next st h) < s.measure st := (by apply s.decreasing; rfl);
  s.eval₀ st h + eval (s.next st h) else 0
termination_by _ st => s.measure st

--def eval [Add α] [Zero α] (s : IndexedStream ι α) : s.σ → ι → α := fun st ↦
--s.eval₀ st + (match h : s.next st with
--  | none => 0
--  | some st' =>
--    have : s.measure st' < s.measure st := (by apply s.decreasing; assumption);
--    s.eval st')
--termination_by _ st => s.measure st

def next' : s.σ → s.σ := fun st ↦ if h : s.valid st then s.next st h else st

theorem eval_spec (h : s.valid st) : s.eval st = s.eval₀ st h + s.eval (s.next st h) := by
  rw [eval]
  split
  . rfl
  . contradiction

@[simp] theorem eval_zero_of_invalid : ¬ s.valid st → s.eval st = 0 := by rw [eval]; intro; split; contradiction; rfl

-- todo: don't need ?
set_option pp.all true
theorem eval_spec': s.eval st = s.eval₀' st + s.eval (s.next' st) := by
  rw [eval₀', next']
  split
  . apply eval_spec
  . simp [*]

end IndexedStream
namespace IndexedStreamExec

variable
  {α : Type _}
  [AddZeroClass α]
  (s : IndexedStreamExec ι α)
  [∀ st : s.σ, Decidable (s.ready st)]
  [∀ st : s.σ, Decidable (s.valid st)]

def eval  : ι → α := by classical!; exact s.toIndexedStream.eval s.state
def succ : IndexedStreamExec ι α := { s with state := s.next' s.state }
end IndexedStreamExec

end eval

variable (V)

structure SyntacticIndexedStream (ι : Type) (α : Type _) where
  -- "σ = Config V"
  next : P V
  valid : E V Bool
  ready : E V Bool
  i : E V ι
  v : α

--structure AlignedSyntacticIndexedStream (σ : Type) (ι : Type) (α : Type _) extends SyntacticIndexedStream V ι α where
--  aligned : Config V → σ → Prop

variable {V}
-- replace aligned with map from ss.σ → Config V → s.σ ?
-- meeting notes: !! vec inside the state
-- todo swap order?
structure SyntacticIndexedStream.represents [Represents V α α']
    (ss : SyntacticIndexedStream V ι α) (s : IndexedStream ι α')
    (aligned : s.σ → Config V → Prop) : Prop where
  next : ∀ (conf : Config V) b, aligned b conf → (h : s.valid b) → ss.next / conf ⇓ aligned (s.next b h)
  i : ∀ (conf : Config V) (b : s.σ), aligned b conf → (h : s.valid b) → ss.i.eval conf.2 = s.index b h
  v : ∀ (conf : Config V) b, aligned b conf → (h : s.ready b) → ⦃ ss.v, s.value b h ⦄ conf
  valid : aligned b conf → ss.valid.eval conf.2 = s.valid b
  ready : aligned b conf → ss.ready.eval conf.2 = s.ready b

instance [Represents V α α'] : Represents V (SyntacticIndexedStream V ι α) (IndexedStreamExec ι α') where
  defines ss s conf := ∃ aligned, aligned s.state conf ∧ ss.represents s.toIndexedStream aligned

--instance [Represents V α α'] [Add α'] [Zero α'] : Represents V (SyntacticIndexedStream V ι α) (ι → α') where
--  defines ss f conf := ∃ (s : IndexedStreamExec ι α') (aligned : _), aligned s.state conf
--    ∧ ss.represents s.toIndexedStream aligned ∧ s.eval = f

abbrev UR := ℕ
@[reducible] instance : VariableType UR := ⟨ fun _ ↦ ℕ ⟩
instance : OfNat UR n := ⟨ n ⟩
open VariableType
@[reducible] instance [∀ (v : V), Inhabited (type v)] : Inhabited (TypedStore V) := ⟨⟨ fun _ ↦ default ⟩⟩

instance [Tagged α] [OfNat α (nat_lit 0)] : OfNat (E V α) (nat_lit 0) := ⟨ E.call .zero ![] ⟩
instance [Tagged α] [OfNat α (nat_lit 1)] : OfNat (E V α) (nat_lit 1) := ⟨ E.call .one ![] ⟩

#check EquivLike

-- error?:
--@[simps]
def SyntacticIndexedStream.range (v : UR) : SyntacticIndexedStream UR ℕ (E UR ℕ) where
  next := .put v (E.var v + 1)
  i := .var v
  v := .var v
  valid := 1
  ready := 1

@[simps]
def IndexedStream.range : IndexedStream ℕ ℕ where
  σ := ℕ
  next := fun s _ ↦ s.succ
  index := fun s _ ↦ s
  value := fun s _ ↦ s
  valid _ := True
  ready _ := True
  measure := sorry
  decreasing := sorry -- not true

#check @IndexedStream.ready

def foo : 1 = decide True := rfl

example (v : UR) : SyntacticIndexedStream.range v |>.represents IndexedStream.range
  (fun n conf ↦ (E.var (v : UR)).eval conf.2 = n) where
  --state conf n := (E.var (v : UR)).eval conf.2 = n
  i _ _ aligned _ := aligned
  v _ _ aligned _ := aligned
  next conf n aligned _ := by
    apply Sem.put
    simp [E.eval] at aligned
    simp [E.eval, aligned]
  -- todo
  ready _ := by simp [E.eval]
  valid _ := by simp [E.eval]

inductive IntervalVars | base | after
@[reducible] instance : VariableType IntervalVars := ⟨ fun | .base => ℕ | .after => ℕ ⟩

--@[simps]
def SyntacticIndexedStream.interval : SyntacticIndexedStream IntervalVars ℕ (E IntervalVars ℕ) where
  next := .put .base (.var .base + 1)
  i := .var .base
  v := .var .base
  valid := .var .base << .var .after
  ready := 1

@[simps] def IndexedStream.interval : IndexedStream ℕ ℕ where
  --next := .put v (E.var v + 1)
  σ := ℕ × ℕ
  next st _ := st.map Nat.succ id
  index st _ := st.fst
  value st _ := st.fst
  measure := fun ⟨a, b⟩ ↦ b - a
  decreasing := by intros m n h eq; cases eq; apply Nat.sub_succ_lt_self m.snd m.fst h
  valid st := st.1 < st.2
  ready _  := True

variable (V)

class Eval (α : Type _) (β : Type _) where eval : α → β
instance : Eval a a := ⟨ id ⟩
noncomputable instance (α) [AddZeroClass α] [Eval α' α] : Eval (IndexedStreamExec ι α') (ι → α) := ⟨ IndexedStreamExec.eval ∘ ((Eval.eval : α' → α)  <$> .) ⟩

open Eval

structure StreamLValue' (ι : Type) (α : Type _) extends SyntacticIndexedStream V ι α where
  value  : α
  commit : E V ι → P V

-- maybe generalize spec for insert? -- modify : (ι → α') → (ι → α') → (ι → α')
structure StreamLValue (ι : Type) [DecidableEq ι] (α α' γ : Type _) [AddZeroClass γ] [Represents V α α'] [Eval α' γ] extends StreamLValue' V ι α where
  --reset : P V
  --reset_spec (v : ι → α') (v' : α') (e : E V ι) :
  --  ⦃ value, v' ⦄ conf → reset / conf ⇓ ⦃ value, (0 : α') ⦄

  spec' (v v'' : IndexedStreamExec ι α') (v' : α') (e : E V ι) :
    (⦃ toSyntacticIndexedStream, v ⦄ ∗ ⦃ value, v' ⦄) conf →
      have new : ι → γ := Function.singleton (e.eval conf.2) (Eval.eval v');
      commit e / conf ⇓ fun conf' ↦ ⦃ toSyntacticIndexedStream, v'' ⦄ conf' ∧ Eval.eval v'' = Eval.eval v + new

class Compile' (α β : Type _) where
  compile : α → β → P V
class Compile (α β : Type _) (α' β' γ : outParam (Type _)) [Represents V α α'] [Represents V β β'] [Eval α' γ] [Eval β' γ] extends Compile' V α β where
  sound (v v' : α') (r' : β') : (⦃ l, v ⦄ ∗ ⦃ r, r'⦄) conf → compile l r / conf ⇓ fun conf' ↦ ⦃ l, v' ⦄ conf' ∧ Eval.eval v' = (Eval.eval r' : γ)

inductive Local (α : Type) | mk deriving DecidableEq
@[reducible] instance : VariableType (Local α) := ⟨ fun | .mk => α ⟩

variable {V' : Type} [VariableType V']
variable {V}

def Config.projL : Config (V ⊕ V') → Config V := fun ⟨h, st⟩ ↦ ⟨h, ⟨fun v ↦ st.val (.inl v)⟩⟩
def TypedStore.projL : TypedStore (V ⊕ V') → TypedStore V := fun st ↦ ⟨fun v ↦ st.val (.inl v)⟩

instance [VariableType V'] [r : Represents V α β] : Represents (V ⊕ V') α β where
  defines x y := fun conf ↦ r.defines x y conf.projL

--@[simp] theorem Config.lift_eval (e : E V α) (conf : Config (V ⊕ V')) : e.liftL.eval conf.2 = e.eval conf.projL.2 := by
--  cases conf
--  induction e <;> (dsimp at *; simp only [E.eval, Config.projL, *])
@[simp] theorem Store.lift_eval (e : E V α) (st : TypedStore (V ⊕ V')) : e.liftL.eval st = e.eval st.projL := by
  induction e <;> (dsimp at *; simp only [E.eval, TypedStore.projL, *])


open Compile' (compile)

variable {ι : Type} [DecidableEq ι]

/-
verifying the compiler
  - lval datastructures satisfy insert_spec
  - stream combinators on SyntacticIndexedStream match up with IndexedStream
  - Compile.sound holds for the main instance
-/

section loop
variable
  (ι : Type) {α α' β β' : Type _}
  [DecidableEq ι]
  [Represents V α α']
  [AddZeroClass γ]
  [Eval α' γ]
  (lval : StreamLValue V ι α α' γ)
  (rval : SyntacticIndexedStream V ι β)
  [Represents V β α']
  [Compile V α β α' α' γ]

def loop_prog : P V :=
  .while rval.valid $
    (.if1 rval.ready
      (compile lval.value rval.v;; lval.commit rval.i));;
    rval.next

instance [Represents V α α'] [Represents V (SyntacticIndexedStream V ι α) β] : Represents V (StreamLValue V ι α α' γ) β := ⟨ fun l r ↦ Represents.defines l.toSyntacticIndexedStream r ⟩

open Classical

def sem : P V → Set (Config V) → Set (Config V) := fun c Q ↦ Sem c Q

-- hmm
theorem post_weaken' {P Q : Set (Config V)} (h : P ⊆ Q) : sem c P ⊆ sem c Q := by
  induction c generalizing P Q
  case seq h1 h2 =>
    intro conf s; constructor; apply h1; apply h2; exact h; cases s; assumption
  . intro conf s; cases s; constructor <;> aesop
  . intro conf s; cases s; constructor; assumption; aesop
  . intro conf s; cases s; constructor <;> aesop
  case _ h1 =>
    intro conf s;
    cases s;
    . constructor <;> aesop;
    . apply Sem.whileLoop; assumption; apply h1; rotate_left 3; sorry; sorry; sorry
  . intro conf s; cases s; constructor <;> aesop; sorry

theorem post_weaken {P Q : Set (Config V)} (s : c / conf ⇓ P) (h : P ⊆ Q) : c / conf ⇓ Q := by
  --cases s; all_goals (constructor <;> aesop)
  induction s generalizing Q
  . constructor; aesop
  . constructor; aesop
  . constructor <;> aesop
  . constructor <;> aesop
  . constructor; sorry
  . constructor <;> aesop
  . apply Sem.whileLoop <;> aesop; sorry
  . constructor <;> aesop
  . constructor <;> aesop; sorry; sorry

  --apply a_ih
-- e.g.
theorem represents_next (r' : IndexedStreamExec ι α') :
⦃ rval, r' ⦄ conf → .if1 rval.valid rval.next / conf ⇓ ⦃ rval, r'.succ ⦄ := by
  obtain ⟨s, st⟩ := r'
  intro h₀
  cases h₀
  next aligned prop =>
  obtain h|h :=  (_root_.em $ s.valid st)
  . dsimp at *
    apply Sem.ifTrue
    . have := prop.2.valid prop.1
      rw [this]
      assumption
    . apply post_weaken;
      . apply prop.2.next _ _ prop.1 h
      . intro x h1; simp [IndexedStreamExec.succ, IndexedStream.next']; split;
        . refine ⟨aligned, h1, prop.2⟩;
        . contradiction
  . apply Sem.ifFalse
    . simpa [h] using prop.2.valid prop.1
    . simp [IndexedStreamExec.succ, IndexedStream.next']; split;
      . contradiction
      . apply Sem.skip; exact ⟨aligned, prop⟩

theorem loop_correct (r' : IndexedStreamExec ι α') (v v' : IndexedStreamExec ι α') :
    (⦃ lval, v ⦄ ∗ ⦃ rval, r'⦄) conf →
    loop_prog _ lval rval / conf ⇓ fun conf' ↦ ⦃ lval, v' ⦄ conf' ∧ eval v' = (eval r' : ι → γ):= by
  --revert r'
  induction r'.state using IndexedStream.induction_on  --generalizing r'
  next st ih =>
  --cases h
    intro h
    obtain ⟨ r', rel, aligned, hEquiv, hEval ⟩ := h
  --cases h2
    sorry

-- todo: need reset before loop
instance : Compile V (StreamLValue V ι α α' γ) (SyntacticIndexedStream V ι β) (IndexedStreamExec ι α') (IndexedStreamExec ι α') (ι → γ) where
  compile l r := loop_prog _ l r
  sound := by intros; apply loop_correct; assumption

end loop

#exit

-- *x += y
instance : Compile (V ⊕ Local ℕ) (E V ℕ) (E V ℕ) ℕ ℕ ℕ where
  compile l r :=
    let temp := Sum.inr Local.mk
    .load l temp;; .store l (.var temp + r.liftL)
  sound := by
    intros _ l v r v' conf hConf
    apply Sem.seq
    --letI : AddressRepresents (type (@Sum.inr V (Local ℕ) Local.mk))  := by
    --  dsimp [type];
    --  dsimp [instVariableTypeSum]
    --  sorry
    apply Sem.load
    next a b =>
      convert hConf
      simp [Represents.defines, AddressRepresents.defines]
      sorry
    . apply Sem.store
      -- dom
      . sorry
      . sorry
      . sorry
    . sorry
/-

port stream induction

rewrite AddressRepresents List to be "small" footprint
how to use these ∗ hypotheses

cancelled:
define list that a stream represents (WF)
use this in ↪ hypothesis for loop
  induct over list
  ! stream may take n steps to produce head


-/

