import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.Have

import Etch.Basic
import Etch.Op

section defs

abbrev Addr := ℕ
abbrev Val  := ℕ
abbrev Ident := ℕ
def Heap  := Addr → Option ℕ
def Store := Ident → Option Val
instance : EmptyCollection Heap := ⟨ fun _ ↦ none ⟩
instance : EmptyCollection Store := ⟨ fun _ ↦ none ⟩
instance : Membership (Ident × Val) Store where mem p s := s p.1 = some p.2
instance : Membership (ℕ × Val) Heap where mem p s := s p.1 = some p.2
instance (a b : Type) : Membership (a × b) (a → Option b) where mem p s := s p.1 = some p.2

variable [DecidableEq α]
def dom : (α → Option β) → Set α := fun h ↦ { n | ∃ v, h n = some v }

instance : Insert (Ident × Val) Store := ⟨ fun p s ↦ Function.update s p.1 p.2 ⟩
instance : Singleton (Ident × Val) Store := ⟨ fun p ↦ Function.update (∅ : Store) p.1 p.2 ⟩
instance : Insert (Addr × ℕ) Heap := ⟨ fun p s ↦ Function.update s p.1 p.2 ⟩
instance : Singleton (Addr × ℕ) Heap := ⟨ fun p ↦ Function.update (∅ : Heap) p.1 p.2 ⟩
notation a " ↦ " b => (a, b)
--notation:max h "[" x " := " y "]" => Function.update h x (some y)

@[ext]
structure TypedStore {Var} (type : Var → Type) where
  val : (v : Var) → type v

def TypedStore.update [DecidableEq V] (st : TypedStore type) (x : V) (y : type x) : TypedStore type :=
⟨ Function.update st.val x y ⟩

notation:max h "[" x " := " y "]" => TypedStore.update h x y

@[simps]
def Op.nat (n : ℕ) : Op ℕ where
  argTypes := ![]
  spec := fun _ ↦ n
  opName := "nat_lit"

inductive E {V : Type} (type : V → Type) : Type → Type 1
| call {α} (op : Op α) (args : (i : Fin op.arity) → E type (op.argTypes i)) : E type α
| var    : (v : V) → E type (type v)

def E.eval (st : TypedStore type) : {α : Type} → E type α → α
| _, var v => st.val v
| _, call op args => op.spec fun param ↦ (args param).eval st

@[simp] theorem TypedStore.val_update_ne (V : Type) (x y : V) (type : V → Type) (v : type x) (l : TypedStore type) [DecidableEq V] (h : x ≠ y) : (l[x := v]).val y = l.val y := by
  simp [val, update, Function.update]
  intro h'
  exfalso
  apply h h'.symm

@[simp] theorem TypedStore.val_update_eq (V : Type) (x : V) (type : V → Type) (v : type x) (l : TypedStore type) [DecidableEq V] : (l[x := v]).val x = v := by
  simp [update, Function.update]

example (V : Type) (x y : V) (type : V → Type) (v : type x) (l : TypedStore type) [DecidableEq V] (h : x ≠ y) : (l[x := v]).val y = l.val y := by simp [h]

#check !true
@[simp] theorem E.eval_nat : (E.call (.nat n) args).eval st = n := rfl
@[simp] theorem E.eval_neg : (E.call .neg ![arg]).eval st = !arg.eval st := rfl
-- todo: this isn't automatically used by simp?
@[simp] theorem E.asdf (a b : E type α) [Tagged α] [DecidableEq α] : E.eval l (E.call Op.eq ![a, b]) = decide (a.eval l = b.eval l) := rfl
@[simp] theorem E.eval_lt {α} [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → _) ] (a b : E type α) : (E.call .lt ![a, b]).eval st = true ↔ a.eval st < b.eval st := by simp [E.eval, Op.lt]
@[simp] theorem E.eval_lt_false {α} [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → _) ] (a b : E type α) : (E.call .lt ![a, b]).eval st = false ↔ ¬ (a.eval st < b.eval st) := by simp [E.eval, Op.lt]

inductive P {V} (type : V → Type)
--| store (x : V) (n : ℕ) (y : E type (type x))
| store' {α} (lval : E type ℕ) (rval : E type α)
| load  (lval : E type ℕ) (y : V)
| put (x : V) (e : E type (type x))
| seq (c₁ c₂ : P type) : P type
| while (c : E type Bool) (body : P type)
| skip
@[match_pattern] infixr:25 ";; " => P.seq

def ConfigSet := Heap → Store → Prop
def TypedConfigSet {V} type := Heap → @TypedStore V type → Prop

class Representable (α : Type _) where
  defines : α → Addr → Heap → Prop

class Storable (α : Type _) extends Representable α where
  store : Heap → Addr → α → Heap
  footprint : α → Addr → Set Addr
  valid (h a v) : defines v a (store h a v)
  frame (a loc v h) : a ∉ footprint v loc → (store h loc v) a = h a

def exprDefines [Representable α] : α → E type Addr → Heap → TypedStore type → Prop :=
  fun val a h s ↦ Representable.defines val (a.eval s) h
notation "⦃" addr " ↪ " val "⦄" => exprDefines val addr

instance : Storable Val where
  defines v addr h := (addr, v) ∈ h
  store   h addr v := Function.update h addr v
  footprint _ addr := { addr }
  --disjoint a₁ a₂ := a₁ ≠ a₂
  valid h a v := by simp [Membership.mem, Storable.store]
  frame a loc v h := by
    intro hf
    simp only [Membership.mem, Storable.store, Function.update]
    split
    . contradiction
    . rfl
variable
{V : Type} [DecidableEq V]
(type : V → Type)

--| storeNat (xNat : type x = ℕ)
--        (hh : (cast xNat (l.val x) + n) ∈ dom h)
--        : Q h[(cast xNat (l.val x) + n) := cast xNat $ y.eval l] l → Sem type (.store x n y) Q h l

inductive Sem  : P type → TypedConfigSet type → Heap → TypedStore type → Prop
| skip : Q h l → Sem .skip Q h l
| put  : Q h l[x := y.eval l] → Sem (.put x y) Q h l
| store {α} {rval : E type α} (hr : Storable α)
        (h1 : lval.eval l ∈ dom h)
        : Q (Storable.store h (lval.eval l) (rval.eval l)) l →
          Sem (.store' lval rval) Q h l
| load (v : type y) {lval : E type ℕ} [hr : Representable (type y)]
       (hv : ⦃lval ↪ v⦄ h l)
       : Q h l[y := v] → Sem (.load lval y) Q h l
| seq : Sem c₁ (Sem c₂ Q) h l → Sem (c₁;; c₂) Q h l
| whileDone (condFalse : x.eval l = false)
            : Q h l → Sem (.while x c) Q h l
| whileLoop (condTrue  : x.eval l = true)
            : Sem c (Sem (.while x c) Q) h l →
              Sem (.while x c) Q h l

-- todo: make type an instance variable
notation c " / " type ", " h ", " l " ⇓ " Q => Sem type c Q h l

-- todo: use, maybe?
/-
class HasUpdate (l r : outParam Type) (h : Type) where
  update : h → l → r → h
instance : HasUpdate ℕ ℕ Heap where update h l r := Function.update h l (some r)
instance : HasUpdate Ident Val Store where update h l r := Function.update h l (some r)
-/
lemma mem_dom_update (h : α → Option β) : a ∈ dom (Function.update h a (some v)) := by simp [dom]
lemma mem_update {h : α → Option β}  : (a, v) ∈ Function.update h a (some v) := by simp [Membership.mem, Function.update]
end defs

instance [Tagged α] [Add α] : Add (E type α) := ⟨ λ a b => E.call .add ![a, b] ⟩
instance [Tagged α] [Sub α] : Sub (E type α) := ⟨ λ a b => E.call .sub ![a, b] ⟩
instance [Tagged α] [Mul α] : Mul (E type α) := ⟨ λ a b => E.call .mul ![a, b] ⟩
instance [Tagged α] [OfNat α (nat_lit 1)] : OfNat (E type α) (nat_lit 1) := ⟨ E.call .one ![] ⟩
instance : OfNat (E type ℕ) n := ⟨ E.call (.nat n) ![] ⟩
abbrev zero : E type ℕ := 0
instance (V) (type : V → Type) : Coe ℕ (E type ℕ) := ⟨ fun n => E.call (.nat n) ![] ⟩

@[simp] theorem E.eval_nat' : (0 : E type ℕ).eval st = 0 := rfl

infixr:35 " ∧ₕ " => fun a b h ↦ a h ∧ b h

def List.defines [Representable α] (addr : Addr) : List α → Heap → Prop
| [] => fun _ ↦ True
| v :: vs => Representable.defines v addr ∧ₕ defines (addr + 1) vs

instance [Representable α] : Representable (List α) where defines vec := vec.defines
instance [Representable α] : Representable (Vector α n) where defines vec addr heap := ∀ i, Representable.defines (vec.nth i) (addr + i) heap

infixr:40 " << " => λ a b => E.call Op.lt ![a, b]
infixr:40 " != " => λ a b => E.call Op.neg ![E.call Op.eq ![a, b]]

namespace tests₁
inductive V₁ | x | y
deriving DecidableEq
abbrev V₁.type : V₁ → Type | x => ℕ | y => ℕ
def V₁.var : (v : V₁) → E V₁.type v.type  := E.var
open V₁

def l₁ : TypedStore type := ⟨fun |x => 2 |y => 7⟩
example : (.store' x.var y.var;; .skip) / V₁.type, {2 ↦ 0} , l₁ ⇓ (fun h _ ↦ ⦃2↪7⦄ h l₁) := by
  apply Sem.seq
  apply Sem.store
  . apply mem_dom_update
  . apply Sem.skip
    apply Storable.valid

example : (.store' (x.var + 1) (y.var * 3);; .skip) / V₁.type, {3 ↦ 0} , l₁ ⇓ (fun h _ ↦ ⦃3↪21⦄ h l₁) := by
  apply Sem.seq
  apply Sem.store
  . apply mem_dom_update
  . apply Sem.skip
    apply Storable.valid

example : (.while (x.var << (3 : E type ℕ)) (.put x (x.var + 1))) / V₁.type, {}, ⟨fun |x |y => 0⟩ ⇓ fun _ _ ↦ True := by
  apply Sem.whileLoop
  . simp only
  apply Sem.put
  apply Sem.whileLoop
  . simp only
  apply Sem.put
  apply Sem.whileLoop
  . simp only
  apply Sem.put
  apply Sem.whileDone
  . simp only
  trivial

theorem cong_locals (V) [DecidableEq V] (type : V → Type) (Q : TypedConfigSet type) (c : P type) (l₁ l₂) (hl : l₁ = l₂) : (c / type, h, l₁ ⇓ Q) ↔ (c / type, h, l₂ ⇓ Q) := by rw [hl]

example (k : ℕ) : (.while (x.var != zero) (.put x (x.var - 1))) / V₁.type, {}, ⟨fun |x => k |y => 0⟩ ⇓ fun _ l ↦ l.val x = 0 := by
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

end tests₁

section tests₂

inductive V | ctr | v | total | base deriving DecidableEq

abbrev V.type : V → Type | ctr | base => ℕ | v => ℕ | total => ℕ
def V.var : (v : V) → E V.type v.type  := E.var
def V.initial : TypedStore type := ⟨fun | ctr | v | total | base => 0⟩
open V

-- see "bug?" below
@[simp] theorem duplicate_of_succ_sub_succ_eq_sub (l : List ℕ) : Nat.succ (List.length l) - 1 = (List.length l) := by simp?

def List.sum [Zero α] [Add α] (l : List α) : α := l.foldr (f := (. + .)) 0
@[simp] theorem List.sum_cons [Zero α] [Add α] (x : α) : (x :: xs).sum = x + xs.sum := rfl

def loopSum : P type :=
.while (ctr.var != zero)
  (.load base.var v;; .put total (total.var + v.var);; .put base (base.var + 1);; .put ctr (ctr.var - 1))

example (array : List ℕ) (hlen : ctr.var.eval l = array.length) (hArr : ⦃base.var ↪ array⦄ h l)
  : loopSum / type, h, l ⇓ fun _ l' ↦ total.var.eval l' = total.var.eval l + array.sum := by
  induction array generalizing l with
  | nil =>
    --cases hlen
    apply Sem.whileDone
    . simp at hlen; rw [E.eval_neg, E.asdf, hlen]; rfl
    . trivial
  | cons x xs ih =>
    apply Sem.whileLoop
    . simp at hlen; rw [E.eval_neg, E.asdf, hlen]; simp -- fix asdf, simp should close
    . apply Sem.seq
      apply Sem.load
      . exact hArr.1
      apply Sem.seq; apply Sem.put
      apply Sem.seq; apply Sem.put
      apply Sem.put
      simp only [E.eval] at hlen
      simp [E.eval, TypedStore.val, hlen]
      rw [← add_assoc]
      set l' := l[v := x][total := TypedStore.val l total + x][base := TypedStore.val l base + 1][ctr := Nat.succ (List.length xs) - 1]
      have h : l.val total + x = l'.val total := by simp
      --change (loopSum / _, _, l' ⇓ _)
      rw [h]
      apply ih
      . simp [E.eval]
        rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] -- bug? simp doesn't use these here
      . exact hArr.2
