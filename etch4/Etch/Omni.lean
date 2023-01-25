import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Set.Basic

abbrev Val := ℕ
abbrev Ident := ℕ
def Heap := ℕ → Option ℕ
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
instance : Insert (ℕ × ℕ) Heap := ⟨ fun p s ↦ Function.update s p.1 p.2 ⟩
instance : Singleton (ℕ × ℕ) Heap := ⟨ fun p ↦ Function.update (∅ : Heap) p.1 p.2 ⟩
notation a " ↦ " b => (a, b)
notation:max h "[" x " := " y "]" => Function.update h x (some y)

inductive P
| store (x : Ident) (n : ℕ) (y : Ident)
| seq (c₁ c₂ : P) : P
| while (c : Ident) (body : P)
| skip
@[match_pattern] infixr:25 "; " => P.seq

def Post := Heap → Store → Prop

inductive Sem : P → Post → Heap → Store → Prop
| skip : Q h l → Sem .skip Q h l
| store {l : Store} {h : Heap} (hx : (x, a) ∈ l) (hh : (a + n) ∈ dom h) (hy : (y, v) ∈ l)
        (hq : Q h[a+n := v] l) : Sem (.store x n y) Q h l
| seq : Sem c₁ (Sem c₂ Q) h l → Sem (c₁; c₂) Q h l
| whileDone (condFalse : (x, 0) ∈ l) : Q h l → Sem (.while x c) Q h l
| whileLoop (condTrue  : (x, 1) ∈ l) (body : Sem c (Sem (.while x c) Q) h l) : Sem (.while x c) Q h l

notation c " / " h "," l " ⇓ " Q => Sem c Q h l

-- todo: use, maybe?
class HasUpdate (l r : outParam Type) (h : Type) where
  update : h → l → r → h
instance : HasUpdate ℕ ℕ Heap where update h l r := Function.update h l (some r)
instance : HasUpdate Ident Val Store where update h l r := Function.update h l (some r)

def x : Ident := 0
def y : Ident := 1

lemma mem_dom_update (h : α → Option β) : a ∈ dom h[a := v] := by simp [dom]
lemma mem_update {h : α → Option β} {v : β} : (a, v) ∈ h[a := v] := by simp [Membership.mem, Function.update]
lemma mem_update_of_mem {h : α → Option β} {v v' : β} (mem : (a, v) ∈ h) (neq : a ≠ a') : (a, v) ∈ h[a' := v'] := by
  simp [Membership.mem, Function.update, mem]
  split
  . contradiction
  . exact mem

example : (.store x 1 y;.skip) / {3 ↦ 0} , {x ↦ 2, y ↦ 7} ⇓ (fun h _ ↦ (3,7) ∈ h) := by
  apply Sem.seq
  apply Sem.store
  . apply mem_update
  . apply mem_dom_update
  . apply mem_update_of_mem
    . apply mem_update
    . simp only
  apply Sem.skip
  . apply mem_update

