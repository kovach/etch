import tactic
import compile

class NatLt (m n : ℕ) := (proof : m < n) .
instance NatLt.one (n : ℕ) : NatLt 0 (n+1) := ⟨nat.succ_pos _⟩
instance NatLt.trans (m n : ℕ) [h : NatLt m n] : NatLt (m+1) (n+1) :=
⟨nat.succ_lt_succ h.proof⟩

-- instance i1 : NatLt 3 2 := infer_instance -- no
instance i2 : NatLt 1 3 := infer_instance

universes u v

class Atomic (α : Type u) .

class Rectangle (Gen : ℕ → Type* → Type*) :=
  (map {α β : Type*} (i : ℕ) : (α → β) → Gen i α → Gen i β)
  (repl {α : Type*} (i : ℕ) : α → Gen i α)

open Rectangle

class Merge (α β : Type*) (γ : out_param Type*) :=
  (merge1 : α → γ)
  (merge2 : β → γ)

open Merge

section MergeInstances
variables {Gen : ℕ → Type u → Type v} [Rectangle Gen]
variables {α β γ : Type u}

instance Gen.Merge.one {ρ} [Atomic ρ] : Merge ρ ρ ρ := ⟨id, id⟩
instance Gen.Merge.succ {i : ℕ} [Merge α β γ] : Merge (Gen i α) (Gen i β) (Gen i γ) :=
⟨map i (merge1 β), map i (merge2 α)⟩
instance Gen.Merge.scalar_r {i : ℕ} {ρ} [Atomic ρ] [Merge α ρ α] : Merge (Gen i α) ρ (Gen i α) :=
⟨id, repl i ∘ merge2 α⟩
instance Gen.Merge.lt {i j : ℕ} [NatLt i j] [Merge α (Gen j β) γ]
: Merge (Gen i α) (Gen j β) (Gen i γ) :=
⟨map i (merge1 (Gen j β)), repl i ∘ merge2 α⟩
instance Gen.Merge.scalar_l {j : ℕ} {ρ} [Atomic ρ] [Merge ρ β β] : Merge ρ (Gen j β) (Gen j β) :=
⟨repl j ∘ merge1 β, id⟩
instance Gen.merge.gt {i j : ℕ} [NatLt j i] [Merge (Gen i α) β γ] : Merge (Gen i α) (Gen j β) (Gen j γ) :=
⟨repl j ∘ merge1 β, map j (merge2 (Gen i α))⟩

def merge {α β γ} [Merge α β γ] : α → β → (γ × γ) := λ a b, (merge1 β a, merge2 α b)
end MergeInstances

def Fun (i : ℕ) (α : Type*) := ℕ → α
def Fun.to_fun {i α} : Fun i α → ℕ → α := id
def map {α β : Type} (m : ℕ) : (α → β) → Fun m α → Fun m β := λ f v, f ∘ v
def repl {α : Type} (m : ℕ) : α → Fun m α := λ v _, v
instance : Rectangle Fun :=
  { map := λ _ _, map, repl := λ _, repl }

instance nat.Atomic : Atomic ℕ := ⟨⟩

example : Merge ℕ ℕ ℕ := infer_instance
example {i : ℕ} : Merge (Fun i ℕ) ℕ (Fun i ℕ) := infer_instance
example {i : ℕ} : Merge (Fun i ℕ) (Fun i ℕ) (Fun i ℕ) := infer_instance
example {i : ℕ} : Merge (Fun i ℕ) ℕ (Fun i ℕ) := infer_instance
example {i j : ℕ} [NatLt i j] : Merge ℕ (Fun j ℕ) (Fun j ℕ) := infer_instance
example {i j : ℕ} [NatLt i j] : Merge (Fun i ℕ) (Fun j ℕ) (Fun i (Fun j ℕ)) := infer_instance
example {i j k : ℕ} [NatLt i j] : Merge (Fun i (Fun j ℕ)) (Fun j (Fun k ℕ)) (Fun i (Fun j (Fun k ℕ))) := infer_instance

@[reducible] def i := 1
@[reducible] def j := 2
@[reducible] def k := 3
@[reducible] def l := 4
@[reducible] def V := ℕ

class has_hmul (α β : Type*) (γ : out_param Type*) :=
  (mul : α → β → γ)
infixr ` <*> ` := has_hmul.mul
instance hmul_of_Merge {α β γ : Type}  [has_mul γ] [Merge α β γ] : has_hmul α β γ :=
⟨λ a b, merge1 β a * merge2 α b⟩


-- demo with functions:
instance mul_Fun {i : ℕ} {α : Type} [has_mul α] : has_mul (Fun i α) :=
⟨λ a b i, a.to_fun i * b.to_fun i⟩
example {i : ℕ} : has_hmul (Fun i ℕ) ℕ (Fun i ℕ) := infer_instance

def v1 : Fun i (Fun j V) := λ i j, i+j
def v2 : Fun j (Fun k V) := λ i j, i*j
def v3 : (Fun l V) := λ i, i
#check merge v1 v2
#reduce (merge v1 v2)
-- the final result:
#reduce v1 <*> v2
  -- 72:1: λ (i i_1 i_2 : ℕ), (i.add i_1).mul (i_1.mul i_2)
#reduce v1 <*> v2 <*> v3
  -- 81:1: λ (i i_1 i_2 i_3 : ℕ), (i.add i_1).mul ((i_1.mul i_2).mul i_3)

--set_option trace.class_instances true
--set_option class.instance_max_depth 20

-- demo with streams:
def Gen' (i : ℕ) (α : Type) := Gen E α
def Gen.idx {α} (i : ℕ) : Gen E α → Gen' i α := id

instance : Rectangle Gen' :=
-- TODO! need to use repeat instead
{ map := λ _ _ i, Gen.map, repl := λ _ m v, repeatScalar (E.ident "x") v }
instance : Atomic E := ⟨⟩
instance Gen'.has_mul {α} {i} [has_mul α] : has_mul (Gen' i α) := ⟨mulGen⟩

def g1 : Gen' i E := Gen.idx i (externGen (E.ident "x"))
def g2 : Gen' j E := (externGen (E.ident "y")).idx j
def g3 : Gen' k E := (range 1 2).to_Gen.idx k

example : Merge (Gen' i E) (Gen' j E) (Gen' i (Gen' j E)) := infer_instance
example : has_hmul (Gen' i E) (Gen' j E) (Gen' i (Gen' j E)) := infer_instance

#check g3 <*> g1 <*> g2 <*> g2
