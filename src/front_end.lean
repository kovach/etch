class NatLt (m n : ℕ) .
instance NatLt.one (n : ℕ) : NatLt 0 (n+1) := ⟨⟩
instance NatLt.trans (m n : ℕ) [h : NatLt m n] : NatLt (m+1) (n+1) := ⟨⟩

-- instance i1 : NatLt 3 2 := infer_instance -- no
instance i2 : NatLt 1 3 := infer_instance

def Gen (i : ℕ) (α : Type*) := ℕ → α
def Gen.to_fun {i α} : Gen i α → ℕ → α := id
def map : ∀ {α β : Type} (m : ℕ), (α → β) → Gen m α → Gen m β := λ _ _ m f v, f ∘ v
def map2 {α β γ : Type} (m : ℕ) : (α → β → γ) → Gen m α → Gen m β → Gen m γ := λ f a b i, f (a i) (b i)
def repl {α : Type} (m : ℕ) : α → Gen m α := λ v _, v

class Merge (α β : Type) (γ : out_param Type) :=
  (merge1 : α → β → γ)
  (merge2 : α → β → γ)
open Merge

instance Gen.Merge.one : Merge ℕ ℕ ℕ := ⟨(λ a b, a), (λ a b, b)⟩
instance Gen.Merge.succ {i : ℕ} {α β γ : Type} [Merge α β γ]
: Merge (Gen i α) (Gen i β) (Gen i γ) := ⟨map2 i Merge.merge1, map2 i Merge.merge2⟩
instance Gen.Merge.scalar_r {i : ℕ} {α : Type} [Merge α ℕ α]
: Merge (Gen i α) ℕ (Gen i α) :=
⟨ λ a b, map i (λ a, Merge.merge1 a b) a,
  λ a b, map2 i Merge.merge2 a (repl i b)⟩
instance Gen.Merge.lt {i j : ℕ} {α β γ : Type} [NatLt i j] [Merge α (Gen j β) γ]
: Merge (Gen i α) (Gen j β) (Gen i γ) :=
⟨ λ a b, map i (λ a, Merge.merge1 a b) a,
  λ a b, map2 i Merge.merge2 a (repl i b)⟩
instance Gen.Merge.scalar_l {j : ℕ} {β : Type} [Merge ℕ β β]
: Merge ℕ (Gen j β) (Gen j β) :=
⟨λ a b, map2 j merge1 (repl j a) b,
λ a b, map j (λ b, merge2 a b) b⟩
instance Gen.merge.gt {i j : ℕ} {α β γ : Type} [NatLt j i] [h : Merge (Gen i α) β γ]
: Merge (Gen i α) (Gen j β) (Gen j γ) :=
⟨λ a b, map2 j Merge.merge1 (repl j a) b,
λ a b, map j (λ b, Merge.merge2 a b) b⟩
def merge {α β γ} [Merge α β γ] : α → β → (γ × γ) := λ a b, (merge1 a b, merge2 a b)

example : Merge ℕ ℕ ℕ := infer_instance
example {i : ℕ} : Merge (Gen i ℕ) ℕ (Gen i ℕ) := infer_instance
example {i : ℕ} : Merge (Gen i ℕ) (Gen i ℕ) (Gen i ℕ) := infer_instance
example {i : ℕ} : Merge (Gen i ℕ) ℕ (Gen i ℕ) := infer_instance
example {i j : ℕ} [NatLt i j] : Merge ℕ (Gen j ℕ) (Gen j ℕ) := infer_instance
example {i j : ℕ} [NatLt i j] : Merge (Gen i ℕ) (Gen j ℕ) (Gen i (Gen j ℕ)) := infer_instance
example {i j k : ℕ} [NatLt i j] : Merge (Gen i (Gen j ℕ)) (Gen j (Gen k ℕ)) (Gen i (Gen j (Gen k ℕ))) := infer_instance

@[reducible] def i := 1
@[reducible] def j := 2
@[reducible] def k := 3
@[reducible] def V := ℕ

class has_hmul (α β : Type*) (γ : out_param Type*) :=
  (mul : α → β → γ)
infixr ` <*> ` := has_hmul.mul
instance hmul_of_Merge {α β γ : Type}  [has_mul γ] [Merge α β γ] : has_hmul α β γ := ⟨λ a b, merge1 a b * merge2 a b⟩
instance mul_Gen {i : ℕ} {α : Type} [has_mul α] : has_mul (Gen i α) := ⟨λ a b i, a.to_fun i * b.to_fun i⟩
example {i : ℕ} : has_hmul (Gen i ℕ) ℕ (Gen i ℕ) := infer_instance

--set_option trace.class_instances true
--set_option class.instance_max_depth 20

-- demo
def v1 : Gen i (Gen j V) := λ i j, i+j
def v2 : Gen j (Gen k V) := λ i j, i*j
#check merge v1 v2
#reduce (merge1 v1 v2)
#reduce (merge2 v1 v2)
-- the final result:
#reduce v1 <*> v2
  -- 72:1: λ (i i_1 i_2 : ℕ), (i.add i_1).mul (i_1.mul i_2)

def v3 : (Gen k V) := λ i, i
#reduce v1 <*> v2 <*> v3
