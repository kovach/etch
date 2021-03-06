import tactic
import compile_fast

class NatLt (m n : ℕ) := (proof : m < n)
instance NatLt.one (n : ℕ) : NatLt 0 (n+1) := ⟨nat.succ_pos _⟩
instance NatLt.trans (m n : ℕ) [h : NatLt m n] : NatLt (m+1) (n+1) :=
⟨nat.succ_lt_succ h.proof⟩

-- instance i1 : NatLt 3 2 := infer_instance -- no
instance i2 : NatLt 1 3 := infer_instance

universes u v

class Atomic (α : Type u) .

class Rectangle (Gen : ℕ → Type* → Type*) :=
  (map {α β : Type*} (i : ℕ) : (α → β) → Gen i α → Gen i β)
  (repl {α : Type*}  (i : ℕ) : α → Gen i α)

open Rectangle

class Merge (α β : Type*) (γ : out_param Type*) :=
  (merge1 : α → γ)
  (merge2 : β → γ)

open Merge

class NestedMap (α β γ δ : Type*) :=
  (map : (β → γ) → α → δ)

section Instances
variables
{Gen : ℕ → Type u → Type v}
{View : ℕ → Type u → Type v}
[Rectangle Gen]
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


instance Gen.NestedMap.Eq {i : ℕ} {α β} : NestedMap (Gen i α) α β (Gen i β) := ⟨Rectangle.map i⟩
instance Gen.NestedMap.Lt {i j : ℕ} {α β γ δ} [NatLt i j] [NestedMap α β γ δ] : NestedMap (Gen i α) β γ (Gen i δ) :=
⟨λ f, Rectangle.map i (NestedMap.map f)⟩

end Instances

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

instance hmul_of_Merge {α β γ : Type}  [has_mul γ] [Merge α β γ] : has_hmul α β γ :=
⟨λ a b, merge1 β a * merge2 α b⟩

-- demo with functions:
instance Fun.mul {i : ℕ} {α : Type} [has_mul α] : has_mul (Fun i α) :=
⟨λ a b i, a.to_fun i * b.to_fun i⟩
example {i : ℕ} : has_hmul (Fun i ℕ) ℕ (Fun i ℕ) := infer_instance

def v1 : Fun i (Fun j V) := λ i j, i+j
def v2 : Fun j (Fun k V) := λ i j, i*j
def v3 : (Fun l V) := λ i, i

--set_option trace.class_instances true
--set_option class.instance_max_depth 20
--set_option pp.all true

section Streams

def Ind (i : ℕ) := E
inductive Stream (n : ℕ) (α : Type)
| view (v : View (Ind n) α) : Stream
| gen  (g : G (Ind n) α)    : Stream

instance {n} : functor (Stream n) :=
{ map := λ _ _ f g, match g with
  | Stream.view v := Stream.view { v with value := f ∘ v.value }
  | Stream.gen  g := Stream.gen  { g with value := f g.value }
  end }

instance : Rectangle Stream :=
{ map  := λ _ _ _, functor.map,
  repl := λ _ m v, Stream.view ⟨λ _, v⟩ }
instance : Atomic E := ⟨⟩

def foo1 : Merge (Stream i E) (Stream j E) (Stream i (Stream j E)) := infer_instance

variables {ι α β γ : Type}
(n : ℕ)

instance G.Ind.hmul {i : ℕ} [has_hmul α β γ] : has_hmul (G (Ind i) α) (G (Ind i) β) (G (Ind i) γ) := ⟨G.mul⟩

instance [inhabited α] : inhabited (Stream n α) := ⟨Stream.view ⟨λ _, default⟩⟩
instance [inhabited ι] [inhabited α] : inhabited (G ι α) := ⟨G.empty⟩

-- instance Stream.has_mul {α} {i} [has_mul α] : has_mul (StreamGen' i α) := ⟨StreamGen.mul⟩
instance Stream.has_mul {γ} {i} [inhabited γ] [has_mul γ] : has_mul (Stream i γ) := ⟨λ a b,
match a, b with
| Stream.view a, Stream.view b := arbitrary _ -- Stream.view $ a⋆b
| Stream.gen a, Stream.view b := Stream.gen $ a⋆b
| Stream.view a, Stream.gen b := Stream.gen $ a⋆b
| Stream.gen a, Stream.gen b := Stream.gen $ a⋆b
end⟩

variables (a : Stream i E) (b : Stream j E)

example : has_mul (Stream i (Stream j E)) := infer_instance
example : Stream i (Stream j E) := a ⋆ b

instance : has_coe (G E E) (Stream n E) := ⟨Stream.gen⟩
instance coe_stream [has_coe α β] : has_coe (G E α) (Stream n β) := ⟨Stream.gen ∘ functor.map has_coe.coe⟩

class of_stream (α β : Type) := (coe : α → β)
instance base.of_stream : of_stream α α := ⟨id⟩
def Stream.to_g {n} [inhabited α] : (Stream n α) → (G E α) := λ s, match s with
| Stream.view _ := arbitrary _
| Stream.gen a := a
end

instance [inhabited β] [of_stream α β] : of_stream (Stream n α) (G E β) := ⟨λ s, match s with
| Stream.view _ := arbitrary _
| Stream.gen a := of_stream.coe <$> a
end⟩

def Stream.of [of_stream α β] : α → β := of_stream.coe

infixr ` →ₛ `:24 := Stream

--def Stream.to_stream {n} [of_stream α β] : Stream n α → G E β := of_stream.coe

-- instance s_level.eval [of_stream γ β] [Ev α (G E β)] : Ev α (Stream i γ) :=
-- ⟨ λ l r, exec l (of_stream.coe r : G E β) ⟩
-- instance stream.level.eval' (n : ℕ) [Ev α (G E β)] : Ev α (Stream n β) :=
-- ⟨ λ l r, exec l $ r.to_g _ ⟩


class Sum (n : ℕ) (α : Type) (β : out_param Type) := (sum : α → β)
instance sum_eq (n : ℕ) [inhabited α] : Sum n (Stream n α) (G unit α) := ⟨G.contract ∘ Stream.to_g⟩
instance sum_lt (m n : ℕ) [NatLt n m] [Sum m α β] : Sum m (Stream n α) (Stream n β) := ⟨functor.map $ Sum.sum m⟩

abbreviation R := E

prefix ` Σ ` := Sum.sum

def mmul1'  := Σ i $ Σ j $ Σ k $ (A : i →ₛ j →ₛ E) ⋆ (B : j →ₛ k →ₛ E)
def mmul2'  := Σ i $ Σ j $ Σ k $ (A : i →ₛ k →ₛ E) ⋆ (B : j →ₛ k →ₛ E)
def ttv'    := Σ i $ Σ j $ Σ k $ (C : i →ₛ j →ₛ k →ₛ R) ⋆ (v : k →ₛ R)
def ttm'    := Σ i $ Σ j $ Σ k $ Σ l $ (C : i →ₛ j →ₛ l →ₛ R) ⋆ (A : k →ₛ l →ₛ R)
def mttkrp' := Σ i $ Σ j $ Σ k $ Σ l $ (C : i →ₛ j →ₛ k →ₛ R) ⋆ (A : j →ₛ l →ₛ R) ⋆ (B : k →ₛ l →ₛ R)
def inner3' := Σ i $ Σ j $ Σ k $ (C : i →ₛ j →ₛ k →ₛ R) ⋆ (D : i →ₛ j →ₛ k →ₛ R)

example : Sum i (Stream i E) (G unit E) := infer_instance
example : Sum j (Stream i (Stream j E)) (Stream i (G unit E)) := infer_instance

def inner : Stream i (Stream j (G unit E)) :=
  Sum.sum k $ (A : i →ₛ k →ₛ E) ⋆ (B : j →ₛ k →ₛ E)

def eg_mmul1 :=
  [me $ exec out mmul1'] ++
  [ta $ Prog.inline_code "taco_ijk_sum();"]

def eg_mmul2 :=
  [me $ exec out mmul2'] ++
  [ta $ Prog.inline_code "mmul2_compute();"]

def eg_ttv :=
  [me $ exec out $ G.contract $ View.to_gen "foo" 30 $ constView E $ ttv'] ++
  [ta $ exec out $ G.contract $ View.to_gen "foo" 30 $ constView E $ E.inline_code "ttv_compute();"]

def eg_ttm :=
  [me $ exec out ttm'] ++
  [ta $ Prog.inline_code "ttm_compute();"]

def eg_mttkrp :=
  [me $ exec out mttkrp'] ++
  [ta $ Prog.inline_code "mttkrp_compute();"]

def eg_inner3 :=
  [me $ exec out inner3'] ++
  [ta $ Prog.inline_code "inner3_compute();"]

def eg_inner3' :=
  [me $ exec out $ G.contract $ View.to_gen "foo" 200 $ constView E $ inner3'] ++
  [ta $ exec out $ G.contract $ View.to_gen "foo" 200 $ constView E $ E.inline_code "inner3_compute();"]

def compile_with_load (v : list Prog) := compile $ load ++ v

def tests :=
  /- 1 -/ eg_mmul1 ++
  /- 2 -/ eg_mmul2 ++
  /- 3 -/ eg_ttv ++
  /- 4 -/ eg_ttm ++
  /- 5 -/ eg_mttkrp ++
  /- 6 -/ eg_inner3'

def run_comparisons := compile_with_load tests

-- main comparison script:
-- #eval run_comparisons

end Streams
