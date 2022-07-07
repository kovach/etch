import tactic
import compile_fast

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
  (repl {α : Type*}  (i : ℕ) : α → Gen i α)

open Rectangle

class Merge (α β : Type*) (γ : Type*) :=
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
#check merge v1 v2
#reduce (merge v1 v2)
-- the final result:
-- #reduce v1 <*> v2
--   -- 72:1: λ (i i_1 i_2 : ℕ), (i.add i_1).mul (i_1.mul i_2)
-- #reduce v1 <*> v2 <*> v3
  -- 81:1: λ (i i_1 i_2 i_3 : ℕ), (i.add i_1).mul ((i_1.mul i_2).mul i_3)

--set_option trace.class_instances true
--set_option class.instance_max_depth 20
--set_option pp.all true

section Streams
-- demo with streams:
--def StreamGen' (i : ℕ) (α : Type) := StreamGen E α
--def StreamGen.idx {α} (i : ℕ) : StreamGen E α → StreamGen' i α := id
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

instance : inhabited (Stream n α) := ⟨sorry⟩
instance : inhabited (G ι α) := ⟨sorry⟩

-- instance Stream.has_mul {α} {i} [has_mul α] : has_mul (StreamGen' i α) := ⟨StreamGen.mul⟩
instance Stream.has_mul {γ} {i} [has_mul γ] : has_mul (Stream i γ) := ⟨λ a b,
match a, b with
| Stream.view a, Stream.view b := arbitrary _ -- Stream.view $ a⋆b
| Stream.gen a, Stream.view b := Stream.gen $ a⋆b
| Stream.view a, Stream.gen b := Stream.gen $ a⋆b
| Stream.gen a, Stream.gen b := Stream.gen $ a⋆b
end⟩

variables
(a : Stream i E)
(a' : G E E)
(b : Stream j E)

example : has_mul (Stream i (Stream j E)) := infer_instance
example : Stream i (Stream j E) := a ⋆ b

instance : has_coe (G E E) (Stream n E) := ⟨Stream.gen⟩
instance coe_stream [has_coe α β] : has_coe (G E α) (Stream n β) := ⟨Stream.gen ∘ functor.map has_coe.coe⟩

class of_stream (α β : Type) := (coe : α → β)
instance base.of_stream : of_stream α α := ⟨id⟩
instance [of_stream α β] : of_stream (Stream n α) (G E β) := ⟨λ s, match s with
| Stream.view _ := arbitrary _
| Stream.gen a := of_stream.coe <$> a
end⟩

example : of_stream (Stream n α) (G E α) := infer_instance

def asdf  : Stream i E := a'
def asdf1 : Stream j E := a'

-- attribute [irreducible] StreamGen'

-- def g1 : StreamGen' i E := StreamGen.idx i (extern (E.ident "x"))
-- def g2 : StreamGen' j E := (extern (E.ident "y")).idx j
-- def g3 : StreamGen' k E := (range 1 2).to_StreamGen.idx k
-- def g4 : StreamGen' i (StreamGen' j E) := Rectangle.map i (λ _, (range 1 2).to_StreamGen.idx j) ((range 1 2).to_StreamGen.idx i)

-- def foo1 : Merge (StreamGen' i E) (StreamGen' j E) (StreamGen' i (StreamGen' j E))    := infer_instance
-- #print foo1
-- example : has_hmul (StreamGen' i E) (StreamGen' j E) (StreamGen' i (StreamGen' j E)) := infer_instance

-- #check g3 <*> g1 <*> g2 <*> g2 <*> g4

section front_end
infixr ` →ₛ `:24 := Stream

--def Stream.to_stream {n} [of_stream α β] : Stream n α → G E β := of_stream.coe
instance s_level.eval [of_stream γ β] [Ev α (G E β)] : Ev α (Stream i γ) := ⟨ λ l r, Ev.eval l (of_stream.coe r : G E β) ⟩
def Stream.of [of_stream α β] : α → β := of_stream.coe

def A1 : i →ₛ j →ₛ E := A
def B1 : j →ₛ k →ₛ E := B

def eg06' : Prog := me $ Ev.eval (E.ident "out") $ G.sum3' $ Stream.of $

  (A : i →ₛ j →ₛ E) ⋆ (B : j →ₛ k →ₛ E)

def eg30 := load_AB ++ [eg06', Prog.time "taco" $ taco_ijk]
#eval compile $ eg30


-- def typedMatrix (var : string) (i j : ℕ) : M (i →ₛ j →ₛ sorry) := do
--   let file := matrixFile,
--   var ← E.ident <$> fresh var (csparse (csparse cdouble)),
--   let gen := functor.map (functor.map StreamGen.singleton) $ functor.map extern (extern $ var),
--   return $ {gen with initialize := Prog.store var (E.call1 (E.ident "loadmtx")
--     (E.ident $ "\"" ++ file ++ "\""))}

-- infixr ` →ₛ `:24 := StreamGen
-- #check E →ₛ unit →ₛ E

-- #check @functor.map
-- --600:1: functor.map : Π {f : Type u_1 → Type u_2} [self : functor f] {α β : Type u_1}, (α → β) → f α → f β
-- #check @functor.map (λ x, E →ₛ x) _ (unit →ₛ E) β
