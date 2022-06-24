import tactic
import data.list.alist
import control.monad.basic
import category_theory.category.basic
--import category_theory.category.Kleisli
--import category_theory.monad.kleisli
import category_theory.monad
--import category_theory.limits.shapes.finite_products
--import category_theory.products.basic
import category_theory.monoidal.category
import category_theory.closed.cartesian

-- some code inspired by http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf

section categories

open category_theory
-- #check monoidal_category.tensor_hom
-- #check cartesian_closed

-- replace with has_mul?
class has_prod (V : Type*) := (prod : V → V → V)
local infixr ` × ` := has_prod.prod
class has_sum  (V : Type*) := (sum : V → V → V)
local infix ` ⊔ ` := has_sum.sum

class cartesian (V : Type*) [category_struct V] extends has_prod V :=
(unit : V)
(exl : Π {A B : V}, (A × B) ⟶ A )
(exr : Π {A B : V}, A × B ⟶ B)
(pair : Π {A B C : V}, (C ⟶ A) → (C ⟶ B) → (C ⟶ (A × B)))
infix ` Δ `:22 := cartesian.pair

instance cartesian.has_one {V} [category_struct V] [cartesian V] : has_one V := ⟨cartesian.unit⟩
class cocartesian V [category_struct V] extends has_sum V :=
(inl : Π {A B : V}, A ⟶ A ⊔ B)
(inr : Π {A B : V}, B ⟶ A ⊔ B)
(copair : Π {A B C : V}, (A ⟶ C) → (B ⟶ C) → (A ⊔ B ⟶ C))
infix `∇`:22 := cocartesian.copair

class has_bool (V : Type*) [category_struct V] [cartesian V] [cocartesian V] :=
(bool : V := 1 ⊔ 1)
(not  : bool ⟶ bool)
(and  : bool × bool ⟶ bool)
(or   : bool × bool ⟶ bool)

notation `𝟚` := has_bool.bool

instance : quiver Type := ⟨(→)⟩
instance : category_theory.category_struct  Type := ⟨λ _, id, λ _ _ _ f g, g ∘ f⟩
instance : cartesian Type   :=
{ unit := unit,
  prod := prod,
  exl  := λ _ _, prod.fst,
  exr  := λ _ _, prod.snd,
  pair := λ _ _ _ f g x, (f x, g x),
}
instance : cocartesian Type :=
{ sum := sum,
  inl := λ _ _, sum.inl,
  inr := λ _ _, sum.inr,
  copair := λ _ _ _ f g, λ v, match v with | sum.inl a := f a | sum.inr b := g b end
}
instance : has_bool Type := ⟨bool, bnot, function.uncurry band, function.uncurry bor⟩

structure CatGen {V : Type*} [category_struct V] [cartesian V] [cocartesian V] [has_bool V] (S ι α : V) :=
(current    : S ⟶ ι)
(value      : S ⟶ α)
(next       : S ⟶ S)
(ready      : S ⟶ 𝟚)
(empty      : S ⟶ 𝟚)

variables {V : Type*} [category V] [cartesian V] [cocartesian V] [has_bool V]
open cartesian cocartesian

def cartesian.tensor {A B C D : V} (f : A ⟶ B) (g : C ⟶ D) : A×C ⟶ B×D := (exl ≫ f) Δ (exr ≫ g)
infixr ` ⊗ `:70 := cartesian.tensor

instance liftl {A B C : V} : has_coe (A ⟶ B) (A × C ⟶ B × C) := ⟨λ f, f ⊗ 𝟙 _⟩
instance liftr {A B C : V} : has_coe (A ⟶ B) (C × A ⟶ C × B) := ⟨λ f, 𝟙 _ ⊗ f⟩
variables {A B C D : V} (f : A ⟶ B)
-- #check (↑f : (C × A × B ⟶ C × B × B )) -- hmm

def i {A : V} : A ⟶ A := 𝟙 A
def dup {A : V} : A ⟶ A×A:= i Δ i

variables {S β α : V}

def mul_gen {S' : V} (mul : α×α⟶α) (f : CatGen S β α) (g : CatGen S' β α)
-- cheating for now:
(min : β×β⟶β) (min' : (β×S)×(β×S') ⟶ (S×S')⊔(S×S')) :
CatGen (S×S') β α :=
{ current := (exl ≫ f.current Δ exr ≫ g.current) ≫ min,
  next := (exl ≫ (f.current Δ 𝟙 _) Δ exr ≫ (g.current Δ 𝟙 _)) ≫ min' ≫ (f.next ∇ g.next),
  -- (f.next ⊗ 𝟙 _ ∇ 𝟙 _ ⊗ g.next),
  value := (f.value ⊗ g.value) ≫ mul,
  ready := (f.ready ⊗ g.ready) ≫ has_bool.and,
  empty := (f.empty ⊗ g.empty) ≫ has_bool.or,
}

def Gen.to_morphism (f : CatGen S β α) : S ⟶ (β × α) × S :=
(f.current Δ f.value) Δ f.next

class closed (V : Type*) [category_struct V] [cartesian V] :=
(hom : Π (A B : V), V)
(infixr ` ⇒ ` := hom)
(apply : Π {A B : V}, (A ⇒ B) × A ⟶ B)
(curry : Π {A B C : V}, (A × B ⟶ C) → (A ⟶ (B ⇒ C)))
(uncurry : Π {A B C : V}, (A ⟶ (B ⇒ C)) → (A × B ⟶ C))

#check category_theory.monad
/-
The data of a monad on C consists of an endofunctor T together with natural transformations
η : 𝟭 C ⟶ T and μ : T ⋙ T ⟶ T satisfying three equations:
- T μ_X ≫ μ_X = μ_(TX) ≫ μ_X (associativity)
- η_(TX) ≫ μ_X = 1_X (left unit)
- Tη_X ≫ μ_X = 1_X (right unit)
-/

-- Question: if we view a stream as an M-algebra for the writer monad M,
-- that is (s : S → (ι→α) × S), or (s : S → S) in the kleisli category,
-- can we define the evaluation map as a fixed point of this morphism? is that useful?

end categories
