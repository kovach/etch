import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.LibrarySearch
import Etch.Basic

-- the class does not need to reference K, the semiring of values
class PositiveAlgebra {A : Type} [DecidableEq A] (α : Finset A → Type) where
  finite : ∀ {S : Finset A}, α S → Type _
  equiv  : A → A → Prop

  mul      (a b : α S) : α S
  expand   (i : A) (S : Finset A) : α S → α (insert i S)
  contract (i : A) (S : Finset A) (s : α S) (fin : finite s) : α (Finset.erase S i)
  rename   (S : Finset A) (ρ : S → A) (equiv : (i : S) → equiv i (ρ i)) : α S → α (S.attach.image ρ)

section KRel
variable (K : Type) [Semiring K] {A : Type} [DecidableEq A] (I : A → Type) (S : Finset A) [(i : A) → DecidableEq (I i)]

abbrev Tuple := (s : S) → I s

instance : EmptyCollection (Tuple I Finset.empty) := ⟨ (nomatch .) ⟩
instance : Inhabited (Tuple I Finset.empty) := ⟨ {} ⟩

#synth DecidableEq (Tuple I S)

def KRel := Tuple I S → K
instance : Semiring (KRel K I S) := Pi.semiring

variable {I} {S}
def Tuple.project {S S' : Finset A} (sub : S ⊆ S') (t : Tuple I S') : Tuple I S := fun ⟨i, mem⟩ ↦ t ⟨i, Finset.mem_of_subset sub mem⟩
def Tuple.erase  (i : A) (t : Tuple I S) : Tuple I (S.erase i) := t.project (S.erase_subset _)
def Tuple.erase' (i : A) (t : Tuple I (insert i S)) : Tuple I S := t.project (S.subset_insert _)

instance KRel.positiveAlgebra : PositiveAlgebra (KRel K I) where
  finite f := Σ' supp : Finset (Tuple I _), ∀ x, f x ≠ 0 → x ∈ supp
  equiv := (I . = I .)
  mul a b := a * b
  expand i _ f x := f (x.erase' i)
  contract i S f fin := fun t ↦ fin.1.filter (fun t' : Tuple I S ↦ t'.erase i = t) |>.sum f
  rename S ρ equiv f t := f (fun (a : S) ↦ equiv a ▸ t ⟨ ρ a, Finset.mem_image_of_mem _ (Finset.mem_attach _ a) ⟩ )

#check @KRel.positiveAlgebra
instance [h : PositiveAlgebra 𝓣] : Mul (𝓣 S) := ⟨ h.mul ⟩

instance : One (KRel K I S) := ⟨ fun _ ↦ 1 ⟩
instance : Zero (KRel K I S) := ⟨ fun _ ↦ 0 ⟩

namespace KRel
variable {K}

def singleton (t : Tuple I S) (v : K) : KRel K I S := fun t' ↦ if t = t' then v else 0

@[simp] def singleton_zero {v : K} (t t' : Tuple I S) (h : t ≠ t') : singleton t v t' = 0 := by simp [singleton, h]
@[simp] def add_hom (f g : KRel K I S) : (f + g) x = f x + g x := rfl -- forgot what this is called

def ofList (l : List (Tuple I S × K)) : KRel K I S := l.map (fun (k, v) ↦ KRel.singleton k v) |>.sum

@[simp] def ofList_cons (kv : Tuple I S × K) : ofList (kv :: l) = singleton kv.fst kv.snd + ofList l := by simp [ofList]
@[simp] def ofList_nil_eq_zero : ofList [] = (0 : KRel K I S) := by simp [ofList]

def finite_ofList (l : List (Tuple I S × K)) : PositiveAlgebra.finite (KRel.ofList l) where
  fst := l.map Prod.fst |>.toFinset
  snd t neq_zero := by
    induction l with
    | nil => cases neq_zero rfl
    | cons kv l ih =>
      simp only [List.map, List.toFinset_cons, List.mem_toFinset, Finset.mem_insert] at ih ⊢
      by_cases h : kv.fst = t
      . left; exact h.symm
      . right; apply ih; simpa [h] using neq_zero

def Tuple.nil : Tuple I {} := {}
def nil : Tuple I {} := Tuple.nil

abbrev I1 : Fin 2 → Type := fun _ ↦ Fin 3
def t1 : Tuple I1 {0} := fun | ⟨0, _⟩ => 0
def t2 : Tuple I1 {0} := fun | ⟨0, _⟩ => 1
def l0 := [(t1, 1), (t2, 3)]
def f0 : KRel ℕ I1 {0} := ofList l0
def f1 : KRel ℕ I1 {0} := 1
#synth PositiveAlgebra (KRel ℕ (fun _ : Fin 2 => Fin 2))

def f2 : KRel ℕ (fun _ : Fin 2 ↦ Fin 2) {0,1} := 1

open PositiveAlgebra
def f0_finite : finite f0 := KRel.finite_ofList l0

notation:15 "∑ " i "," a => contract i _ (ofList a) (finite_ofList a)

#check contract 0 _ (ofList l0) (finite_ofList l0)
#reduce contract 0 _ f0 f0_finite
#eval contract 0 _ f0 f0_finite nil
#check contract 1 _ (ofList l0) (finite_ofList l0)
#eval (∑ 1, l0) t2

end KRel
