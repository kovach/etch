--set_option trace.Meta.synthInstance.instances true
--set_option pp.all true
import Mathlib.Algebra.Ring.Basic

instance : Add Bool := ⟨ or ⟩
instance : Mul Bool := ⟨ and ⟩

-- todo, generalize
def Fin.mk1 {γ : Fin 1 → Type _} (a : γ 0) : (i : Fin 1) → (γ i) | 0 => a
def Fin.mk2 {γ : Fin 2 → Type _} (a : γ 0) (b : γ 1) : (i : Fin 2) → (γ i) | 0 => a | 1 => b
def Fin.mk3 {γ : Fin 3 → Type _} (a : γ 0) (b : γ 1) (c : γ 2) : (i : Fin 3) → (γ i)
| 0 => a | 1 => b | 2 => c


set_option quotPrecheck false
notation "![]" => λ i => nomatch i
set_option quotPrecheck true
notation "![" a "]" => Fin.mk1 a
notation "![" a "," b "]" => Fin.mk2 a b
notation "![" a "," b "," c "]" => Fin.mk3 a b c

def List.ofFin_aux (k) (f : Fin k → α) : List α :=
match k, f with
| 0, _ => []
| n+1, f => f 0 :: List.ofFin_aux n (f ∘ Fin.succ)

def List.ofFin (f : Fin k → α) : List α := List.ofFin_aux _ f

def rev_fmap_comp {f} [Functor f] (x : α → f β) (y : β → γ) := Functor.map y ∘ x
infixr:90 "⊚" => rev_fmap_comp
def rev_app : α → (α → β) → β := Function.swap (. $ .)
infixr:9 "&" => rev_app
