import tactic.derive_fintype
import logic.function.basic
import data.set.function

section vars
@[derive decidable_eq, derive fintype, derive inhabited]
inductive Vars
| i | j | k | w | x | y | z | ind₀ | ind₁ | ind₂ | break | output

open Vars
instance : has_to_string Vars :=
⟨λ v, match v with 
-- S.split(" | ").map(s => s + ' := "' + s + '"')
| i := "i" | j := "j" | k := "k" | w := "w" | x := "x" | y := "y" | z := "z" | ind₀ := "ind₀" | ind₁ := "ind₁" | ind₂ := "ind₂" | break := "break" | output := "output"
end⟩
end vars

section NameSpace
@[derive decidable_eq, derive inhabited, derive has_to_string, reducible]
def NameSpace := ℕ

def NameSpace.reserved : NameSpace := 0

def fresh (S : finset NameSpace) : NameSpace :=
S.max.iget + 1

theorem not_fresh_mem (S : finset NameSpace) : fresh S ∉ S :=
begin
  simp only [fresh],
  cases hn : S.max,
  { rw [finset.max_eq_none] at hn, subst hn, exact finset.not_mem_empty _, },
  intro h, simpa using finset.le_max_of_mem h hn,
end

theorem not_fresh_reserved (S : finset NameSpace) : fresh S ≠ NameSpace.reserved :=
by simp [fresh, NameSpace.reserved]

attribute [irreducible] NameSpace
end NameSpace

@[derive decidable_eq, derive fintype, derive inhabited]
inductive Types
| nn | rr

section Ident

@[derive decidable_eq]
structure Ident :=
(ns : NameSpace)
(name : Vars)
(type : Types)

instance : has_to_string Ident :=
⟨λ i, "n" ++ (to_string i.ns) ++ "_" ++ (to_string i.name)⟩

lemma Ident_ns_surjective : function.surjective Ident.ns :=
by { intro x, use ⟨x, default, default⟩, }

@[simp] lemma Ident_ns_range : set.range Ident.ns = set.univ :=
by simpa [set.surjective_iff_surj_on_univ, set.surj_on, set.univ_subset_iff] using Ident_ns_surjective

local infix `∷`:9000 := Ident.mk

end Ident

section frames
variables {α γ : Type*} {β : α → Type*} (f : (Π x, β x) → γ) (g : (Π x, β x) → (Π x, β x))

def function.has_dframe (S : set α) : Prop :=
∀ ⦃c₁ c₂ : Π x, β x⦄, (∀ x ∈ S, c₁ x = c₂ x) → f c₁ = f c₂

structure function.has_dheap (S : set α) : Prop :=
(local_frame : ∀ (c₁ c₂ : Π x, β x), (∀ x ∈ S, c₁ x = c₂ x) → ∀ {y}, y ∈ S → g c₁ y = g c₂ y)
(global_id : ∀ (c y), y ∉ S → g c y = c y)

theorem function.has_dframe.res {S S'} (h : function.has_dframe f S) (hS' : S ⊆ S') :
  function.has_dframe f S' :=
λ c₁ c₂ h', h (λ x hx, h' _ (hS' hx))

theorem function.has_dframe.const (x : γ) (S : set α) : function.has_dframe (λ _ : Π x, β x, x) S :=
λ _ _ _, rfl

theorem function.has_dheap.id (S : set α) : function.has_dheap (@id (Π x, β x)) S :=
{ local_frame := λ c₁ c₂ h y hy, h y hy,
  global_id := λ _ _ _, rfl }

end frames
