import tactic.derive_fintype


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


section Ident

@[derive decidable_eq]
structure Ident :=
(ns : NameSpace)
(name : Vars)
(type : bool)


instance : has_to_string Ident :=
⟨λ i, "n" ++ (to_string i.ns) ++ "_" ++ (to_string i.name)⟩

@[simp] lemma Ident_ns_range : set.range Ident.ns = set.univ :=
by { ext, simp, exact ⟨⟨x, default, default⟩, rfl⟩, }

local infix `∷`:9000 := Ident.mk

end Ident