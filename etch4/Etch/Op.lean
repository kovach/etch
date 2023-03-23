import Etch.Basic

class Tagged (α : Type _) where
  tag : String

def tag_mk_fun (α : Type _) [Tagged α] (fn : String) : String :=
(Tagged.tag α) ++ "_" ++ fn

inductive R | mk

instance : Tagged Unit := ⟨ "macro" ⟩ -- default type for actual monotypic function
instance : Tagged ℕ := ⟨ "nat" ⟩
instance : Tagged Int := ⟨ "int" ⟩
instance : Tagged String := ⟨ "str" ⟩
instance : Tagged Bool := ⟨ "bool" ⟩
instance : Tagged R := ⟨ "num" ⟩

instance : Inhabited R := ⟨ R.mk ⟩
-- todo
instance : Add R := ⟨ λ _ _ => default ⟩
instance : LT R := ⟨ λ _ _  => false ⟩
instance : DecidableRel (LT.lt : R → R → _) :=  λ .mk .mk => .isFalse (by simp [LT.lt] )
instance : LE R := ⟨ λ _ _  => false ⟩
instance : DecidableRel (LE.le : R → R → _) :=  λ .mk .mk => .isFalse (by simp [LE.le] )

instance : DecidableEq R := fun .mk .mk => .isTrue (by simp)
instance : Max R := ⟨fun _ _ => default⟩
instance : Mul R := ⟨ λ _ _ => default ⟩

instance : Sub R := ⟨ λ _ _ => default ⟩

instance : OfNat R (nat_lit 0) := ⟨ default ⟩
instance : OfNat R (nat_lit 1) := ⟨ default ⟩

instance : Coe ℕ R := ⟨fun _ => default⟩

namespace String

instance instLEString : LE String := ⟨fun s₁ s₂ ↦ s₁ < s₂ || s₁ = s₂⟩

instance decLe : @DecidableRel String (· ≤ ·)
  | s₁, s₂ => if h₁ : s₁ < s₂ then isTrue (by simp [instLEString, h₁])
              else if h₂ : s₁ = s₂ then isTrue (by simp [instLEString, h₂])
              else isFalse (by simp [instLEString, h₁, h₂])

instance zero : Zero String := ⟨""⟩

instance max : Max String := ⟨fun s₁ s₂ ↦ if s₁ < s₂ then s₂ else s₁⟩

end String

--attribute [irreducible] RMin
--attribute [irreducible] RMax

structure Op (α : Type _) where
  arity : ℕ
  argTypes : Fin arity → Type
  spec : ((n : Fin arity) → argTypes n) → α
  opName : String

attribute [reducible] Op.argTypes
attribute [simp] Op.spec

-- def Op.name (f : Op β) : String := f.tag ++ "_" ++ f.opName

def Op.lt [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → _) ] : Op Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 < a 1
  opName := tag_mk_fun α "lt"

def Op.le [Tagged α] [LE α] [DecidableRel (LE.le : α → α → _) ] : Op Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 ≤ a 1
  opName := tag_mk_fun α "le"

def Op.max [Tagged α] [Max α] : Op α where
  argTypes := ![α, α]
  spec := λ a => Max.max (a 0) (a 1)
  opName := tag_mk_fun α "max"

def Op.min [Tagged α] [Min α] : Op α where
  argTypes := ![α, α]
  spec := λ a => Min.min (a 0) (a 1)
  opName := tag_mk_fun α "min"

@[simps, reducible]
def Op.eq [Tagged α] [DecidableEq α] : Op Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 = a 1
  opName := tag_mk_fun α "eq"

@[simps]
def Op.add [Tagged α] [Add α] : Op α where
  argTypes := ![α, α]
  spec := λ a => a 0 + a 1
  opName := tag_mk_fun α "add"

@[simps]
def Op.sub [Tagged α] [Sub α] : Op α where
  argTypes := ![α, α]
  spec := λ a => a 0 - a 1
  opName := tag_mk_fun α "sub"

def Op.mid : Op ℕ where
  argTypes := ![ℕ, ℕ]
  spec := λ a => Nat.div (a 0 + a 1) 2
  opName := tag_mk_fun ℕ "mid"

def Op.mul [Tagged α] [Mul α] : Op α where
  argTypes := ![α, α]
  spec := λ a => a 0 * a 1
  opName := tag_mk_fun α "mul"

def Op.div [Tagged α] [HDiv α α β] : Op β where
  argTypes := ![α, α]
  spec := λ a => a 0 / a 1
  opName := tag_mk_fun α "div"

@[simps]
def Op.neg : Op Bool where
  argTypes := ![Bool]
  spec := λ a => not $ a 0
  opName := tag_mk_fun Bool "neg"

def Op.one [Tagged α] [OfNat α 1] : Op α where
  argTypes := ![]
  spec := λ _ => 1
  opName := tag_mk_fun α "one"

def Op.zero [Tagged α] [OfNat α 0] : Op α where
  argTypes := ![]
  spec := λ _ => 0
  opName := tag_mk_fun α "zero"

def Op.atoi : Op ℕ where
  argTypes := ![String]
  spec := λ _ => default
  opName := tag_mk_fun String "atoi"

def Op.atof : Op R where
  argTypes := ![String]
  spec := λ _ => default -- todo
  opName := tag_mk_fun String "atof"

def Op.ofBool [Tagged α] [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] : Op α where
  argTypes := ![Bool]
  spec := λ a => if a 0 then 1 else 0
  opName := tag_mk_fun α "ofBool"

def Op.toNum : Op R where
  argTypes := ![ℕ]
  spec := λ _ => default
  opName := tag_mk_fun ℕ "toNum"

def Op.ternary : Op α where
  argTypes := ![Bool, α, α]
  spec := λ a => bif (a 0) then a 1 else a 2
  opName := "macro_ternary"

def Op.access {ι α : Type} : Op α :=
{ argTypes := ![ι → α, ι],
  spec := λ x  => (x 0) (x 1),
  opName := "arr_access" }
