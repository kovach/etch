import Etch.Basic

class Tagged (α : Type _) where
  tag : String

def tag_mk_fun (α : Type _) [Tagged α] (fn : String) : String :=
(Tagged.tag α) ++ "_" ++ fn

inductive R | mk

def RMin := R
def RMin.ofR : R → RMin := id

def RMax := R
def RMax.ofR : R → RMax := id

instance : Tagged Unit := ⟨ "macro" ⟩ -- default type for actual monotypic function
instance : Tagged ℕ := ⟨ "nat" ⟩
instance : Tagged String := ⟨ "str" ⟩
instance : Tagged Bool := ⟨ "bool" ⟩
instance : Tagged R := ⟨ "num" ⟩
instance : Tagged RMin := ⟨ "min" ⟩
instance : Tagged RMax := ⟨ "max" ⟩

instance : Inhabited R := ⟨ R.mk ⟩
instance : Inhabited RMin := ⟨ R.mk ⟩
instance : Inhabited RMax := ⟨ R.mk ⟩
-- todo
instance : Add R := ⟨ λ _ _ => default ⟩
instance : Add RMin := ⟨ λ _ _ => default ⟩
instance : Add RMax := ⟨ λ _ _ => default ⟩
instance : LT R := ⟨ λ _ _  => false ⟩
instance : DecidableRel (LT.lt : R → R → _) :=  λ .mk .mk => .isFalse (by simp [LT.lt] )

instance : Mul R := ⟨ λ _ _ => default ⟩
instance : Mul RMin := ⟨ λ _ _ => default ⟩
instance : Mul RMax := ⟨ λ _ _ => default ⟩

instance : Sub R := ⟨ λ _ _ => default ⟩

instance : OfNat R (nat_lit 0) := ⟨ default ⟩
instance : OfNat R (nat_lit 1) := ⟨ default ⟩
instance : OfNat RMin (nat_lit 0) := ⟨ default ⟩
instance : OfNat RMin (nat_lit 1) := ⟨ default ⟩
instance : OfNat RMax (nat_lit 0) := ⟨ default ⟩
instance : OfNat RMax (nat_lit 1) := ⟨ default ⟩

--attribute [irreducible] RMin
--attribute [irreducible] RMax

structure O (α : Type _) where
  arity : ℕ
  argTypes : Fin arity → Type
  spec : ((n : Fin arity) → argTypes n) → α
  opName : String

-- def O.name (f : O β) : String := f.tag ++ "_" ++ f.opName

def O.lt [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → _) ] : O Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 < a 1
  opName := tag_mk_fun α "lt"

def O.le [Tagged α] [LE α] [DecidableRel (LE.le : α → α → _) ] : O Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 ≤ a 1
  opName := tag_mk_fun α "le"

def O.max [Tagged α] [Max α] : O α where
  argTypes := ![α, α]
  spec := λ a => Max.max (a 0) (a 1)
  opName := tag_mk_fun α "max"

def O.min [Tagged α] [Min α] : O α where
  argTypes := ![α, α]
  spec := λ a => Min.min (a 0) (a 1)
  opName := tag_mk_fun α "min"

def O.eq [Tagged α] [DecidableEq α] : O Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 = a 1
  opName := tag_mk_fun α "eq"

def O.add [Tagged α] [Add α] : O α where
  argTypes := ![α, α]
  spec := λ a => a 0 + a 1
  opName := tag_mk_fun α "add"

def O.sub [Tagged α] [Sub α] : O α where
  argTypes := ![α, α]
  spec := λ a => a 0 - a 1
  opName := tag_mk_fun α "sub"

def O.mid : O ℕ where
  argTypes := ![ℕ, ℕ]
  spec := λ a => Nat.div (a 0 + a 1) 2
  opName := tag_mk_fun ℕ "mid"

def O.mul [Tagged α] [Mul α] : O α where
  argTypes := ![α, α]
  spec := λ a => a 0 * a 1
  opName := tag_mk_fun α "mul"

def O.neg : O Bool where
  argTypes := ![Bool]
  spec := λ a => not $ a 0
  opName := tag_mk_fun Bool "neg"

def O.one [Tagged α] [OfNat α 1] : O α where
  argTypes := ![]
  spec := λ _ => 1
  opName := tag_mk_fun α "one"

def O.zero [Tagged α] [OfNat α 0] : O α where
  argTypes := ![]
  spec := λ _ => 0
  opName := tag_mk_fun α "zero"

def O.atoi : O ℕ where
  argTypes := ![String]
  spec := λ _ => default
  opName := tag_mk_fun String "atoi"

def O.atof : O R where
  argTypes := ![String]
  spec := λ _ => default -- todo
  opName := tag_mk_fun String "atof"

def O.ofBool [Tagged α] [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] : O α where
  argTypes := ![Bool]
  spec := λ a => if a 0 then 1 else 0
  opName := tag_mk_fun α "ofBool"

def O.toNum : O R where
  argTypes := ![ℕ]
  spec := λ _ => default
  opName := tag_mk_fun ℕ "toNum"

def O.toMin : O RMin where
  argTypes := ![R]
  spec := λ a => RMin.ofR (a 0)
  opName := tag_mk_fun R "toMin"

def O.toMax : O RMax where
  argTypes := ![R]
  spec := λ a => RMax.ofR (a 0)
  opName := tag_mk_fun R "toMax"

def O.ternary : O α where
  argTypes := ![Bool, α, α]
  spec := λ a => bif (a 0) then a 1 else a 2
  opName := "macro_ternary"

def O.udf : O RMin := { argTypes := ![ℕ, ℕ], spec := default, opName := "udf" }
def O.udf_max : O RMax where argTypes := ![ℕ, ℕ]; spec := default; opName := "udf_max"
def O.toGuard [Tagged α] [OfNat β 1] : O β where argTypes := ![α]; spec := λ _ => 1; opName := tag_mk_fun α "toGuard"

def O.access {ι α : Type} : O α :=
{ argTypes := ![ι → α, ι],
  spec := λ x  => (x 0) (x 1),
  opName := "arr_access" }
