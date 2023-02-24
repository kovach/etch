import Etch.Basic

inductive CType
| int | double | char | bool | array : CType → CType
| none
deriving Repr

class Tagged (α : Type _) where
  tag : String
  decl : CType

def tag_mk_fun (α : Type _) [Tagged α] (fn : String) : String :=
(Tagged.tag α) ++ "_" ++ fn

inductive R | mk

def RMin := R
def RMin.ofR : R → RMin := id

def RMax := R
def RMax.ofR : R → RMax := id

instance : Tagged Unit := ⟨ "macro", .none ⟩ -- default type for actual monotypic function
instance : Tagged ℕ := ⟨ "nat", .int ⟩
instance : Tagged String := ⟨ "str", .array .char⟩
instance : Tagged Bool := ⟨ "bool", .bool ⟩
instance : Tagged R := ⟨ "num", .double ⟩
instance : Tagged RMin := ⟨ "min", .double ⟩
instance : Tagged RMax := ⟨ "max", .double ⟩
instance [Tagged α] : Tagged (ℕ → α) := ⟨ "arr_" ++ Tagged.tag α, .array (Tagged.decl α) ⟩

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

structure Op (α : Type _) where
  arity : ℕ
  argTypes : Fin arity → Type
  spec : ((n : Fin arity) → argTypes n) → α
  opName : String

attribute [reducible] Op.argTypes
attribute [simp] Op.spec

-- def Op.name (f : Op β) : String := f.tag ++ "_" ++ f.opName

@[simps, reducible]
def Op.lt [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → _) ] : Op Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 < a 1
  opName := tag_mk_fun α "lt"

@[simps, reducible]
def Op.le [Tagged α] [LE α] [DecidableRel (LE.le : α → α → _) ] : Op Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 ≤ a 1
  opName := tag_mk_fun α "le"

@[simps, reducible]
def Op.max [Tagged α] [Max α] : Op α where
  argTypes := ![α, α]
  spec := λ a => Max.max (a 0) (a 1)
  opName := tag_mk_fun α "max"

@[simps, reducible]
def Op.min [Tagged α] [Min α] : Op α where
  argTypes := ![α, α]
  spec := λ a => Min.min (a 0) (a 1)
  opName := tag_mk_fun α "min"

@[simps, reducible]
def Op.eq [Tagged α] [DecidableEq α] : Op Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 = a 1
  opName := tag_mk_fun α "eq"

@[simps, reducible]
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

@[simps, reducible]
def Op.mul [Tagged α] [Mul α] : Op α where
  argTypes := ![α, α]
  spec := λ a => a 0 * a 1
  opName := tag_mk_fun α "mul"

@[simps]
def Op.neg : Op Bool where
  argTypes := ![Bool]
  spec := λ a => not $ a 0
  opName := tag_mk_fun Bool "neg"

@[simps, reducible]
def Op.one [Tagged α] [OfNat α 1] : Op α where
  argTypes := ![]
  spec := λ _ => 1
  opName := tag_mk_fun α "one"

@[simps, reducible]
def Op.zero [Tagged α] [OfNat α 0] : Op α where
  argTypes := ![]
  spec := λ _ => 0
  opName := tag_mk_fun α "zero"

class OfString (α : Type _) where
  ofString : String → α
-- todo
instance : OfString ℕ := ⟨ fun _ ↦ default ⟩
instance : OfString R := ⟨ fun _ ↦ default ⟩

-- todo remove
def Op.atoi : Op ℕ where
  argTypes := ![String]
  spec := λ _ => default
  opName := tag_mk_fun String "atoi"
def Op.atof : Op R where
  argTypes := ![String]
  spec := λ _ => default -- todo
  opName := tag_mk_fun String "atof"

@[simps, reducible]
def Op.ofString [Tagged α] [OfString α] : Op α where
  argTypes := ![String]
  spec := fun a => OfString.ofString $ a 0
  opName := tag_mk_fun α "of_str"

def Op.ofBool [Tagged α] [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] : Op α where
  argTypes := ![Bool]
  spec := λ a => if a 0 then 1 else 0
  opName := tag_mk_fun α "ofBool"

def Op.toNum : Op R where
  argTypes := ![ℕ]
  spec := λ _ => default
  opName := tag_mk_fun ℕ "toNum"

def Op.toMin : Op RMin where
  argTypes := ![R]
  spec := λ a => RMin.ofR (a 0)
  opName := tag_mk_fun R "toMin"

def Op.toMax : Op RMax where
  argTypes := ![R]
  spec := λ a => RMax.ofR (a 0)
  opName := tag_mk_fun R "toMax"

def Op.ternary : Op α where
  argTypes := ![Bool, α, α]
  spec := λ a => bif (a 0) then a 1 else a 2
  opName := "macro_ternary"

def Op.udf : Op RMin := { argTypes := ![ℕ, ℕ], spec := default, opName := "udf" }
def Op.udf_max : Op RMax where argTypes := ![ℕ, ℕ]; spec := default; opName := "udf_max"
def Op.toGuard [Tagged α] [OfNat β 1] : Op β where argTypes := ![α]; spec := λ _ => 1; opName := tag_mk_fun α "toGuard"

def Op.access {ι α : Type} : Op α :=
{ argTypes := ![ι → α, ι],
  spec := λ x  => (x 0) (x 1),
  opName := "arr_access" }

@[simps, reducible]
def Op.nat (n : ℕ) : Op ℕ where
  argTypes := ![]
  spec := fun _ ↦ n
  opName := s!"nat_lit({n})"

instance : OfNat Bool (nat_lit 0) := ⟨ false ⟩
instance : OfNat Bool (nat_lit 1) := ⟨ .true ⟩
