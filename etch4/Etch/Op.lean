import Etch.Basic

class Tagged (α : Type _) where
  tag : String

inductive R | mk

def RMin := R
def RMin.ofR : R → RMin := id

def RMax := R
def RMax.ofR : R → RMax := id

instance : Tagged Unit := ⟨ "macro" ⟩
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

-- todo reconsider α parameter
structure O (α β : Type _) extends Tagged α where
  arity : ℕ
  argTypes : Fin arity → Type
  spec : ((n : Fin arity) → argTypes n) → β
  opName : String

def O.name (f : O α β) : String := f.tag ++ "_" ++ f.opName

def O.lt [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → _) ] : O α Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 < a 1
  opName := "lt"

def O.le [Tagged α] [LE α] [DecidableRel (LE.le : α → α → _) ] : O α Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 ≤ a 1
  opName := "le"

def O.max [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → Prop) ] : O α α where
  argTypes := ![α, α]
  spec := λ a => _root_.max (a 0) (a 1)
  opName := "max"

def O.min [Tagged α] [LE α] [DecidableRel (LE.le : α → α → Prop) ] : O α α where
  argTypes := ![α, α]
  spec := λ a => _root_.min (a 0) (a 1)
  opName := "min"

def O.eq [Tagged α] [DecidableEq α] : O α Bool where
  argTypes := ![α, α]
  spec := λ a => a 0 = a 1
  opName := "eq"

def O.add [Tagged α] [Add α] : O α α where
  argTypes := ![α, α]
  spec := λ a => a 0 + a 1
  opName := "add"

def O.sub [Tagged α] [Sub α] : O α α where
  argTypes := ![α, α]
  spec := λ a => a 0 - a 1
  opName := "sub"

def O.mid : O ℕ ℕ where
  argTypes := ![ℕ, ℕ]
  spec := λ a => Nat.div (a 0 + a 1) 2
  opName := "mid"

def O.mul [Tagged α] [Mul α] : O α α where
  argTypes := ![α, α]
  spec := λ a => a 0 * a 1
  opName := "mul"

def O.neg : O Bool Bool where
  argTypes := ![Bool]
  spec := λ a => not $ a 0
  opName := "neg"

def O.one [Tagged α] [OfNat α 1] : O α α where
  argTypes := ![]
  spec := λ _ => 1
  opName := "one"

def O.zero [Tagged α] [OfNat α 0] : O α α where
  argTypes := ![]
  spec := λ _ => 0
  opName := "zero"

def O.atoi : O String ℕ where
  argTypes := ![String]
  spec := λ _ => default
  opName := "atoi"

def O.atof : O String R where
  argTypes := ![String]
  spec := λ _ => default -- todo
  opName := "atof"

def O.ofBool [Tagged α] [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] : O α α where
  argTypes := ![Bool]
  spec := λ a => if a 0 then 1 else 0
  opName := "ofBool"

def O.toNum : O ℕ R where
  argTypes := ![ℕ]
  spec := λ _ => default
  opName := "toNum"

def O.toMin : O R RMin where
  argTypes := ![R]
  spec := λ a => RMin.ofR (a 0)
  opName := "toMin"

def O.toMax : O R RMax where
  argTypes := ![R]
  spec := λ a => RMax.ofR (a 0)
  opName := "toMax"

def O.ternary : O Unit α where
  argTypes := ![Bool, α, α]
  spec := λ a => bif (a 0) then a 1 else a 2
  opName := "ternary"

def O.udf : O ℕ RMin := { argTypes := ![ℕ, ℕ], spec := default, opName := "udf" }
def O.udf_max : O ℕ RMax where argTypes := ![ℕ, ℕ]; spec := default; opName := "udf_max"
def O.toGuard [Tagged α] [OfNat β 1] : O α β where argTypes := ![α]; spec := λ _ => 1; opName := "toGuard"
