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

instance : Add R := ⟨ λ _ _ => default ⟩
instance : Add RMin := ⟨ λ _ _ => default ⟩
instance : Add RMax := ⟨ λ _ _ => default ⟩

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

attribute [irreducible] RMin
attribute [irreducible] RMax

-- todo reconsider α parameter
structure O (α β : Type _) extends Tagged α where
  arity : ℕ
  argTypes : Fin arity → Type
  spec : ((n : Fin arity) → argTypes n) → β
  --compileSpec : ((n : Fin arity) → E (argTypes n)) → P
  opName : String

def O.name (f : O α β) : String := f.tag ++ "_" ++ f.opName

def O.voidCall (f : String) : O Unit Unit where
  arity := 0
  argTypes := λ y => nomatch y
  spec := λ _ => default
  opName := ""
  tag := f

def O.lt [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → _) ] : O α Bool where
  arity := 2
  argTypes := λ | 0 => α | 1 => α
  spec := λ a => a 0 < a 1
  opName := "lt"

def O.le [Tagged α] [LE α] [DecidableRel (LE.le : α → α → _) ] : O α Bool where
  arity := 2
  argTypes := λ | 0 => α | 1 => α
  spec := λ a => a 0 ≤ a 1
  opName := "le"

def O.max [Tagged α] [LT α] [DecidableRel (LT.lt : α → α → Prop) ] : O α α where
  arity := 2
  argTypes := λ | 0 => α | 1 => α
  spec := λ a => _root_.max (a 0) (a 1)
  opName := "max"

def O.min [Tagged α] [LE α] [DecidableRel (LE.le : α → α → Prop) ] : O α α where
  arity := 2
  argTypes := λ | 0 => α | 1 => α
  spec := λ a => _root_.min (a 0) (a 1)
  opName := "min"

def O.eq [Tagged α] [DecidableEq α] : O α Bool where
  arity := 2
  argTypes := λ | 0 => α | 1 => α
  spec := λ a => a 0 = a 1
  opName := "eq"

def O.add [Tagged α] [Add α] : O α α where
  arity := 2
  argTypes := λ | 0 => α | 1 => α
  spec := λ a => a 0 + a 1
  opName := "add"

def O.sub [Tagged α] [Sub α] : O α α where
  arity := 2
  argTypes := λ | 0 => α | 1 => α
  spec := λ a => a 0 - a 1
  opName := "sub"

def O.mid : O ℕ ℕ where
  arity := 2
  argTypes := λ | 0 => ℕ | 1 => ℕ
  spec := λ a => Nat.div (a 0 + a 1) 2
  opName := "mid"

def O.mul [Tagged α] [Mul α] : O α α where
  arity := 2
  argTypes := λ | 0 => α | 1 => α
  spec := λ a => a 0 * a 1
  opName := "mul"

def O.neg : O Bool Bool where
  arity := 1
  argTypes := λ | 0 => Bool
  spec := λ a => not $ a 0
  opName := "neg"

def O.one [Tagged α] [OfNat α 1] : O α α where
  arity := 0
  argTypes := λ i => nomatch i
  spec := λ _ => 1
  opName := "one"

def O.zero [Tagged α] [OfNat α 0] : O α α where
  arity := 0
  argTypes := λ i => nomatch i
  spec := λ _ => 0
  opName := "zero"

def O.atoi : O String ℕ where
  arity := 1
  argTypes := λ | 0 => String
  spec := λ _ => default -- todo
  opName := "atoi"

def O.atof : O String R where
  arity := 1
  argTypes := λ | 0 => String
  spec := λ _ => default -- todo
  opName := "atof"

def O.ofBool [Tagged α] [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] : O α α where
  arity := 1
  argTypes := λ | 0 => Bool
  spec := λ a => if a 0 then 1 else 0
  opName := "ofBool"

def O.toNum : O ℕ R where
  arity := 1
  argTypes := λ | 0 => ℕ
  spec := λ _ => default -- todo
  opName := "toNum"

def O.toMin : O R RMin where
  arity := 1
  argTypes := λ | 0 => R
  spec := λ a => RMin.ofR (a 0)
  opName := "toMin"

def O.toMax : O R RMax where
  arity := 1
  argTypes := λ | 0 => R
  spec := λ a => RMax.ofR (a 0)
  opName := "toMax"

def O.ternary : O Unit α where
  arity := 3
  argTypes := λ | 0 => Bool | 1 => α | 2 => α
  spec := λ a => bif (a 0) then a 1 else a 2
  opName := "ternary"
