import data.finsupp

-- structure Stream (ι α : Type) :=
-- (index : ι)
-- (value : ι → α)
-- (next : ι → ι)
-- (n : ℕ)

-- class Evalable (α β : Type) :=
-- (eval : α → β)

-- instance refl_eval {α : Type} : Evalable α α := ⟨id⟩ 

-- instance ind_eval {ι ι' α α' : Type} [Evalable ι ι'] [Evalable α α'] [has_zero α'] :
--   Evalable (Stream ι α) (ι →₀ α') := sorry

-- example {ι ι' α α' : Type} [Evalable ι ι'] [Evalable α α'] [has_zero α'] :
--   Evalable (Stream ι α) (ι →₀ α') := infer_instance

@[irreducible]
def Expr (R : Type) [add_zero_class R] : Type := ℕ

@[irreducible]
def Prog (R : Type) [add_zero_class R] : Type := ℕ

@[irreducible]
def Ident := ℕ

@[irreducible]
def IdentVal (R : Type) [add_zero_class R] : Type := ℕ

variables (R : Type) [add_zero_class R]

structure BoundedStreamGen (ι α : Type) :=
(current : ι)
(value : α)
(ready : Expr R)
(next : Prog R)
(valid : Expr R)
(bound : Expr R)
(reset : Prog R)
(initialize : Prog R)

class Evalable (α β : Type) :=
(eval : (Ident → IdentVal R) → α → β)

variable {R}
instance refl_eval {α : Type} : Evalable R α α := ⟨λ _, id⟩ 


instance base_eval_nat : Evalable R (Expr R) ℕ :=
sorry

instance base_eval_R : Evalable R (Expr R) R :=
sorry

instance ind_eval {ι ι' α α' : Type} [Evalable R ι ι'] [Evalable R α α'] [has_zero α'] :
  Evalable R (BoundedStreamGen R ι α) (ι →₀ α') := sorry

example {ι ι' α α' : Type} [Evalable R ι ι'] [Evalable R α α'] [has_zero α'] :
  Evalable R (BoundedStreamGen R ι α) (ι →₀ α') := infer_instance
