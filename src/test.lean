import verification.vars

section
parameter (R : Type)

open Types (nn rr)


@[reducible]
def ExprVal : Types → Type
| nn := ℕ
| rr := R

def IdentVal : Types → Type := sorry
def IdentVal.get : ∀ {b : Types}, IdentVal b → ℕ → ExprVal b := sorry

inductive Expr : Types → Type
| lit {b} : ExprVal b → Expr b
| ident {b} : Ident b → Expr b
| access {b} : Ident b → Expr nn → Expr b


def Expr.eval (ctx : Context IdentVal) : ∀ {b}, Expr b → ExprVal b
| _ (Expr.lit r) := r
| b (Expr.ident x) := (λ a : Ident b → IdentVal b, IdentVal.get (a x) 0) (Context.get ctx)
| b (Expr.access x i) := IdentVal.get (ctx.get x) i.eval --(λ a : Ident b → IdentVal b, (a x).get i') (Context.get ctx)
end
