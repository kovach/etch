import data.vector
import data.fin.vec_notation

variables (R : Type) [has_zero R] [has_one R] [has_add R] [has_mul R]

@[reducible] def Ident := string
instance : decidable_eq Ident := infer_instance 
def Ident.of (x : string) : Ident := x
attribute [irreducible] Ident

inductive ExprVal
| nat (n : ℕ)
| float (r : R)
| stream {ι : Type} (current : ι) (val : ι → ExprVal)

instance : inhabited (ExprVal R) := ⟨ExprVal.nat 0⟩

namespace ExprVal
variable {R}

def add : ExprVal R → ExprVal R → ExprVal R
| (nat n₁) (nat n₂) := nat (n₁ + n₂)
| (float f₁) (float f₂) := float (f₁ + f₂)
| _ _ := arbitrary _

def and : ExprVal R → ExprVal R → ExprVal R
| (nat n₁) (nat n₂) := if n₁ = 0 then nat 0 else nat n₂
| _ _ := arbitrary _

def mul : ExprVal R → ExprVal R → ExprVal R
| (nat n₁) (nat n₂) := nat (n₁ * n₂)
| (float f₁) (float f₂) := float (f₁ * f₂)
| _ _ := arbitrary _

def value : ExprVal R → ExprVal R
| (stream c v) := v c 
| _ := arbitrary _

def to_nat : ExprVal R → ℕ
| (nat n₁) := n₁
| _ := 0

end ExprVal

inductive Op
| add | and | mul

@[reducible] def Op.arity : Op → ℕ
| Op.add := 2
| Op.mul := 2
| Op.and := 2

variable {R}
def Op.eval : ∀ o : Op, (fin o.arity → ExprVal R) → ExprVal R
| Op.add := λ x, (x 0).add (x 1)
| Op.mul := λ x, (x 0).mul (x 1)
| Op.and := λ x, (x 0).and (x 1)

variable (R)
inductive Expr
| lit : ExprVal R → Expr
| ident : Ident → Expr
| call : ∀ o : Op, (fin o.arity → Expr) → Expr

variable {R}
def Expr.eval  (ctx : Ident → ExprVal R) : Expr R → ExprVal R
| (Expr.lit r) := r
| (Expr.ident i) := ctx i
| (Expr.call o args) := o.eval (λ i, (args i).eval)


variable (R)
inductive Prog
| skip : Prog
| store (dst : Ident) (val : Expr R)
| seq (a : Prog) (b : Prog)
| branch (cond : Expr R) (a : Prog) (b : Prog)
| loop (n : Expr R) (b : Prog)

def Prog.eval : Prog R → (Ident → ExprVal R) → (Ident → ExprVal R)
| Prog.skip ctx := ctx
| (Prog.store dst val) ctx := function.update ctx dst (Expr.eval ctx val)
| (Prog.seq a b) ctx := b.eval (a.eval ctx)
| (Prog.branch cond a b) ctx := if (Expr.eval ctx cond).to_nat = 0 then a.eval ctx else b.eval ctx
| (Prog.loop n b) ctx := (nat.iterate b.eval $ (Expr.eval ctx n).to_nat) ctx


infixr ` <;> `:1 := Prog.seq
infixr ` ::= `:20 := Prog.store


section example_prog
namespace vars

abbreviation x := Ident.of "x"
abbreviation y := Ident.of "y"
abbreviation z := Ident.of "z"

end vars

open Expr Prog vars

end example_prog






