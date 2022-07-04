import data.vector
import data.fin.vec_notation

-- This is just some experiments I'm doing, unofficial
-- Anything that works out will go back into compile.lean

variables (R : Type) [has_zero R] [has_one R] [has_add R] [has_mul R]

-- Same thing as `ℕ ⊕ R` TODO: change or keep?
inductive ExprVal
| nat (n : ℕ)
| rval (r : R)


namespace ExprVal
variable {R}

instance : inhabited (ExprVal R) := ⟨nat 0⟩

instance [has_repr R] : has_repr (ExprVal R) :=
⟨λ v, match v with
| (nat n) := "(nat " ++ (repr n) ++ ")"
| (rval r) := "(rval " ++ (repr r) ++ ")"
end⟩

def add : ExprVal R → ExprVal R → ExprVal R
| (nat n₁) (nat n₂) := nat (n₁ + n₂)
| (rval f₁) (rval f₂) := rval (f₁ + f₂)
| _ _ := arbitrary _


def and : ExprVal R → ExprVal R → ExprVal R
| (nat n₁) (nat n₂) := if n₁ = 0 then nat 0 else nat n₂
| _ _ := arbitrary _

def mul : ExprVal R → ExprVal R → ExprVal R
| (nat n₁) (nat n₂) := nat (n₁ * n₂)
| (rval f₁) (rval f₂) := rval (f₁ * f₂)
| _ _ := arbitrary _

def not : ExprVal R → ExprVal R
| (nat n₁) := if n₁ = 0 then nat 1 else nat 0
| _ := arbitrary _

def to_nat : ExprVal R → ℕ
| (nat n₁) := n₁
| _ := default

def eq : ExprVal R → ExprVal R → ExprVal R
| (nat n₁) (nat n₂) := if n₁ = n₂ then nat 1 else nat 0
| _ _ := arbitrary _

def lt : ExprVal R → ExprVal R → ExprVal R
| (nat n₁) (nat n₂) := if n₁ < n₂ then nat 1 else nat 0
| _ _ := arbitrary _

def to_r : ExprVal R → R
| (nat n) := n
| (rval r) := r

def cast_r (v : ExprVal R) : ExprVal R := rval v.to_r

end ExprVal

section Ident


@[reducible] def Ident := string
@[pattern] def Ident.of : string → Ident := id
instance : decidable_eq Ident := infer_instance
instance : has_repr Ident := infer_instance
attribute [irreducible] Ident

inductive IdentVal
| base : ExprVal R → IdentVal
| arr : ∀ (n : ℕ), (fin n → IdentVal) → IdentVal


variable {R}
def IdentVal.get : list ℕ → IdentVal R → ExprVal R
| [] (IdentVal.base x) := x
| (idx :: idcs) (IdentVal.arr n vals) :=
  if h : idx < n then (vals ⟨idx, h⟩).get idcs
  else arbitrary _
| _ _ := arbitrary _

end Ident


inductive Op
| add | mul | and | or | not | eq | lt | cast_r

namespace Op
instance : has_repr Op := ⟨λ v, match v with
| add := "add"
| mul := "mul"
| and := "and"
| or := "or"
| not := "not"
| eq := "eq"
| lt := "lt"
| cast_r := "cast"
end⟩

@[reducible] def arity : Op → ℕ
| Op.add := 2
| Op.mul := 2
| Op.and := 2
| Op.or := 2
| Op.not := 1
| Op.eq := 2
| Op.lt := 2
| Op.cast_r := 1
end Op

variable {R}
def Op.eval : ∀ o : Op, (fin o.arity → ExprVal R) → ExprVal R
| Op.add := λ x, (x 0).add (x 1)
| Op.mul := λ x, (x 0).mul (x 1)
| Op.and := λ x, (x 0).and (x 1)
| Op.or := λ x, ((x 0).not.and $ (x 1).not).not -- TODO
| Op.not := λ x, (x 0).not
| Op.eq := λ x, (x 0).eq (x 1)
| Op.lt := λ x, (x 0).lt (x 1)
| Op.cast_r := λ x, (x 0).cast_r

variable (R)
inductive Expr
| lit : ExprVal R → Expr
| ident : ∀ {n : ℕ}, Ident → (fin n → Expr) → Expr
| call : ∀ o : Op, (fin o.arity → Expr) → Expr

notation a ` ⟪+⟫ `:80 b := Expr.call Op.add ![a, b]
notation a ` ⟪*⟫ `:80 b := Expr.call Op.mul ![a, b]
notation a ` ⟪&&⟫ `:80 b := Expr.call Op.and ![a, b]
notation a ` ⟪||⟫ `:80 b := Expr.call Op.or ![a, b]
notation a ` ⟪<⟫ `:80 b := Expr.call Op.lt ![a, b]
notation a ` ⟪=⟫ `:80 b := Expr.call Op.eq ![a, b]


variable {R}
def Expr.eval  (ctx : Ident → IdentVal R) : Expr R → ExprVal R
| (Expr.lit r) := r
| (Expr.ident i idcs) := (ctx i).get (vector.of_fn (λ j, (idcs j).eval.to_nat)).to_list
| (Expr.call o args) := o.eval (λ i, (args i).eval)

instance has_coe_from_nat : has_coe ℕ (Expr R) := ⟨λ n, Expr.lit $ ExprVal.nat n⟩
instance has_coe_From_R : has_coe R (Expr R) := ⟨λ r, Expr.lit $ ExprVal.rval r⟩

example : Expr R := (0 : ℕ)
example : Expr R := (0 : R)

/-- Pretty print repr of indices; ignores [] (scalar), represents only
    vector indices -/
def idcs_repr {n : ℕ} (idcs : vector string n) : string :=
if n = 0 then "" else "[" ++ ", ".intercalate idcs.to_list ++ "]"

def expr_repr [has_repr R] : Expr R → string
| (Expr.lit r) := repr r
| (Expr.ident i idcs) := repr i ++ idcs_repr (vector.of_fn $ λ j, expr_repr (idcs j))
| (Expr.call o args) := (repr o) ++ "(" ++ ", ".intercalate (vector.of_fn (λ i, expr_repr $ args i)).to_list ++ ")"

instance [has_repr R] : has_repr (Expr R) := ⟨expr_repr⟩

-- Because ambiguous whether R or ℕ
-- instance : has_zero (Expr R) := ⟨Expr.lit 0⟩
-- instance : has_one (Expr R) := ⟨Expr.lit 1⟩

variable (R)
inductive Prog
| skip : Prog
| store (dst : Ident) (idcs : list (Expr R)) (val : Expr R)
| seq (a : Prog) (b : Prog)
| branch (cond : Expr R) (a : Prog) (b : Prog)
| loop (n : Expr R) (b : Prog)

variable {R}

def prog_repr [has_repr R] : Prog R → list string
| Prog.skip := [";"]
| (Prog.store dst val) := [(repr dst) ++ " := " ++ (repr val) ++ ";"]
| (Prog.seq a b) := (prog_repr a) ++ (prog_repr b)
| (Prog.branch c a b) := ["if " ++ (repr c)]
    ++ (prog_repr a).map (λ s, "  " ++ s)
    ++ ["else"]
    ++ (prog_repr b).map (λ s, "  " ++ s)
| (Prog.loop n b) := ["for " ++ (repr n) ++ " times"]
    ++ (prog_repr b).map (λ s, "  " ++ s)

instance [has_repr R] : has_to_string (Prog R) := ⟨λ p, "\n".intercalate (prog_repr p)⟩

def Prog.eval : Prog R → (Ident → IdentVal R) → (Ident → IdentVal R)
| Prog.skip ctx := ctx
| (Prog.store dst val) ctx := function.update ctx dst (Expr.eval ctx val)
| (Prog.seq a b) ctx := b.eval (a.eval ctx)
| (Prog.branch cond a b) ctx := if (Expr.eval ctx cond).to_nat = 0 then a.eval ctx else b.eval ctx
| (Prog.loop n b) ctx := (nat.iterate b.eval (Expr.eval ctx n).to_nat) ctx

infixr ` <;> `:1 := Prog.seq
infixr ` ::= `:20 := Prog.store

section example_prog
namespace vars

abbreviation x := Ident.of "x"
abbreviation y := Ident.of "y"
abbreviation z := Ident.of "z"

end vars

open Expr Prog vars

def pow_prog : Prog ℤ :=
z ::= (1 : ℤ) <;>
loop (ident y) (z ::= (ident x) ⟪*⟫ (ident z))

def pow_prog_input (i : Ident) : ExprVal ℤ :=
  if i = x then ExprVal.rval 3
  else if i = y then ExprVal.nat 4
  else ExprVal.rval 0

-- #eval (pow_prog.eval pow_prog_input) (Ident.of "z")

end example_prog

variable (R)
structure BoundedStreamGen (ι α : Type) :=
(current : ι)
(value : α)
(ready : Expr R)
(next : Prog R)
(empty : Expr R)
(bound : Expr R)
(reset : Prog R)
(initialize : Prog R)

variables {ι α : Type} {R}
def BoundedStreamGen.compile (g : BoundedStreamGen R unit (Prog R)) : Prog R :=
g.reset <;>
Prog.loop g.bound $
  Prog.branch g.ready g.value Prog.skip <;>
  Prog.branch g.empty Prog.skip g.next


def BoundedStreamGen.singleton (a : α) : BoundedStreamGen R unit α :=
{ current := (),
  value := a,
  ready := (1 : ℕ),
  empty := (1 : ℕ),
  bound := (1 : ℕ),
  next := Prog.skip,
  reset := Prog.skip,
  initialize := Prog.skip }

def BoundedStreamGen.expr_to_prog (inp : BoundedStreamGen R unit (Expr R)) : BoundedStreamGen R unit (Prog R) :=
{ current := (),
  value := (Ident.of "output") ::= inp.value,
  ready := inp.ready,
  next := inp.next,
  empty := inp.empty,
  bound := inp.bound,
  reset := inp.reset,
  initialize := inp.initialize }

section example_singleton

def test : BoundedStreamGen ℤ unit (Expr ℤ) := BoundedStreamGen.singleton (10 : ℤ)

#eval trace_val (to_string test.expr_to_prog.compile)

end example_singleton

def range (n : Expr R) (var : Ident) : BoundedStreamGen R (Expr R) (Expr R) :=
{ current := Expr.ident var,
  value := Expr.call Op.cast_r ![Expr.ident var],
  ready := (Expr.ident var) ⟪<⟫ n,
  empty := Expr.call Op.not ![(Expr.ident var) ⟪<⟫ n],
  next := var ::= (Expr.ident var) ⟪+⟫ (1 : ℕ),
  reset := var ::= (0 : ℕ),
  bound := n,
  initialize := var ::= (0 : ℕ), }

def contraction {ι : Type} (acc : Ident) (v : BoundedStreamGen R ι (Expr R)) :
  BoundedStreamGen R unit (Expr R) :=
{ BoundedStreamGen.singleton (Expr.ident acc) with
  reset := v.reset <;>
    acc ::= (0 : R) <;>
    Prog.loop v.bound $
      Prog.branch v.ready (acc ::= (Expr.ident acc) ⟪+⟫ v.value) Prog.skip <;>
      Prog.branch v.empty Prog.skip v.next,
  initialize := v.initialize }

def test₂ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := range (10 : ℕ) (Ident.of "x")
#eval trace_val $ to_string $ (contraction (Ident.of "acc") test₂).expr_to_prog.compile

def externVec (len : ℕ) : BoundedStreamGen R (Expr R) (Expr R) :=
let inp_idx := Ident.of "inp_idx" in
{ current := Expr.ident inp_idx,
  value := Expr.ident (Ident.of "input[inp_idx]"),
  ready := (Expr.ident inp_idx) ⟪<⟫ len,
  next := inp_idx ::= (Expr.ident inp_idx) ⟪+⟫ (1 : ℕ),
  empty := Expr.call Op.not ![Expr.ident inp_idx ⟪<⟫ len],
  bound := len,
  reset := inp_idx ::= (0 : ℕ),
  initialize := inp_idx ::= (0 : ℕ) }

def test₃ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := externVec 10

#eval trace_val $ to_string $ (contraction (Ident.of "acc") test₃).expr_to_prog.compile
