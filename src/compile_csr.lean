import data.vector
import data.fin.vec_notation
import data.list.of_fn

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


-- @[reducible] def Ident := string
@[derive decidable_eq]
inductive Ident
| reserved_break : Ident
| name : string → Ident

def Ident.of : string → Ident := Ident.name
-- instance : decidable_eq Ident := infer_instance
instance : has_repr Ident := ⟨λ i, match i with
| Ident.reserved_break := "break"
| (Ident.name s) := s
end⟩

-- attribute [irreducible] Ident
-- #exit

inductive IdentVal
| base (val : ExprVal R) : IdentVal
| arr (val : list (ExprVal R)) : IdentVal
instance : inhabited (IdentVal R) := ⟨IdentVal.base default⟩ 

variable {R}
def IdentVal.get : IdentVal R → option ℕ → ExprVal R
| (IdentVal.base val) none := val
| (IdentVal.arr val) (some i) := val.inth i
| _ _ := arbitrary _ 

def IdentVal.update : IdentVal R → option ℕ → ExprVal R → IdentVal R
| (IdentVal.base val) none newval := IdentVal.base newval
| (IdentVal.arr val) (some i) newval := IdentVal.arr (val.modify_nth (λ _, newval) i)
| _ _ _ := arbitrary _

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

variable {R}
def eval : ∀ o : Op, (fin o.arity → ExprVal R) → ExprVal R
| add := λ x, (x 0).add (x 1)
| mul := λ x, (x 0).mul (x 1)
| and := λ x, (x 0).and (x 1)
| or := λ x, ((x 0).not.and $ (x 1).not).not -- TODO
| not := λ x, (x 0).not
| eq := λ x, (x 0).eq (x 1)
| lt := λ x, (x 0).lt (x 1)
| cast_r := λ x, (x 0).cast_r
end Op

variable (R)
inductive Expr
| lit : ExprVal R → Expr
| ident : Ident → Expr
| access : Ident → Expr → Expr
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
| (Expr.ident x) := (ctx x).get none
| (Expr.access x i) := (ctx x).get (some i.eval.to_nat)
| (Expr.call o args) := o.eval (λ i, (args i).eval)

instance has_coe_from_nat : has_coe ℕ (Expr R) := ⟨λ n, Expr.lit $ ExprVal.nat n⟩
instance has_coe_From_R : has_coe R (Expr R) := ⟨λ r, Expr.lit $ ExprVal.rval r⟩
instance has_coe_from_expr : has_coe Ident (Expr R) := ⟨Expr.ident⟩

example : Expr R := (0 : ℕ)
example : Expr R := (0 : R)

/-- Pretty print repr of indices; ignores [] (scalar), represents only
    vector indices -/
-- def idcs_repr (idcs : list string) : string :=
-- if idcs.length = 0 then "" else "[" ++ ", ".intercalate idcs ++ "]"

def expr_repr [has_repr R] : Expr R → string
| (Expr.lit r) := repr r
| (Expr.ident x) := repr x
| (Expr.access x i) := (repr x) ++ "[" ++ (expr_repr i) ++ "]"
| (Expr.call o args) := (repr o) ++ "(" ++ ", ".intercalate (vector.of_fn (λ i, expr_repr $ args i)).to_list ++ ")"

instance [has_repr R] : has_repr (Expr R) := ⟨expr_repr⟩
-- Because ambiguous whether R or ℕ
-- instance : has_zero (Expr R) := ⟨Expr.lit 0⟩
-- instance : has_one (Expr R) := ⟨Expr.lit 1⟩

variable (R)
inductive Prog
| skip : Prog
| store (dst : Ident) (ind : option (Expr R)) (val : Expr R)
| seq (a : Prog) (b : Prog)
| branch (cond : Expr R) (a : Prog) (b : Prog)
| loop (n : Expr R) (b : Prog)

variable {R}

def prog_repr [has_repr R] : Prog R → list string
| Prog.skip := [";"]
| (Prog.store dst ind val) := [(repr dst) ++ (ind.elim "" (λ i, "[" ++ repr i ++ "]")) ++ " := " ++ (repr val) ++ ";"]
| (Prog.seq a b) := (prog_repr a) ++ (prog_repr b)
| (Prog.branch c a b) := ["if " ++ (repr c)]
    ++ (prog_repr a).map (λ s, "  " ++ s)
    ++ ["else"]
    ++ (prog_repr b).map (λ s, "  " ++ s)
| (Prog.loop n b) := ["for at most " ++ (repr n) ++ " times"]
    ++ (prog_repr b).map (λ s, "  " ++ s)

instance [has_repr R] : has_to_string (Prog R) := ⟨λ p, "\n".intercalate (prog_repr p)⟩



def Prog.eval : Prog R → (Ident → IdentVal R) → (Ident → IdentVal R)
| Prog.skip ctx := ctx
| (Prog.store dst ind val) ctx := function.update ctx dst ((ctx dst).update (ind.map (λ i : Expr R, (i.eval ctx).to_nat)) (val.eval ctx))
| (Prog.seq a b) ctx := b.eval (a.eval ctx)
| (Prog.branch cond a b) ctx := if 0 < (Expr.eval ctx cond).to_nat then a.eval ctx else b.eval ctx
| (Prog.loop n b) ctx := (nat.iterate b.eval (Expr.eval ctx n).to_nat) ctx

infixr ` <;> `:1 := Prog.seq
notation a ` ::= `:20 c := Prog.store a none c
notation a ` ⟬ `:9000 i ` ⟭ ` ` ::= `:20 c := Prog.store a (some i) c
notation x ` ⟬ `:9000 i ` ⟭ ` := Expr.access x i 

-- 
section example_prog
namespace vars

abbreviation x := Ident.of "x"
abbreviation y := Ident.of "y"
abbreviation z := Ident.of "z"
abbreviation s := Ident.of "s"
abbreviation i := Ident.of "i"
abbreviation acc := Ident.of "acc"
abbreviation output := Ident.of "output"

end vars

open Expr Prog vars

def pow_prog : Prog ℤ :=
z ::= (1 : ℤ) <;>
loop y (z ::= x ⟪*⟫ z)

def pow_prog_input (i : Ident) : IdentVal ℤ :=
  if i = x then IdentVal.base (ExprVal.rval 3)
  else if i = y then IdentVal.base (ExprVal.nat 4)
  else arbitrary _

def arr_prog : Prog ℤ :=
s ::= (0 : ℤ) <;>
i ::= (0 : ℕ) <;>
loop y $
  s ::= s ⟪+⟫ x⟬i⟭ <;>
  i ::= i ⟪+⟫ (1 : ℕ)

def arr_prog_input (i : Ident) : IdentVal ℤ :=
  if i = x then IdentVal.arr [ExprVal.rval 30, ExprVal.rval (-1), ExprVal.rval 4]
  else if i = y then IdentVal.base (ExprVal.nat 3)
  else arbitrary _

end example_prog

variable (R)
structure BoundedStreamGen (ι α : Type) :=
(current : ι)
(value : α)
(ready : Expr R)
(next : Prog R)
(valid : Expr R)
(bound : Expr R)
(reset : Prog R)
(initialize : Prog R)

variables {ι α : Type} {R}

@[pattern]
def Prog.if1 (cond : Expr R) (b : Prog R) := Prog.branch cond b Prog.skip

def BoundedStreamGen.compile (g : BoundedStreamGen R unit (Prog R)) : Prog R :=
g.reset <;>
Ident.reserved_break ::= (0 : ℕ) <;>
Prog.loop g.bound $
  Prog.if1 (Expr.call Op.not ![Ident.reserved_break]) $
    Prog.if1 g.ready g.value <;>
    Prog.branch g.valid g.next (Ident.reserved_break ::= (1 : ℕ))


def BoundedStreamGen.singleton (a : α) : BoundedStreamGen R unit α :=
{ current := (),
  value := a,
  ready := (1 : ℕ),
  valid := (0 : ℕ),
  bound := (1 : ℕ),
  next := Prog.skip,
  reset := Prog.skip,
  initialize := Prog.skip }

def BoundedStreamGen.expr_to_prog (inp : BoundedStreamGen R unit (Expr R)) : BoundedStreamGen R unit (Prog R) :=
{ current := (),
  value := vars.output ::= inp.value,
  ready := inp.ready,
  next := inp.next,
  valid := inp.valid,
  bound := inp.bound,
  reset := inp.reset,
  initialize := inp.initialize }

section example_singleton

def test : BoundedStreamGen ℤ unit (Expr ℤ) := BoundedStreamGen.singleton (10 : ℤ)

#eval trace_val (to_string test.expr_to_prog.compile)

end example_singleton

def range (n : Expr R) (var : Ident) : BoundedStreamGen R (Expr R) (Expr R) :=
{ current := var,
  value := Expr.call Op.cast_r ![var],
  ready := var ⟪<⟫ n,
  valid := var ⟪<⟫ n,
  next := var ::= var ⟪+⟫ (1 : ℕ),
  reset := var ::= (0 : ℕ),
  bound := n,
  initialize := var ::= (0 : ℕ), }

def contraction {ι : Type} (acc : Ident) (v : BoundedStreamGen R ι (Expr R)) :
  BoundedStreamGen R unit (Expr R) :=
{ BoundedStreamGen.singleton acc with
  reset := v.reset <;>
    acc ::= (0 : R) <;>
    Prog.loop v.bound $
      Prog.if1 v.ready (acc ::= acc ⟪+⟫ v.value) <;>
      Prog.if1 v.valid v.next,
  initialize := v.initialize }

def flatten {ι₁ ι₂ α : Type} (outer : BoundedStreamGen R ι₁ (BoundedStreamGen R ι₂ α)) :
  BoundedStreamGen R (ι₁ × ι₂) α :=
let inner := outer.value in
{ current := (outer.current, inner.current),
  value := inner.value,
  ready := outer.ready ⟪&&⟫ inner.ready,
  next := let next_outer := outer.next <;> inner.reset in
  Prog.branch outer.ready 
    (Prog.branch inner.valid inner.next next_outer) 
    next_outer,
  valid := outer.valid,
  bound := outer.bound ⟪*⟫ inner.bound, -- TODO: fix
  reset := outer.reset <;> inner.reset, -- TODO: fix
  initialize := outer.initialize <;> inner.initialize }


-- x := (nat 0);
-- acc := (rval 0);
-- for at most (nat 2) times
--   if lt(x, (nat 2))
--     acc := add(acc, cast(x));
--   else
--     ;
--   if lt(x, (nat 2))
--     x := add(x, (nat 1));
--   else
--     ;
-- break := (nat 0);
-- for at most (nat 1) times
--   if not(break)
--     if (nat 1)
--       output := acc;
--     else
--       ;
--     if (nat 0)
--       ;
--     else
--       break := (nat 1);
--   else
--     ;

def test₂ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := range (4 : ℕ) vars.x
-- #eval trace_val $ to_string $ (contraction vars.acc test₂).expr_to_prog.compile
-- #eval ((contraction vars.acc test₂).expr_to_prog.compile.eval (λ _, arbitrary _) (Ident.of "output")).get none

def externVec (len : Expr R) (inp : Ident) (inp_idx : Ident) : BoundedStreamGen R (Expr R) (Expr R) :=
{ current := inp_idx,
  value := inp⟬ inp_idx ⟭,
  ready := inp_idx ⟪<⟫ len,
  next := inp_idx ::= inp_idx ⟪+⟫ (1 : ℕ),
  valid := inp_idx ⟪<⟫ len,
  bound := len,
  reset := inp_idx ::= (0 : ℕ),
  initialize := inp_idx ::= (0 : ℕ) }

def externCSRMat (l₁ l₂ : Expr R) (rows cols data : Ident) (i j k : Ident) :
  BoundedStreamGen R (Expr R × Expr R) (Expr R) :=
{ current := (i, cols⟬j⟭),
  value := data⟬k⟭,
  ready := j ⟪<⟫ rows⟬i ⟪+⟫ (1 : ℕ)⟭,
  next := 
    k ::= k ⟪+⟫ (1 : ℕ) <;>
    Prog.branch (j ⟪<⟫ rows⟬i ⟪+⟫ (1 : ℕ)⟭)
      (j ::= j ⟪+⟫ (1 : ℕ))
      (i ::= i ⟪+⟫ (1 : ℕ)),
  valid := i ⟪<⟫ l₁,
  bound := l₁ ⟪*⟫ l₂ ,
  reset := i ::= (0 : ℕ) <;> j ::= (0 : ℕ) <;> k ::= (0 : ℕ),
  initialize := Prog.skip }


def test₃ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := externVec (10 : ℕ) (Ident.of "input") (Ident.of "idx") 

#eval trace_val $ to_string $ (contraction (Ident.of "acc") test₃).expr_to_prog.compile
