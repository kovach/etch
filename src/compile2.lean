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


@[reducible] def Ident := string
@[pattern] def Ident.of : string → Ident := id
instance : decidable_eq Ident := infer_instance
instance : has_repr Ident := ⟨id⟩
attribute [irreducible] Ident

inductive IdentVal
| base : ExprVal R → IdentVal
| arr : ∀ (n : ℕ), (fin n → IdentVal) → IdentVal

instance : inhabited (IdentVal R) := ⟨IdentVal.base default⟩ 

variable {R}
def IdentVal.get : list ℕ → IdentVal R → ExprVal R
| [] (IdentVal.base x) := x
| (idx :: idcs) (IdentVal.arr n vals) :=
  if h : idx < n then (vals ⟨idx, h⟩).get idcs
  else arbitrary _
| _ _ := arbitrary _

@[simp] lemma IdentVal.base_get (r : ExprVal R) :
  (IdentVal.base r).get [] = r := rfl
@[simp] lemma IdentVal.arr_get {n m : ℕ} (vals : fin n → IdentVal R) (h : m < n) (idcs : list ℕ) :
  (IdentVal.arr n vals).get (m :: idcs) = (vals ⟨m, h⟩).get idcs :=
by simp [IdentVal.get, h]


def IdentVal.update (y : ExprVal R) : list ℕ → IdentVal R → IdentVal R
| [] (IdentVal.base x) := IdentVal.base y
| (idx :: idcs) (IdentVal.arr n vals) :=
  if h : idx < n then
    let val' : IdentVal R := (vals ⟨idx, h⟩).update idcs in IdentVal.arr n $ function.update vals ⟨idx, h⟩ val'
  else arbitrary _ 
| _ _ := arbitrary _

-- TODO: definitional lemmas for update

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
| ident' : ∀ {n : ℕ}, Ident → (fin n → Expr) → Expr
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
| (Expr.ident' i idcs) := (ctx i).get (list.of_fn (λ j, (idcs j).eval.to_nat))
| (Expr.call o args) := o.eval (λ i, (args i).eval)

/-- An identifier with a list of indices -/
variable (R)
structure ExprLoc :=
(i : Ident)
(idcs : list (Expr R))

variable {R}
def ExprLoc.idcs_eval (loc : ExprLoc R) (ctx : Ident → IdentVal R) : list ℕ :=
loc.idcs.map $ ExprVal.to_nat ∘ Expr.eval ctx

def ExprLoc.get (loc : ExprLoc R) (ctx : Ident → IdentVal R) : ExprVal R :=
(ctx loc.i).get (loc.idcs_eval ctx)

def ExprLoc.update (loc : ExprLoc R) (ctx : Ident → IdentVal R) (val : ExprVal R) : Ident → IdentVal R :=
function.update ctx loc.i ((ctx loc.i).update val (loc.idcs_eval ctx))

def Expr.ident (loc : ExprLoc R) : Expr R :=
Expr.ident' loc.i (λ j : fin loc.idcs.length, loc.idcs.nth_le j (fin.is_lt j))


instance has_coe_from_nat : has_coe ℕ (Expr R) := ⟨λ n, Expr.lit $ ExprVal.nat n⟩
instance has_coe_From_R : has_coe R (Expr R) := ⟨λ r, Expr.lit $ ExprVal.rval r⟩

example : Expr R := (0 : ℕ)
example : Expr R := (0 : R)

/-- Pretty print repr of indices; ignores [] (scalar), represents only
    vector indices -/
def idcs_repr (idcs : list string) : string :=
if idcs.length = 0 then "" else "[" ++ ", ".intercalate idcs ++ "]"

def expr_repr [has_repr R] : Expr R → string
| (Expr.lit r) := repr r
| (Expr.ident' i idcs) := repr i ++ idcs_repr (list.of_fn $ λ j, expr_repr (idcs j))
| (Expr.call o args) := (repr o) ++ "(" ++ ", ".intercalate (vector.of_fn (λ i, expr_repr $ args i)).to_list ++ ")"

instance [has_repr R] : has_repr (Expr R) := ⟨expr_repr⟩
instance [has_repr R] : has_repr (ExprLoc R) :=
⟨λ loc, repr loc.i ++ idcs_repr (loc.idcs.map repr)⟩
-- Because ambiguous whether R or ℕ
-- instance : has_zero (Expr R) := ⟨Expr.lit 0⟩
-- instance : has_one (Expr R) := ⟨Expr.lit 1⟩

variable (R)
inductive Prog
| skip : Prog
| store (dst : ExprLoc R) (val : Expr R)
| seq (a : Prog) (b : Prog)
| branch (cond : Expr R) (a : Prog) (b : Prog)
| loop (n : Expr R) (b : Prog)

variable {R}

def prog_repr [has_repr R] : Prog R → list string
| Prog.skip := [";"]
| (Prog.store dst val) := [(repr dst.i) ++ (idcs_repr (dst.idcs.map repr)) ++ " := " ++ (repr val) ++ ";"]
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
| (Prog.store dst val) ctx := dst.update ctx (val.eval ctx)
| (Prog.seq a b) ctx := b.eval (a.eval ctx)
| (Prog.branch cond a b) ctx := if (Expr.eval ctx cond).to_nat = 0 then a.eval ctx else b.eval ctx
| (Prog.loop n b) ctx := (nat.iterate b.eval (Expr.eval ctx n).to_nat) ctx

infixr ` <;> `:1 := Prog.seq
notation a ` ::= `:20 c := Prog.store a c
notation x ` ⟬ ` l:(foldr `, ` (h t, list.cons h t) list.nil ` ⟭ `) := (ExprLoc.mk x l)
notation x ` ⟬ `:10000 l:(foldr `, ` (h t, list.cons h t) list.nil ` ⟭ `) := Expr.ident (ExprLoc.mk x l)

-- 
section example_prog
namespace vars

abbreviation x := Ident.of "x"
abbreviation y := Ident.of "y"
abbreviation z := Ident.of "z"

end vars

open Expr Prog vars

def pow_prog : Prog ℤ :=
z⟬⟭ ::= (1 : ℤ) <;>
loop (y⟬⟭) (z⟬⟭ ::= x⟬⟭ ⟪*⟫ z⟬⟭)

def pow_prog_input (i : Ident) : IdentVal ℤ :=
  if i = x then IdentVal.base (ExprVal.rval 3)
  else if i = y then IdentVal.base (ExprVal.nat 4)
  else arbitrary _

#eval ExprLoc.get z⟬⟭ (pow_prog.eval pow_prog_input)

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
  value := (Ident.of "output")⟬⟭ ::= inp.value,
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
{ current := var⟬⟭,
  value := Expr.call Op.cast_r ![var⟬⟭],
  ready := var⟬⟭ ⟪<⟫ n,
  empty := Expr.call Op.not ![var⟬⟭ ⟪<⟫ n],
  next := var⟬⟭ ::= var⟬⟭ ⟪+⟫ (1 : ℕ),
  reset := var⟬⟭ ::= (0 : ℕ),
  bound := n,
  initialize := var⟬⟭ ::= (0 : ℕ), }

def contraction {ι : Type} (acc : Ident) (v : BoundedStreamGen R ι (Expr R)) :
  BoundedStreamGen R unit (Expr R) :=
{ BoundedStreamGen.singleton (Expr.ident acc⟬⟭) with
  reset := v.reset <;>
    acc⟬⟭ ::= (0 : R) <;>
    Prog.loop v.bound $
      Prog.branch v.ready (acc⟬⟭ ::= acc⟬⟭ ⟪+⟫ v.value) Prog.skip <;>
      Prog.branch v.empty Prog.skip v.next,
  initialize := v.initialize }

def flatten {ι₁ ι₂ α : Type} (outer : BoundedStreamGen R ι₁ (BoundedStreamGen R ι₂ α)) :
  BoundedStreamGen R (ι₁ × ι₂) α :=
let inner := outer.value in
{ current := (outer.current, inner.current),
  value := inner.value,
  ready := outer.ready ⟪&&⟫ inner.ready,
  next := let next_outer := outer.next <;> inner.reset in
  Prog.branch outer.ready 
    (Prog.branch inner.empty next_outer inner.next) 
    next_outer,
  empty := outer.empty,
  bound := outer.bound ⟪*⟫ inner.bound, -- TODO: fix
  reset := outer.reset <;> inner.reset, -- TODO: fix
  initialize := outer.initialize <;> inner.initialize }

def test₂ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := range (10 : ℕ) (Ident.of "x")
#eval trace_val $ to_string $ (contraction (Ident.of "acc") test₂).expr_to_prog.compile

def externVec (len : Expr R) (inp : Ident) (inp_idx : Ident) : BoundedStreamGen R (Expr R) (Expr R) :=
{ current := Expr.ident inp_idx⟬⟭,
  value := inp⟬ inp_idx⟬⟭ ⟭,
  ready := inp_idx⟬⟭ ⟪<⟫ len,
  next := inp_idx⟬⟭ ::= inp_idx⟬⟭ ⟪+⟫ (1 : ℕ),
  empty := Expr.call Op.not ![inp_idx⟬⟭ ⟪<⟫ len],
  bound := len,
  reset := inp_idx⟬⟭ ::= (0 : ℕ),
  initialize := inp_idx⟬⟭ ::= (0 : ℕ) }

def externMat (l₁ l₂ : Expr R) (inp idx₁ idx₂ : Ident) : BoundedStreamGen R (Expr R) (BoundedStreamGen R (Expr R) (Expr R)) :=
{ current := Expr.ident idx₁⟬⟭,
  value := { current := Expr.ident idx₂⟬⟭,
    value := inp⟬idx₁⟬⟭, idx₂⟬⟭⟭,
    ready := idx₂⟬⟭ ⟪<⟫ l₂,
    next := idx₂⟬⟭ ::= idx₂⟬⟭ ⟪+⟫ (1 : ℕ),
    empty := Expr.call Op.not ![idx₂⟬⟭ ⟪<⟫ l₂],
    bound := l₂,
    reset := idx₂⟬⟭ ::= (0 : ℕ),
    initialize := idx₂⟬⟭ ::= (0 : ℕ) },
  ready := idx₁⟬⟭ ⟪<⟫ l₁,
  next := idx₁⟬⟭ ::= idx₁⟬⟭ ⟪+⟫ (1 : ℕ),
  empty := Expr.call Op.not ![idx₁⟬⟭ ⟪<⟫ l₁],
  bound := l₁,
  reset := idx₁⟬⟭ ::= (0 : ℕ),
  initialize := idx₁⟬⟭ ::= (0 : ℕ) }

def externSparseMat (l₁ l₂ : Expr R) (vals idx₁ idx₂ i j : Ident) : BoundedStreamGen R (Expr R) (BoundedStreamGen R (Expr R) (Expr R)) :=
{ current := Expr.ident i⟬⟭,
  value := { current := Expr.ident j⟬⟭,
    value := vals⟬ idx₂⟬idx₁⟬i⟬⟭⟭, j⟬⟭⟭ ⟭,
    ready := j⟬⟭ ⟪<⟫ l₂,
    next := j⟬⟭ ::= j⟬⟭ ⟪+⟫ (1 : ℕ),
    empty := Expr.call Op.not ![j⟬⟭ ⟪<⟫ l₂],
    bound := l₂,
    reset := j⟬⟭ ::= (0 : ℕ),
    initialize := j⟬⟭ ::= (0 : ℕ) },
  ready := i⟬⟭ ⟪<⟫ l₁,
  next := i⟬⟭ ::= i⟬⟭ ⟪+⟫ (1 : ℕ),
  empty := Expr.call Op.not ![i⟬⟭ ⟪<⟫ l₁],
  bound := l₁,
  reset := i⟬⟭ ::= (0 : ℕ),
  initialize := i⟬⟭ ::= (0 : ℕ) }

def test₃ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := externVec (10 : ℕ) (Ident.of "input") (Ident.of "idx") 

#eval trace_val $ to_string $ (contraction (Ident.of "acc") test₃).expr_to_prog.compile

def test₄ : BoundedStreamGen ℤ (Expr ℤ) _ := externMat (10 : ℕ) (20 : ℕ) (Ident.of "inp") vars.x vars.y 
def test₅ : BoundedStreamGen ℤ (Expr ℤ × Expr ℤ) (Expr ℤ) := flatten test₄

#eval trace_val $ to_string $ (contraction (Ident.of "acc") test₅).expr_to_prog.compile


def test₆ : BoundedStreamGen ℤ (Expr ℤ) _ := externSparseMat (10 : ℕ) (20 : ℕ) (Ident.of "vals") (Ident.of "idx₁") (Ident.of "idx₂") (Ident.of "i") (Ident.of "j")
def test₇ : BoundedStreamGen ℤ (Expr ℤ × Expr ℤ) (Expr ℤ) := flatten test₆

#eval trace_val $ to_string $ (contraction (Ident.of "acc") test₇).expr_to_prog.compile