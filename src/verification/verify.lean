import data.fin.vec_notation
import verification.misc

def NameSpace := list ℕ

section vars
@[derive decidable_eq, derive inhabited]
inductive Vars
| i | j | k | w | x | y | z | ind₀ | ind₁ | ind₂ | break | output | len | vals

open Vars
instance : has_to_string Vars :=
⟨λ v, match v with
-- S.split(" | ").map(s => s + ' := "' + s + '"')
| i := "i" | j := "j" | k := "k" | w := "w" | x := "x" | y := "y" | z := "z" | ind₀ := "ind₀" | ind₁ := "ind₁" | ind₂ := "ind₂" | break := "break" | output := "output" | len := "len" | vals := "vals"
end⟩
end vars

structure Ident :=
(type : Type)
(ns : NameSpace)
(v : Vars)

def Context : Type 1 := ∀ (v : Ident), v.type

class has_tag (α : Type*) :=
(tag : string)

class has_axis_num (α : Type*) :=
(axis : string)

instance : has_tag ℕ := ⟨"NAT"⟩

def tag_mk_fun (α : Type*) [has_tag α] (fn : string) : string :=
(has_tag.tag α) ++ "_" ++ fn

structure Op (β : Type*) :=
(arity : ℕ)
(argTypes : fin arity → Type)
(spec : (Π n, argTypes n) → β)
(opName : string) -- For compiling to C

def Op.add {α : Type*} [has_tag α] [has_add α] : Op α :=
{ arity := 2,
  argTypes := ![α, α],
  spec := λ x, (x 0) + (x 1),
  opName := tag_mk_fun α "add" }

def Op.lit (n : ℕ) : Op ℕ :=
{ arity := 0,
  argTypes := default,
  spec := λ _, n,
  opName := "macro_lit(" ++ (to_string n) ++ ")" }

def Op.access {ι α : Type} : Op α :=
{ arity := 2,
  argTypes := ![ι → α, ι],
  spec := λ x, (x 0) (x 1),
  opName := "arr_access" }

def Op.top {ι : Type*} [has_axis_num ι] : Op (with_top ι) :=
{ arity := 0,
  argTypes := default,
  spec := λ _, ⊤,
  opName := "axis_" ++ (has_axis_num.axis ι) ++ "_max" }

inductive Expr : Type → Type 1
| call {β} (op : Op β) (args : ∀ i, Expr (op.argTypes i)) : Expr β
| var (v : Ident) : Expr v.type

@[simp] def Expr.eval (ctx : Context) : ∀ {α}, Expr α → α
| _ (Expr.call o args) := o.spec (λ n, Expr.eval (args n))
| _ (Expr.var v) := ctx v

-- PartialExpr (λ c, the value of "v" is 5) (Op.call = (var v) 5)
-- ParitalExpr (λ i, i < ⊤) a[i]
inductive PartialExpr (dom : Context → Prop) : Type → Type 1
| call {β} (op : Op β) (args : ∀ i, PartialExpr (op.argTypes i)) : PartialExpr β
| var (v : Ident) : PartialExpr v.type

instance {α : Type} [has_tag α] [has_add α] : has_add (Expr α) :=
⟨λ x y, Expr.call Op.add (fin.cons x $ fin.cons y fin_zero_elim)⟩

@[simp] lemma Expr.add_spec (e₁ e₂ : Expr ℕ) (ctx : Context) : (e₁ + e₂).eval ctx = (e₁.eval ctx) + (e₂.eval ctx) := rfl

inductive Prog
| skip : Prog
| store (dst : Ident) (val : Expr dst.type)
| seq (a : Prog) (b : Prog)
| branch (cond : Expr bool) (a : Prog) (b : Prog)

@[simp] def Prog.eval : Prog → Context → Context := sorry

section holes

inductive HExpr {σ : Type} (holes : σ → Type) : Type → Type 1
| call {β} (op : Op β) (args : ∀ i, HExpr (op.argTypes i)) : HExpr β
| var (v : Ident) : HExpr v.type
| hole (v : σ) : HExpr (holes v)

@[simp] def HExpr.toExpr {σ : Type} {holes : σ → Type} (vals : ∀ i, Expr (holes i)) :
  ∀ {α}, HExpr holes α → Expr α
| _ (HExpr.call op args) := Expr.call op (λ i, (args i).toExpr)
| _ (HExpr.var v) := Expr.var v
| _ (HExpr.hole v) := vals v



end holes

structure StreamGen (ι : Type) (α : ∀ {σ}, (σ → Type) → Type):=
(σ : Type)
(state : σ → Type)
(init : ∀ i, Expr (state i))
-- while (index ≠ ⊤) { .. } 
-- (if i < ⊤ then ↑inds[i] else ⊤) ≠ ⊤ ↔ i < ⊤
(index : HExpr state (with_top ι))
(ready : HExpr state bool)
-- i < ⊤
(value : α state)
(next : Prog)

/-
Program which prints CSR indices

for (int i = 0; i + 1 < rcrds.length; ++i) {
  int row_start = rows[i], row_end = rows[i+1];
  for (int j = row_start; j < row_end; ++j) {
    print("Row {i}, columns {cols[j]}, value {vals[j]}")
  }
}

-/

