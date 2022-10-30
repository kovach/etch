import verification.verify
import code_gen

variables {α ι γ β : Type}
variables (R : Type) [add_zero_class R] [has_one R] [has_mul R]

def rev_fmap_comp {f} [functor f] (x : α → f β) (y : β → f γ) := functor.map y ∘ x
infixr ` ⊚ `:90 := rev_fmap_comp
def rev_app : α → (α → β) → β := function.swap ($)
infixr ` & `:9 := rev_app

variable {R}

class has_hmul (α β : Type*) (γ : out_param Type*) :=
  (mul : α → β → γ)
instance hmul_of_mul {α : Type*} [has_mul α] : has_hmul α α α := ⟨has_mul.mul⟩
infix ` ⋆ `:71 := has_hmul.mul

open Types

def Ident.access {b} : Ident b → Expr R nn → Expr R b := Expr.access
def Ident.ident  {b} : Ident b → Expr R b := Expr.ident

namespace Expr
@[pattern] def false : Expr R bb := lit ff
@[pattern] def true  : Expr R bb := lit tt

def neg : Expr R bb → Expr R bb
| (Expr.true)  := Expr.false
| (Expr.false) := Expr.true
| e := Expr.call Op.not $ fin.cons e default
end Expr

infixr ` :: `:67 := fin.cons
notation `nil` := default
-- notation a ` ⟪&&⟫ `:70 b := Expr.call Op.and (a :: b :: nil)
-- notation a ` ⟪||⟫ `:65 b := Expr.call Op.or (a :: b :: nil)
notation a ` ⟪/=⟫ `:80 b := Expr.neg $ Expr.call Op.nat_eq (a :: b :: nil)
infixr ` ⟪;⟫ `:1 := Prog.seq
--@[pattern] def Expr.le : Expr R nn → Expr R nn → Expr R bb := λ a b, (a ⟪<⟫ b) ⟪||⟫ (a ⟪=⟫ b)
infix `∷`:9000 := Ident.mk

def Prog.accum : Ident rr → Expr R rr → Prog R := λ name v, Prog.store name (v + name.ident)
def Prog.accum_arr : Ident rr → Expr R nn → Expr R rr → Prog R := λ name i v, Prog.store_arr name i (v + name.ident)
def Ident.increment : Ident nn → Prog R := λ v, Prog.store v (v + 1)

def min : Expr R nn → Expr R nn → Expr R nn := λ a b, Expr.ternary (Expr.call Op.lt (a :: b :: nil)) a b
def max : Expr R nn → Expr R nn → Expr R nn := λ a b, Expr.ternary (Expr.call Op.lt (a :: b :: nil)) b a

def BoundedStreamGen.mul [has_hmul α β γ] (a : BoundedStreamGen R (Expr R nn) α) (b : BoundedStreamGen R (Expr R nn) β) : BoundedStreamGen R (Expr R nn) γ :=
{ current := max a.current b.current,
  value := a.value ⋆ b.value,
  ready := a.ready ⊓ b.ready ⊓ (a.current ⟪=⟫ b.current),
  next  := Prog.branch ((a.current ⟪<⟫ b.current) ⊔
                   ((a.current ⟪=⟫ b.current) ⊓ a.ready.neg))
                        a.next
                        b.next,
  valid := a.valid ⊓ b.valid,
  initialize  := a.initialize ⟪;⟫ b.initialize,
  bound := sorry,
  ctx_inv := λ _, true,
}

instance [has_hmul α β γ] : has_hmul
  (BoundedStreamGen R (Expr R nn) α)
  (BoundedStreamGen R (Expr R nn) β)
  (BoundedStreamGen R (Expr R nn) γ) := ⟨BoundedStreamGen.mul⟩

variables (R)
structure AccessExpr (b : Types) := (base : Ident b) (index : Expr R nn)

variables {R}

def AccessExpr.store {b} : AccessExpr R b → Expr R b → Prog R := λ e, Prog.store_arr e.base e.index
def AccessExpr.accum {b} : AccessExpr R b → Expr R b → Prog R := λ e, Prog.store_arr e.base e.index
def AccessExpr.expr  {b} : AccessExpr R b → Expr R b := λ e, Expr.access e.base e.index

section csr_lval
variables (R)

@[reducible] def loc := Expr R nn
structure il :=
  (crd  : loc R → Expr R nn)
  (push : Expr R nn → (loc R → Prog R) → Prog R × loc R)
structure vl (α : Type) :=
  (pos  : loc R → α)
  (init : loc R → Prog R)
structure lvl (α : Type) extends (il R), (vl R α).
instance : functor (lvl R) := { map := λ _ _ f l, { l with pos := f ∘ l.pos } }


variables {R}

def Prog.guard (a : Expr R bb) (b : Prog R) := Prog.branch a b Prog.skip

def sparse_index (indices : Ident nn) (bounds : AccessExpr R nn × AccessExpr R nn) : il R :=
let (lower, upper) := bounds, -- upper := uv.access ui, lower := lv.access li,
     current := indices.access (upper.expr - 1) in
let loc := upper.expr - 1 in
{ crd  := indices.access,
  push := λ i init,
    let prog := Prog.guard ((lower.expr ⟪=⟫ upper.expr) ⊔ (i ⟪/=⟫ current))
                      ((upper.accum 1) ⟪;⟫ init loc) ⟪;⟫
                Prog.store_arr indices (upper.expr - 1) i
    in (prog, loc) }

variable {R}

def Expr.to_loop_bound (e : Expr R nn) : LoopBound R := sorry

def dense_index (dim : Expr R nn) (counter : Ident nn) (base : Expr R nn) : il R :=
{ crd  := id,
  push := λ i init,
    let l i  : loc R  := base * dim + i,
        prog : Prog R := Prog.loop i.to_loop_bound (counter.to_expr ⟪≤⟫ i)
                           (init (l counter) ⟪;⟫ counter.increment)
    in (prog, l i) }


def interval_vl (array : Ident nn) : vl R (AccessExpr R nn × AccessExpr R nn) :=
{ pos  := λ loc, (⟨array, loc⟩, ⟨array, loc + 1⟩),
  init := λ loc, (AccessExpr.mk array $ loc + 1).store (array.access loc) }

def dense_vl (array : Ident rr) : vl R (Expr R rr) :=
{ pos  := λ loc, array.access loc,
  init := λ loc, (AccessExpr.mk array loc).store 0 }

def implicit_vl : vl R (Expr R nn) := { pos := id, init := λ _, Prog.skip }

-- this combinator combines an il with a vl to form a lvl.
-- the extra parameter α is used to thread the primary argument to a level through ⊚.
--   see dcsr/csr_mat/dense below
def with_values : (α → il R) → vl R β → α → lvl R β := λ i v e, lvl.mk (i e) v

def dense_mat (d₁ d₂ : Expr R nn) (ns : NameSpace) := 0 &
  (with_values (dense_index d₁ (ns ∷ Vars.i)) implicit_vl) ⊚
  (with_values (dense_index d₂ (ns ∷ Vars.j)) $ dense_vl (ns ∷ Vars.x))

def dcsr (ns : NameSpace) : lvl R (lvl R (Expr R rr)) :=
  let coord1 : Ident nn := ns ∷ Vars.i,
      coord2 : Ident nn := ns ∷ Vars.j,
      pos1   : Ident nn := ns ∷ Vars.x,
      pos2   : Ident nn := ns ∷ Vars.y,
      vals   : Ident rr := ns ∷ Vars.w
  in
    (interval_vl pos1).pos 0 &
      (with_values (sparse_index coord1) (interval_vl pos2)) ⊚
      (with_values (sparse_index coord2) (dense_vl vals))

def csr (d : Expr R nn) (ns : NameSpace) : lvl R (lvl R (Expr R rr)) :=
  let i    : Ident nn := ns ∷ Vars.i, coord2 : Ident nn := ns ∷ Vars.j,
      pos2 : Ident nn := ns ∷ Vars.y, vals   : Ident rr := ns ∷ Vars.w
  in 0 & (with_values (dense_index d i) (interval_vl pos2)) ⊚
         (with_values (sparse_index coord2) (dense_vl vals))

end csr_lval

variables (R)
class Compile (l r : Type) := (compile : l → r → Prog R)

instance expr.compile : Compile R (Ident rr) (Expr R rr) :=
{ compile := λ l r, Prog.store l r }

instance unit_compile [Compile R α β] : Compile R α (BoundedStreamGen R unit β) :=
{ compile := λ acc v,
    v.initialize ⟪;⟫ Prog.loop v.bound v.valid
      (Prog.guard v.ready (Compile.compile acc v.value) ⟪;⟫ v.next) }

instance ind_compile [Compile R α β] : Compile R (lvl R α) (BoundedStreamGen R (Expr R nn) β) :=
{ compile := λ storage v,
    let (push_i, loc) := storage.push v.current storage.init in
    v.initialize ⟪;⟫
    Prog.loop v.bound v.valid
      (Prog.guard v.ready (push_i ⟪;⟫ Compile.compile (storage.pos loc) v.value) ⟪;⟫ v.next) }

section output
variables {R}
def Ident.to_c : ∀ {b}, Ident b → codegen.Ident
| _ i := to_string i

def Op.to_c : ∀ {b}, Op b → codegen.E
| _ op := codegen.E.ident (to_string op)

def Expr.to_c : ∀ {b}, Expr R b → codegen.E
| rr (Expr.lit v) := default -- todo
| nn (Expr.lit v) := codegen.E.lit v
| bb (Expr.lit v) := codegen.E.lit (if v then 1 else 0)
| _ (Expr.ident i) := to_string i
| _ (Expr.access base i) := codegen.E.access base.to_c i.to_c
| _ (Expr.call op args) := codegen.E.call op.to_c $ list.of_fn (λ i, (args i).to_c)
| _ (Expr.ternary b c a) := codegen.E.ternary b.to_c c.to_c a.to_c

def Prog.to_c : Prog R → codegen.Prog
| (Prog.skip) := codegen.Prog.skip
| (Prog.store dst val) := codegen.Prog.store (to_string dst) val.to_c
| (Prog.store_arr dst i val) := codegen.Prog.store (Expr.access dst i).to_c val.to_c
| (Prog.seq a b) := codegen.Prog.seq a.to_c b.to_c
| (Prog.branch cond a b) := codegen.Prog.if cond.to_c a.to_c b.to_c
| (Prog.loop _ cond body) := codegen.Prog.while cond.to_c body.to_c

-- here. scalar types and declarations. update front end? finish chk and demo

end output
