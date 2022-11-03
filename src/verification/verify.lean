import data.vector
import data.fin.vec_notation
import data.fin.tuple.basic
import data.list.of_fn
import data.list.alist
import data.finsupp.basic
import control.bifunctor
import tactic.derive_fintype
import tactic.fin_cases
import finsupp_lemmas
import frames
import verification.vars
import verification.misc
import verification.stream
import data.pfun

section

parameters (R : Type)
open Types (nn rr bb)
open NameSpace (reserved)
open Vars (ind₀ vals len output)

section compiler

parameters [add_comm_monoid R] [has_one R] [has_mul R]

@[reducible]
def ExprVal : Types → Type
| nn := ℕ
| rr := R
| bb := bool

parameter {R}
namespace ExprVal

instance : ∀ b, inhabited (ExprVal b)
| nn := ⟨0⟩
| rr := ⟨0⟩
| bb := ⟨ff⟩

instance [has_to_string R] :
∀ b, has_to_string (ExprVal b)
| nn := infer_instance
| rr := infer_instance
| bb := infer_instance

end ExprVal

@[derive decidable_eq]
inductive Op : Types → Type
| nadd : Op nn | radd : Op rr
| nmul : Op nn | rmul : Op rr
| nsub : Op nn
| and : Op bb
| or : Op bb
| not : Op bb
| nat_eq : Op bb
| lt : Op bb
| le : Op bb
| cast_r : Op rr

namespace Op
instance : ∀ b, has_to_string (Op b)
| rr := ⟨λ v, match v with
| radd := "+"
| rmul := "*"
| cast_r := "cast"
end⟩
| nn := ⟨λ v, match v with
| nadd := "+"
| nmul := "*"
| nsub := "-"
end⟩
| bb := ⟨λ v, match v with
| and := "&&"
| or := "||"
| not := "!"
| nat_eq := "="
| lt := "<"
| le := "<="
end⟩

@[reducible]
def arity : ∀ {b}, Op b → ℕ
| _ nadd := 2
| _ radd := 2
| _ nmul := 2
| _ rmul := 2
| _ nsub := 2
| _ and := 2 | _ or := 2 | _ not := 1 | _ nat_eq := 2 | _ lt := 2 | _ le := 2
| _ cast_r := 1

def is_not_infix : finset (Σ b, Op b) :=
{⟨_, Op.cast_r⟩}

def to_str_with_args {b} (o : Op b) (args : list string) : string :=
if H : (sigma.mk b o) ∈ is_not_infix ∨ 3 ≤ o.arity then
  (to_string o) ++ "(" ++ ", ".intercalate args ++ ")"
else match o.arity, (show ¬(3 ≤ o.arity), by tauto!) with
  0, _ := (to_string o),
  1, _ := (to_string o) ++ args.head,
  2, _ := "(" ++ (args.inth 0) ++ " " ++ (to_string o) ++ " " ++ (args.inth 1) ++ ")",
  (n + 3), h := by { exfalso, simpa using h, }
end

@[reducible]
def signature : ∀ {b} (o : Op b), (fin o.arity → Types)
| _ nadd := ![nn, nn] | _ radd := ![rr, rr]
| _ nmul := ![nn, nn] | _ rmul := ![rr, rr]
| _ nsub := ![nn, nn]
| _ and := ![bb, bb] | _ or := ![bb, bb] | _ not := ![bb]
| _ nat_eq := ![nn, nn] | _ lt := ![nn, nn] | _ le := ![nn, nn]
| _ cast_r := ![nn]

@[simp]
def eval : ∀ {b} (o : Op b), (Π (n : fin o.arity), ExprVal (o.signature n)) → ExprVal b
| _ nadd := λ args, ((+) : ℕ → ℕ → ℕ) (args 0) (args 1)
| _ radd := λ args, ((+) : R → R → R) (args 0) (args 1)
| _ nmul := λ args, ((*) : ℕ → ℕ → ℕ) (args 0) (args 1)
| _ rmul := λ args, ((*) : R → R → R) (args 0) (args 1)
| _ nsub := λ args, nat.sub (args 0) (args 1)
| _ and := λ args, (args 0 : bool) && (args 1 : bool)
| _ or := λ args, (args 0 : bool) || (args 1 : bool)
| _ not := λ args, bnot (args 0)
| _ nat_eq := λ args, args 0 = args 1
| _ lt := λ args, (show ℕ, from args 0) < args 1
| _ le := λ args, (show ℕ, from args 0) ≤ args 1
| _ cast_r := λ args, show ℕ, from args 0

end Op

parameter (R)
inductive Expr : Types → Type
| lit {b} : ExprVal b → Expr b
| ident {b} : Ident b → Expr b
| access {b} : Ident b → Expr nn → Expr b
| call {b} : ∀ o : Op b, (Π (n : fin o.arity), Expr (o.signature n)) → Expr b
| ternary {b} : Expr bb → Expr b → Expr b → Expr b


abbreviation EContext := HeapContext ExprVal
abbreviation Frame := finset (Σ b, Ident b)
instance : inhabited Frame := ⟨(default : finset (Σ b, Ident b))⟩

parameter {R}

def Expr.eval (ctx : EContext) : ∀ {b}, Expr b → option (ExprVal b)
| _ (Expr.lit r) := some r
| b (Expr.ident x) := some (ctx.store.get x)
| b (Expr.access x i) := i.eval >>= λ i', (ctx.heap.get x).nth i'
| _ (Expr.call o args) := fin.tuple_some (λ i, (args i).eval) >>= λ r, some (o.eval r)
| _ (Expr.ternary c e₁ e₂) := c.eval >>= λ r, cond r e₁.eval e₂.eval

@[simp] def Expr.frame : ∀ {b}, Expr b → Frame
| _ (Expr.lit r) := ∅
| _ (Expr.ident x) := {sigma.mk _ x}
| _ (Expr.access x i) := insert (sigma.mk _ x) i.frame
| _ (Expr.call o args) := finset.bUnion finset.univ (λ i, (args i).frame)
| _ (Expr.ternary c e₁ e₂) := c.frame ∪ e₁.frame ∪ e₂.frame

-- local notation a ` ⟪<⟫ ` b := Expr.call Op.lt (fin.cons (a : Expr nn) (fin.cons (b : Expr nn) default))

class has_comp (α : Type*) (β : out_param Type*) :=
(eq : α → α → β)
(le : α → α → β)
(lt : α → α → β)
(ge : α → α → β)
(gt : α → α → β)

infix ` ⟪≤⟫ `:50   := has_comp.le
infix ` ⟪<⟫ `:50   := has_comp.lt
infix ` ⟪≥⟫ `:50   := has_comp.ge
infix ` ⟪>⟫ `:50   := has_comp.gt
infix ` ⟪=⟫ `:50   := has_comp.eq

@[simps { attrs := [] }] instance Expr.has_comp : has_comp (Expr nn) (Expr bb) :=
{ eq := λ a b, Expr.call Op.nat_eq $ fin.cons a $ fin.cons b default,
  lt := λ a b, Expr.call Op.lt $ fin.cons a $ fin.cons b default,
  le := λ a b, Expr.call Op.le $ fin.cons a $ fin.cons b default,
  ge := λ a b, Expr.call Op.le $ fin.cons b $ fin.cons a default,
  gt := λ a b, Expr.call Op.lt $ fin.cons b $ fin.cons a default }

section Expr

def expr_repr [has_to_string R] : ∀ {b : Types}, (Expr b) → string
| _ (Expr.lit r) := to_string r
| _ (Expr.ident x) := to_string x
| _ (Expr.access x i) := (to_string x) ++ "[" ++ (expr_repr i) ++ "]"
| _ (Expr.call o args) := o.to_str_with_args (vector.of_fn (λ i, expr_repr $ args i)).to_list
| _ (Expr.ternary c e₁ e₂) := (expr_repr c) ++ " ? " ++ (expr_repr e₁) ++ " : " ++ (expr_repr e₂)

instance {b : Types} [has_to_string R] : has_to_string (Expr b) := ⟨expr_repr⟩

instance Expr.zero_nn : has_zero (Expr nn) := ⟨Expr.lit (0 : ℕ)⟩
instance Expr.one_nn : has_one (Expr nn) := ⟨Expr.lit (1 : ℕ)⟩
instance Expr.zero_rr : has_zero (Expr rr) := ⟨Expr.lit (0 : R)⟩
instance Expr.one_rr : has_one (Expr rr) := ⟨Expr.lit (1 : R)⟩

instance Expr.has_coe_from_nat : has_coe ℕ (Expr nn) := ⟨λ n, Expr.lit n⟩
instance Expr.has_coe_from_R : has_coe R (Expr rr) := ⟨λ r, Expr.lit r⟩

@[simp] lemma Expr_frame_coe_nat (n : ℕ) : (n : Expr nn).frame = ∅ := rfl
@[simp] lemma Expr_frame_coe_R (r : R) : (r : Expr rr).frame = ∅ := rfl
@[simp] lemma Expr_frame_zero_nat : (0 : Expr nn).frame = ∅ := rfl
@[simp] lemma Expr_frame_one_nat : (1 : Expr nn).frame = ∅ := rfl

@[simps { attrs := [] }] instance add_nn : has_add (Expr nn) :=
⟨λ a b, Expr.call Op.nadd (fin.cons a (fin.cons b default))⟩
@[simps { attrs := [] }] instance add_rr : has_add (Expr rr) :=
⟨λ a b, Expr.call Op.radd (fin.cons a (fin.cons b default))⟩
@[simps { attrs := [] }] instance mul_nn : has_mul (Expr nn) :=
⟨λ a b, Expr.call Op.nmul (fin.cons a (fin.cons b default))⟩
@[simps { attrs := [] }] instance mul_rr : has_mul (Expr rr) :=
⟨λ a b, Expr.call Op.rmul (fin.cons a (fin.cons b default))⟩
@[simps { attrs := [] }] instance sub_nn : has_sub (Expr nn) :=
⟨λ a b, Expr.call Op.nsub (fin.cons a (fin.cons b default))⟩

instance inf_bb : has_inf (Expr bb) :=
⟨λ a b, Expr.call Op.and (fin.cons a (fin.cons b default))⟩

instance sup_bb : has_sup (Expr bb) :=
⟨λ a b, Expr.call Op.or (fin.cons a (fin.cons b default))⟩

def Expr.not : Expr bb → Expr bb := λ e, Expr.call Op.not (fin.cons e default)

instance has_coe_to_expr {b : Types} : has_coe (Ident b) (Expr b) := ⟨Expr.ident⟩

@[reducible] def Ident.to_expr {b} : Ident b → Expr b := Expr.ident
@[simp] lemma Expr_frame_coe_ident {b} (i : Ident b) : (i : Expr b).frame = {sigma.mk _ i} := rfl

/- Warning! Lean 3 uses zero, add, one instead of coe from ℕ for numerals -/
example : (3 : Expr nn) = 1 + 1 + 1 := rfl
example : (3 : Expr nn) ≠ Expr.lit 3 := by trivial
example : ((3 : ℕ) : Expr nn) = Expr.lit 3 := rfl

@[simp] lemma Expr.eval_lit {b : Types} (x : ExprVal b) (ctx : EContext) :
  (Expr.lit x).eval ctx = some x := rfl
@[simp] lemma Expr.lit_eq_nn (x : ℕ) : @Expr.lit nn x = ↑x := rfl
@[simp] lemma Expr.lit_eq_rr (x : R) : @Expr.lit rr x = ↑x := rfl
@[simp] lemma Expr.eval_lit_nn (x : ℕ) (ctx : EContext) :
  (x : Expr nn).eval ctx = some x := rfl
@[simp] lemma Expr.eval_lit_rr (x : R) (ctx : EContext) :
  (x : Expr rr).eval ctx = some x := rfl
@[simp] lemma Expr.eval_zero_nn (ctx : EContext) : (0 : Expr nn).eval ctx = some 0 := rfl
@[simp] lemma Expr.eval_zero_rr (ctx : EContext) : (0 : Expr rr).eval ctx = some 0 := rfl
@[simp] lemma Expr.eval_one_nn (ctx : EContext) : (1 : Expr nn).eval ctx = some 1 := rfl
@[simp] lemma Expr.eval_one_rr (ctx : EContext) : (1 : Expr rr).eval ctx = some 1 := rfl
@[simp] lemma Expr.eval_ident {b : Types} (x : Ident b) (ctx : EContext) :
  (Expr.ident x).eval ctx = some (ctx.store.get x) := rfl
@[simp] lemma Expr.eval_ident' {b : Types} (x : Ident b) (ctx : EContext) :
  (x : Expr b).eval ctx = some (ctx.store.get x) := rfl
@[simp] lemma Expr.eval_access {b : Types} (x : Ident b) (ind : Expr nn) (ctx : EContext) :
  (Expr.access x ind).eval ctx = ind.eval ctx >>= λ i, (ctx.heap.get x).nth i := rfl

@[simp] lemma Expr.eval_nadd (e₁ e₂ : Expr nn) (ctx : EContext) :
  (e₁ + e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n + m) :=
by { simp [add_nn_add, Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_radd (e₁ e₂ : Expr rr) (ctx : EContext) :
  (e₁ + e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n + m) :=
by { simp [add_rr_add, Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_nmul (e₁ e₂ : Expr nn) (ctx : EContext) :
  (e₁ * e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n * m) :=
by { simp [mul_nn_mul, Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_rmul (e₁ e₂ : Expr rr) (ctx : EContext) :
  (e₁ * e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n * m) :=
by { simp [mul_rr_mul, Expr.eval, fin.tuple_some] with functor_norm, refl, }

@[simp] lemma Expr.eval_lt (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪<⟫ e₂) = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n < m : bool) :=
by { simp [(⟪<⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_le (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪≤⟫ e₂) = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n ≤ m : bool) :=
by { simp [(⟪≤⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }
-- todo: consider less surprising evaluation order
@[simp] lemma Expr.eval_gt (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪>⟫ e₂) = (e₂.eval ctx) >>= λ n, e₁.eval ctx >>= λ m, some (n < m : bool) :=
by { simp [(⟪>⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }
@[simp] lemma Expr.eval_ge (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪≥⟫ e₂) = (e₂.eval ctx) >>= λ n, e₁.eval ctx >>= λ m, some (m ≥ n : bool) :=
by { simp [(⟪≥⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }

@[simp] lemma Expr.eval_eq (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪=⟫ e₂) = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n = m : bool) :=
by { simp [(⟪=⟫), Expr.eval, fin.tuple_some] with functor_norm, refl, }

@[simp] lemma Expr.eval_and (e₁ e₂ : Expr bb) (ctx : EContext) :
  (e₁ ⊓ e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n && m : bool) :=
by { simp [has_inf.inf, Expr.eval, fin.tuple_some] with functor_norm, refl }
@[simp] lemma Expr.eval_or  (e₁ e₂ : Expr bb) (ctx : EContext) :
  (e₁ ⊔ e₂).eval ctx = (e₁.eval ctx) >>= λ n, e₂.eval ctx >>= λ m, some (n || m : bool) :=
by { simp [has_sup.sup, Expr.eval, fin.tuple_some] with functor_norm, refl }

@[simp] lemma Expr.eval_ident_is_some {b : Types} {ctx : EContext} (i : Ident b) :
  (Expr.eval ctx (i : Expr b)).is_some := by simp

@[simp] lemma Expr.eval_not (e : Expr bb) (ctx : EContext) :
  e.not.eval ctx = (e.eval ctx) >>= λ v, some (bnot v) :=
by { simp [Expr.not, Expr.eval, fin.tuple_some] with functor_norm, refl, }

@[simp] def EContext.is_length {b : Types} (ctx : EContext) (arr : Ident b) (len : Ident nn) : Prop :=
(ctx.heap.get arr).length = ctx.store.get len

-- lemma get_arr_some {b : Types} {ctx : EContext} {arr : Ident b} {len : Expr nn}
--   (h₁ : ctx.is_length arr len) {i : ℕ} (h₂ : ∀ n, len.eval ctx = some n → i < n) :
--   ((ctx.get arr).get_arr i).is_some :=
-- by { }

-- @[simp] lemma get_arr_is_some_iff {b : Types} {ctx : EContext} {arr : Ident b} {i} :
--   ((ctx.heap.get arr).nth i).is_some ↔ i < (ctx.heap.get arr).length :=
-- by { simp, }

end Expr

parameter (R)
structure LoopBound :=
(frame : Frame)
(to_fun : EContext → ℕ)
(has_frame : true /- TODO: function.has_frame to_fun frame -/)

section LoopBound

instance : has_coe_to_fun LoopBound (λ _, EContext → ℕ) :=
⟨LoopBound.to_fun⟩
instance has_coe_from_nat : has_coe ℕ LoopBound := ⟨λ n, ⟨finset.empty, (λ _, n), true.intro⟩⟩

@[simp] lemma LoopBound.mk_apply (a f c x) : (LoopBound.mk a f c) x = f x := rfl  

end LoopBound

parameter (R)
inductive Prog
| skip : Prog
| store {b : Types} (dst : Ident b) (val : Expr b)
| store_arr {b : Types} (dst : Ident b) (ind : Expr nn) (val : Expr b)
| seq (a : Prog) (b : Prog)
| branch (cond : Expr bb) (a : Prog) (b : Prog)
| loop (n : LoopBound) (cond : Expr bb) (b : Prog)

section Prog

parameter {R}
def prog_repr [has_to_string R] : Prog → list string
| Prog.skip := ["pass"]
| (Prog.store dst val) := [(to_string dst) ++ " := " ++ (to_string val)]
| (Prog.store_arr dst ind val) := [(to_string dst) ++ ("[" ++ to_string ind ++ "]") ++ " := " ++ (to_string val)]
| (Prog.seq a b) := (prog_repr a) ++ (prog_repr b)
| (Prog.branch c a b) := ["if " ++ (to_string c) ++ ":"]
    ++ (prog_repr a).map (λ s, "  " ++ s)
    ++ ["else:"]
    ++ (prog_repr b).map (λ s, "  " ++ s)
| (Prog.loop n cond b) := ["while " ++ (to_string cond) ++ ":"]
    ++ (prog_repr b).map (λ s, "  " ++ s)

instance [has_to_string R] : has_to_string Prog :=
⟨λ p, "\n".intercalate (prog_repr p)⟩

def Prog.eval : Prog → EContext → option EContext
| Prog.skip ctx := some ctx
| (Prog.store dst val) ctx := (val.eval ctx) >>= λ r, some (ctx.update dst r)
| (Prog.store_arr dst ind val) ctx := ind.eval ctx >>= λ i, val.eval ctx >>= λ v,
  if i < (ctx.heap.get dst).length then some (ctx.update_arr dst i v) else none
| (Prog.seq a b) ctx := (a.eval ctx) >>= b.eval
| (Prog.branch condition a b) ctx := (Expr.eval ctx condition) >>= λ c : bool, cond c (a.eval ctx) (b.eval ctx)
| (Prog.loop n c b) ctx := (iterate_while b.eval
      (λ ctx : EContext, c.eval ctx)
      (n ctx)) ctx

@[simp] def Prog.frame : Prog → Frame
| Prog.skip := ∅
| (Prog.store dst val) := insert (sigma.mk _ dst) val.frame
| (Prog.store_arr dst ind val) := insert (sigma.mk _ dst) (ind.frame ∪ val.frame)
| (Prog.seq a b) := a.frame ∪ b.frame
| (Prog.branch c a b) := c.frame ∪ a.frame ∪ b.frame
| (Prog.loop n c b) := c.frame ∪ b.frame  

@[simp] lemma Prog.eval_skip_is_some (ctx : EContext) : (Prog.skip.eval ctx).is_some := by simp [Prog.eval]
@[simp] lemma Prog.store_is_some_iff {b : Types} {ctx : EContext} {dst : Ident b} {val : Expr b} :
  ((Prog.store dst val).eval ctx).is_some ↔ (val.eval ctx).is_some :=
by simp [Prog.eval]

end Prog

local infixr ` <;> `:1 := Prog.seq
local notation a ` ::= `:20 c := Prog.store a c
local notation a ` ⟬ `:9000 i ` ⟭ ` ` ::= `:20 c := Prog.store_arr a i c
local notation x ` ⟬ `:9000 i ` ⟭ ` := Expr.access x i

class TRAble (α : Type) (β : out_param Type) :=
(tr : EContext → α →. /- partial function -/ β)

open TRAble (tr)

@[simps]
instance tr_expr_nn : TRAble (Expr nn) ℕ :=
{ tr := λ ctx e, e.eval ctx }

@[simps]
instance tr_expr_nn' : TRAble (Expr nn) (ExprVal nn) := tr_expr_nn

@[simps]
instance tr_expr_rr : TRAble (Expr rr) R :=
{ tr := λ ctx e, e.eval ctx }

section stream

parameter (R)
structure BoundedStreamGen (ι α : Type) :=
(current : ι)
(value : α)
(ready : Expr bb)
(next : Prog)
(valid : Expr bb)
(bound : LoopBound)
(initialize : Prog)
(ctx_inv : EContext → Prop)

parameter {R}
variables {ι α ι' β : Type}

@[ext]
lemma BoundedStreamGen.ext {s₁ s₂ : BoundedStreamGen ι α} (h₁ : s₁.current = s₂.current)
  (h₂ : s₁.value = s₂.value) (h₃ : s₁.ready = s₂.ready) (h₄ : s₁.next = s₂.next) (h₅ : s₁.valid = s₂.valid)
  (h₆ : s₁.bound = s₂.bound) (h₇ : s₁.initialize = s₂.initialize) (h₈ : s₁.ctx_inv = s₂.ctx_inv) : s₁ = s₂ :=
by { cases s₁, cases s₂, dsimp only at *, subst_vars, }

section functorality

@[simps]
instance : bifunctor BoundedStreamGen :=
{ bimap := λ _ _ _ _ f g s, { s with current := f s.current, value := g s.value } }

instance : is_lawful_bifunctor BoundedStreamGen :=
{ id_bimap := by { intros, ext; simp, },
  bimap_bimap := by { intros, ext; simp, } }

end functorality

def BoundedStreamGen.inv_valid_at (s : BoundedStreamGen ι α) (ctx : EContext) : Prop :=
s.ctx_inv ctx ∧ s.valid.eval ctx = some tt

def BoundedStreamGen.ready_at (s : BoundedStreamGen ι α) (ctx : EContext) : Prop :=
s.inv_valid_at ctx ∧ s.ready.eval ctx = some tt

@[simp] lemma BoundedStreamGen.bimap_inv_valid_at {s : BoundedStreamGen ι α} {ctx : EContext} (f : ι → ι') (g : α → β) :
  (bimap f g s).inv_valid_at ctx ↔ s.inv_valid_at ctx := iff.rfl

@[simp] lemma BoundedStreamGen.ready_inv_valid_at {s : BoundedStreamGen ι α} {ctx : EContext} (f : ι → ι') (g : α → β) :
  (bimap f g s).ready_at ctx ↔ s.ready_at ctx := iff.rfl

def preserves (s : BoundedStreamGen ι α) (ctx : EContext) (p : EContext → Prop) : Prop :=
p ctx → ∀ {c}, s.next.eval ctx = some c → p c

section preserves
variables {s : BoundedStreamGen ι α} {ctx : EContext} {p₁ p₂ : EContext → Prop}
lemma preserves.and (h₀ : preserves s ctx p₁) (h₁ : preserves s ctx p₂) : (preserves s ctx (λ c, p₁ c ∧ p₂ c)) :=
by { simp only [preserves] at *, tauto, }

lemma preserves.is_length {b : Types} (v : Ident b) (e : Ident nn)  (h : (sigma.mk nn e) ∉ s.next.frame) :
  preserves s ctx (λ c, c.is_length v e) := sorry

end preserves

structure is_defined [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α) (ctx : EContext) : Prop :=
(hvalid : s.ctx_inv ctx → (s.valid.eval ctx).is_some)
(hready : s.inv_valid_at ctx → (s.ready.eval ctx).is_some)
(hnext : s.inv_valid_at ctx → (s.next.eval ctx).is_some)
(hcurr : s.inv_valid_at ctx → (tr ctx s.current).dom)
(hval : s.ready_at ctx → (tr ctx s.value).dom)
(hstep : preserves s ctx s.ctx_inv)

structure is_defined_at [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α) (ctx : EContext) : Prop :=
(to_is_def : ∀ c, is_defined s c)
(inv : s.ctx_inv ctx)
(hinit : (s.initialize.eval ctx).is_some)

@[simps]
def BoundedStreamGen.to_stream_of_is_defined_aux  [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α)
  (hs : ∀ ctx, is_defined s ctx) : Stream EContext ι' β :=
{ valid := s.inv_valid_at,
  ready := s.ready_at,
  next := λ ctx h, option.get ((hs ctx).hnext h),
  index := λ ctx h, part.get _ ((hs ctx).hcurr h),
  value := λ ctx h, part.get _ ((hs ctx).hval h) }

@[simps]
def BoundedStreamGen.to_stream_of_is_defined [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α)
   (ctx₀ : EContext) (hs : is_defined_at s ctx₀) : StreamExec EContext ι' β :=
{ stream := s.to_stream_of_is_defined_aux hs.to_is_def,
  bound := s.bound ctx₀,
  state := option.get hs.hinit }

instance eval_stream [TRAble ι ι'] [TRAble α β] : TRAble (BoundedStreamGen ι α) (StreamExec EContext ι' β) :=
{ tr := λ ctx s, ⟨_, s.to_stream_of_is_defined ctx⟩ }

@[simp] lemma eval_stream_is_some_iff [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α) {c₀} :
  (tr c₀ s).dom ↔ is_defined_at s c₀ := iff.rfl

section translate
open_locale classical

structure tr_to_stream {σ'} [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α)
  (t : Stream σ' ι' β) (f : EContext → σ') (ctx : EContext) : Prop :=
(hvalid : s.ctx_inv ctx → s.valid.eval ctx = some (t.valid (f ctx)))
(hready : s.inv_valid_at ctx → s.ready.eval ctx = some (t.ready (f ctx)))
(hnext : s.inv_valid_at ctx → ∀ h, (f <$> s.next.eval ctx) = some (t.next (f ctx) h))
(hcurr : s.inv_valid_at ctx → ∀ h, tr ctx s.current = part.some (t.index (f ctx) h))
(hval : s.ready_at ctx → ∀ h, tr ctx s.value = part.some (t.value (f ctx) h))
(hstep : preserves s ctx s.ctx_inv)

structure tr_to {σ'} [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α)
  (t : StreamExec σ' ι' β) (f : EContext → σ') (ctx : EContext) : Prop :=
(to_stream : ∀ c, tr_to_stream s t.stream f c)
(inv : s.ctx_inv ctx)
(hinit : (f <$> s.initialize.eval ctx) = some t.state)
(hbound : s.bound ctx = t.bound)

lemma tr_to_stream.is_def {σ'} [TRAble ι ι'] [TRAble α β] {s : BoundedStreamGen ι α}
  {t : Stream σ' ι' β} {f : EContext → σ'} {c : EContext} (h : tr_to_stream s t f c) :
  is_defined s c :=
{ hvalid := λ H, by simp [h.hvalid H],
  hready := λ H, by simp [h.hready H],
  hnext := λ H, by { have := h.hnext H (by simpa [H.2] using h.hvalid H.1), simpa using congr_arg option.is_some this, },
  hcurr := λ H, by { rw h.hcurr H (by simpa [H.2] using h.hvalid H.1), trivial, },
  hval := λ H, by { rw h.hval H (by simpa [H.2] using h.hready H.1), trivial, },
  hstep := h.hstep }

lemma tr_to.is_def_at {σ'} [TRAble ι ι'] [TRAble α β] {s : BoundedStreamGen ι α}
  {t : StreamExec σ' ι' β} {f : EContext → σ'} {c : EContext} (h : tr_to s t f c) :
  is_defined_at s c :=
{ to_is_def := λ c, (h.to_stream c).is_def,
  inv := h.inv,
  hinit := by simpa using congr_arg option.is_some h.hinit }

variables {σ' : Type} [TRAble ι ι'] [TRAble α β] {s : BoundedStreamGen ι α}
  {t : Stream σ' ι' β} {f : EContext → σ'} {ctx : EContext}

lemma tr_to_stream.inv_valid_at_iff (h : tr_to_stream s t f ctx) (hctx : s.ctx_inv ctx) : s.inv_valid_at ctx ↔ t.valid (f ctx) :=
by simp [BoundedStreamGen.inv_valid_at, hctx, h.hvalid hctx]

lemma tr_to_stream.ready_at_iff (h : tr_to_stream s t f ctx) (hctx : s.ctx_inv ctx) : 
  s.ready_at ctx ↔ t.valid (f ctx) ∧ t.ready (f ctx) :=
by { simp [BoundedStreamGen.ready_at, h.inv_valid_at_iff hctx], intro hv, simp [h.hready (by rwa h.inv_valid_at_iff hctx)], }

variables [add_zero_class β] (h : ∀ c, tr_to_stream s t f c)

lemma tr_to_stream.eval₀ (hctx : s.ctx_inv ctx) (h₀ h₁) : 
  (s.to_stream_of_is_defined_aux (λ c, (h c).is_def)).eval₀ ctx h₀ =
  t.eval₀ (f ctx) h₁ :=
begin
  simp [Stream.eval₀, (h ctx).ready_at_iff hctx, h₁],
  split_ifs with h₂, swap, { /- If both are not ready -/ refl, },
  congr; rw part.get_eq_iff_eq_some,
  -- Show that index = index
  { rw (h ctx).hcurr (by rwa [(h ctx).inv_valid_at_iff hctx]) h₁, },
  -- Show that value = value
  { rw (h ctx).hval (by simp [(h ctx).ready_at_iff hctx, h₁, h₂]) h₂, },
end

lemma tr_to_stream.eval_steps_eq (hctx : s.ctx_inv ctx) (n : ℕ) :
  (s.to_stream_of_is_defined_aux (λ c, (h c).is_def)).eval_steps n ctx = 
  t.eval_steps n (f ctx) :=
begin
  induction n with n ih generalizing ctx, { refl, },
  simp [StreamExec.valid, (h ctx).inv_valid_at_iff hctx],
  split_ifs, swap, { refl, },
  congr' 1, swap, { rw tr_to_stream.eval₀ h hctx, },
  rw ih ((h ctx).hstep hctx (option.some_get _).symm),
  have := (h ctx).hnext (by rwa (h ctx).inv_valid_at_iff hctx) (by assumption),
  simp at this, obtain ⟨a, ha₁, ha₂⟩ := this, simp [ha₁, ha₂],
end

lemma tr_to.eval_finsupp_eq {t : StreamExec σ' ι' β} (h : tr_to s t f ctx) :
  ((tr ctx s).get h.is_def_at).eval = t.eval :=
begin
  have := h.hinit, simp at this,
  obtain ⟨cinit, hc₁, hc₂⟩ := this, 
  have : s.ctx_inv cinit := sorry, -- TODO: Initialize preserves ctx_inv
  simp [StreamExec.eval, tr, h.hbound, hc₁, hc₂, tr_to_stream.eval_steps_eq h.to_stream this],
end

lemma tr_to.eval_finsupp_eq' {t : StreamExec σ' ι' β} (h : tr_to s t f ctx) :
  ∃ s' : StreamExec _ _ _, s' ∈ tr ctx s ∧ s'.eval = t.eval :=
⟨(tr ctx s).get h.is_def_at, part.get_mem _, h.eval_finsupp_eq⟩

end translate

instance eval_unit : TRAble unit unit := ⟨λ _, part.some⟩
@[simp] lemma eval_unit_dom (c) : (tr c ()).dom := trivial

def singleton (x : α) : BoundedStreamGen unit α := sorry

def range_nn (n : Expr nn) : BoundedStreamGen (Expr nn) (Expr nn) := sorry

def range_rr (n : Expr nn) : BoundedStreamGen (Expr nn) (Expr rr) := sorry

def externSparseVec (scratch : NameSpace) : BoundedStreamGen (Expr nn) (Expr rr) :=
let i : Ident nn := scratch∷Vars.i,
    len : Ident nn := reserved∷Vars.len,
    inds : Ident nn := reserved∷ind₀,
    vals : Ident rr := reserved∷vals in
{ current := inds⟬i⟭,
  value := vals⟬i⟭,
  ready := Expr.lit tt,
  next := i ::= i + 1,
  valid := (i : Expr nn) ⟪<⟫ len,
  bound := ⟨default, λ ctx, ctx.store.get len, /- TODO: Frame -/ trivial⟩,
  initialize := i ::= 0,
  ctx_inv := λ ctx, ctx.is_length inds len ∧ ctx.is_length vals len }

def contract (x : BoundedStreamGen ι α) : BoundedStreamGen unit α :=
default <$₁> x

section functor_is_defined
variables {ι₁ ι₁' ι₂ ι₂' α' β' : Type} [TRAble ι₁ ι₂] [TRAble α β]
  {x : BoundedStreamGen ι₁ α} {c : EContext} (hx : is_defined x c)
  (f : ι₁ → ι₁') (g : α → α')
include hx

@[simp] lemma bimap_is_defined [TRAble ι₁' ι₂'] [TRAble α' β'] :
  is_defined (bifunctor.bimap f g x) c ↔ ((x.inv_valid_at c → (tr c (f x.current)).dom) ∧ (x.ready_at c → (tr c (g x.value)).dom)) :=
⟨λ ⟨hv, hr, hn, hc, hl, hs⟩, ⟨hc, hl⟩, λ ⟨H₁, H₂⟩, ⟨hx.hvalid, hx.hready, hx.hnext, H₁, H₂, hx.hstep⟩⟩

@[simp] lemma imap_is_defined [TRAble ι₁' ι₂'] :
  is_defined (f <$₁> x) c ↔ (x.inv_valid_at c → (tr c (f x.current)).dom) :=
by { rw bimap_is_defined hx, have := hx.hval, simp [imp_iff_distrib], tauto, }

@[simp] lemma vmap_is_defined [TRAble α' β'] :
  is_defined (g <$₂> x) c ↔ (x.ready_at c → (tr c (g x.value)).dom) :=
by { rw bimap_is_defined hx, have := hx.hcurr, simp [imp_iff_distrib], tauto, }

end functor_is_defined

lemma contract_spec [TRAble ι ι'] [TRAble α β] (x : BoundedStreamGen ι α)
  (ctx : EContext) (h : is_defined_at x ctx) :
  tr ctx (contract x) = part.some (contract_stream ((tr ctx x).get h)) :=
by { rw ← part.get_eq_iff_eq_some, swap, { refine ⟨_, h.inv, h.hinit⟩, simp [contract, h.to_is_def], }, refl, }

lemma contract_spec' [TRAble ι ι'] [TRAble α β] {ctx : EContext} (x : BoundedStreamGen ι α) 
  (hctx : x.ctx_inv ctx) (motive : StreamExec EContext unit β → Prop)
  (hyp : ∃ c, c ∈ tr ctx x ∧ motive (contract_stream c)) :
  ∃ c, c ∈ tr ctx (contract x) ∧ motive c :=
begin
  rcases hyp with ⟨c, hc₁, hc₂⟩,
  refine ⟨_, _, hc₂⟩,
  rw contract_spec _ _ (part.dom_iff_mem.mpr ⟨_, hc₁⟩),
  simp [part.eq_some_iff.mpr hc₁],
end

section sparse_vectors
open NameSpace (reserved) Vars (ind₀ vals len)

lemma externSparseVec_has_tr_to_stream (scratch : NameSpace) (c : EContext) :
  tr_to_stream (externSparseVec scratch) primitives.externSparseVec_stream 
    (λ ctx, ⟨ctx.store.get scratch∷ₙVars.i, ctx.heap.get reserved∷ₙind₀, ctx.heap.get reserved∷ᵣvals⟩) c :=
{ hvalid := by { simp [externSparseVec, primitives.externSparseVec_stream], intros a b, simp [a], },
  hready := by { simp [externSparseVec, primitives.externSparseVec_stream, BoundedStreamGen.inv_valid_at], intros a b, simp [b], },
  hnext := λ _ _, by { simp [externSparseVec, primitives.externSparseVec_stream, Prog.eval], },
  hcurr := λ _ _, by { simp [externSparseVec, primitives.externSparseVec_stream, list.some_nth_le_eq], },
  hval := λ _ _, by { simp [externSparseVec, primitives.externSparseVec_stream, list.some_nth_le_eq], },
  hstep := by { apply preserves.and; apply preserves.is_length; simp [externSparseVec, has_add.add, fin.forall_fin_two], }, }

lemma externSparseVec_has_tr (scratch : NameSpace) (c : EContext) 
  (hc : (externSparseVec scratch).ctx_inv c) :
  tr_to (externSparseVec scratch) (primitives.externSparseVec (c.heap.get reserved∷ₙind₀) (c.heap.get reserved∷ᵣvals)) 
    (λ ctx, ⟨ctx.store.get scratch∷ₙVars.i, ctx.heap.get reserved∷ₙind₀, ctx.heap.get reserved∷ᵣvals⟩) c :=
{ to_stream := λ c', (externSparseVec_has_tr_to_stream scratch c'),
  inv := hc,
  hinit := by simp [externSparseVec, Prog.eval, primitives.externSparseVec],
  hbound := by { simp [externSparseVec] at hc, simp [externSparseVec, primitives.externSparseVec, hc.1], } }

lemma externSparseVec_is_defined_at (scratch : NameSpace) (c : EContext) (hc : (externSparseVec scratch).ctx_inv c) :
  is_defined_at (externSparseVec scratch) c := (externSparseVec_has_tr scratch c hc).is_def_at

lemma externSparseVec_spec (scratch : NameSpace) (c : EContext)
  (hc : (externSparseVec scratch).ctx_inv c) :
  ∃ c' : StreamExec EContext ℕ R, c' ∈ tr c (externSparseVec scratch) ∧ 
  c'.eval = (list.zip_with finsupp.single (c.heap.get reserved∷ₙind₀) (c.heap.get reserved∷ᵣvals)).sum :=
begin
  obtain ⟨c', hc₁, hc₂⟩ := (externSparseVec_has_tr scratch c hc).eval_finsupp_eq',
  exact ⟨c', hc₁, by simp [hc₂]⟩,
end

end sparse_vectors

def compile_scalar (x : BoundedStreamGen unit (Expr rr)) : Prog :=
let out : Ident rr := reserved∷output in
out ::= 0 <;>
x.initialize <;>
Prog.loop x.bound x.valid $
  Prog.branch x.ready 
    (out ::= out + x.value) 
    Prog.skip <;>
  x.next


section compile_sound

def BoundedStreamGen.body (x : BoundedStreamGen unit (Expr rr)) : Prog :=
Prog.branch x.ready (reserved∷ᵣoutput ::= reserved∷ᵣoutput + x.value) Prog.skip <;> 
x.next

structure BoundedStreamGen.compile_invariant (x : BoundedStreamGen unit (Expr rr)) 
  (s : Stream EContext unit R) (ctx₀ : EContext) (ctx : EContext) (i : ℕ) : Prop :=
(hout : ctx.store.get reserved∷ᵣoutput = s.eval_steps i ctx₀ ())
(hi : i ≤ x.bound ctx₀)
(hleft : s.bound_valid_aux ((x.bound ctx₀) - i) ctx)


lemma compile_scalar_sound (x : BoundedStreamGen unit (Expr rr)) (ctx : EContext)
  (h : is_defined_at x ctx) :
  ∃ (c' : EContext), 
    (compile_scalar x).eval ctx = some c' ∧
    c'.store.get (NameSpace.reserved∷Vars.output : Ident rr) = ((tr ctx x).get h).eval () :=
begin
  simp [compile_scalar, Prog.eval],
  set ctx' := ctx.update reserved∷ᵣoutput 0,
  have : (x.initialize.eval ctx').is_some := sorry, -- This is similar to `h.hinit`, but requires some frame issues to be resolved
  rw option.is_some_iff_exists at this, cases this with ctx₂ hctx₂,
  simp only [hctx₂, exists_eq_left'],

  sorry,
end



end compile_sound

end stream

end compiler

section examples
open TRAble (tr)

parameters [add_comm_monoid R] [has_one R] [has_mul R]

def sum_vec (scratch : NameSpace) : BoundedStreamGen unit (Expr rr) :=
contract (externSparseVec scratch)

lemma sum_vec_spec (scratch : NameSpace) (ctx : EContext) (hctx : (externSparseVec scratch).ctx_inv ctx) :
  ∃ (s : StreamExec EContext unit R), s ∈ tr ctx (sum_vec scratch) ∧
  s.eval = finsupp.single () (ctx.heap.get (NameSpace.reserved∷Vars.vals : Ident rr)).sum :=
begin
  apply contract_spec' _ hctx,
  simp,
  obtain ⟨c, hc₁, hc₂⟩ := externSparseVec_spec scratch _ hctx, refine ⟨c, hc₁, _⟩, rw hc₂,
  -- TODO: Up to here should be automated
  have : (ctx.heap.get reserved∷ₙind₀).length = (ctx.heap.get reserved∷ᵣvals).length,
  { simp [externSparseVec] at hctx, rw [hctx.1, hctx.2], },
  simp [← list.sum_hom, list.map_zip_with], rw list.zip_with_snd this.symm.le,
end

end examples

-- Final theorem will be something like:
-- ∀ (x : BoundedStreamGen ι α) [TRAble ι → ι'] [TRAble α → β] [FinsuppEval (StreamExec EContext ι' β)]
--  (hind₁ : ι compiles correctly) (hind₂ : α compiles correctly) : BoundedStreamGen ι α compiles correctly


end

section examples
open Types

notation ` Σ_c ` := contract
@[derive [add_comm_monoid, has_one, has_mul, has_to_string], irreducible]
def R := ℤ
abbreviation compile := @compile_scalar R

def sum_vec' : BoundedStreamGen R unit (Expr R rr) :=
Σ_c (externSparseVec (fresh ∅))

#eval do io.print_ln (compile sum_vec')

end examples
