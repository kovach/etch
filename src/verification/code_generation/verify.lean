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
import verification.code_generation.vars
import verification.misc
import verification.semantics.stream
import data.pfun

section

parameters (R : Type)
open Types (nn rr bb)
open NameSpace (reserved)
open Vars (ind₀ vals len output)

section compiler

parameters [add_comm_monoid_with_one R] [has_mul R]

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
| _ cast_r := λ args, (coe : ℕ → R) (show ℕ, from args 0)

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

def Expr.eval (ctx : EContext) : ∀ {b}, Expr b → ExprVal b
| _ (Expr.lit r) := r
| b (Expr.ident x) := ctx.store.get x
| b (Expr.access x i) := (ctx.heap.get x).inth i.eval
| _ (Expr.call o args) := o.eval (λ i, (args i).eval)
| _ (Expr.ternary c e₁ e₂) := cond c.eval e₁.eval e₂.eval

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
{ eq := λ a b, Expr.call Op.nat_eq (by exact fin.cons a (fin.cons b fin.elim0)),
  lt := λ a b, Expr.call Op.lt (by exact fin.cons a (fin.cons b fin.elim0)),
  le := λ a b, Expr.call Op.le (by exact fin.cons a (fin.cons b fin.elim0)),
  ge := λ a b, Expr.call Op.le (by exact fin.cons b (fin.cons a fin.elim0)),
  gt := λ a b, Expr.call Op.lt (by exact fin.cons b (fin.cons a fin.elim0)) }



#exit
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
  (Expr.lit x).eval ctx = x := rfl
@[simp] lemma Expr.lit_eq_nn (x : ℕ) : @Expr.lit nn x = ↑x := rfl
@[simp] lemma Expr.lit_eq_rr (x : R) : @Expr.lit rr x = ↑x := rfl
@[simp] lemma Expr.eval_lit_nn (x : ℕ) (ctx : EContext) :
  (x : Expr nn).eval ctx = x := rfl
@[simp] lemma Expr.eval_lit_rr (x : R) (ctx : EContext) :
  (x : Expr rr).eval ctx = x := rfl
@[simp] lemma Expr.eval_zero_nn (ctx : EContext) : (0 : Expr nn).eval ctx = 0 := rfl
@[simp] lemma Expr.eval_zero_rr (ctx : EContext) : (0 : Expr rr).eval ctx = 0 := rfl
@[simp] lemma Expr.eval_one_nn (ctx : EContext) : (1 : Expr nn).eval ctx = 1 := rfl
@[simp] lemma Expr.eval_one_rr (ctx : EContext) : (1 : Expr rr).eval ctx = 1 := rfl
@[simp] lemma Expr.eval_ident {b : Types} (x : Ident b) (ctx : EContext) :
  (Expr.ident x).eval ctx = ctx.store.get x := rfl
@[simp] lemma Expr.eval_ident' {b : Types} (x : Ident b) (ctx : EContext) :
  (x : Expr b).eval ctx = ctx.store.get x := rfl
@[simp] lemma Expr.eval_access {b : Types} (x : Ident b) (ind : Expr nn) (ctx : EContext) :
  (Expr.access x ind).eval ctx = (ctx.heap.get x).inth (ind.eval ctx ) := rfl

-- TODO: Derive automatically?
@[simp] lemma Expr.eval_nadd (e₁ e₂ : Expr nn) (ctx : EContext) :
  (e₁ + e₂).eval ctx = (e₁.eval ctx) + (e₂.eval ctx) :=
by simp [add_nn_add, Expr.eval]
@[simp] lemma Expr.eval_radd (e₁ e₂ : Expr rr) (ctx : EContext) :
  (e₁ + e₂).eval ctx = e₁.eval ctx + e₂.eval ctx :=
by simp [add_rr_add, Expr.eval]
@[simp] lemma Expr.frame_nadd (e₁ e₂ : Expr nn) : (e₁ + e₂).frame = e₁.frame ∪ e₂.frame :=
by { simp [add_nn_add], ext, simp [fin.exists_fin_two], }

@[simp] lemma Expr.eval_nmul (e₁ e₂ : Expr nn) (ctx : EContext) :
  (e₁ * e₂).eval ctx = (e₁.eval ctx) * (e₂.eval ctx) :=
by simp [mul_nn_mul, Expr.eval]
@[simp] lemma Expr.eval_rmul (e₁ e₂ : Expr rr) (ctx : EContext) :
  (e₁ * e₂).eval ctx = (e₁.eval ctx) * (e₂.eval ctx) :=
by simp [mul_rr_mul, Expr.eval]

@[simp] lemma Expr.eval_lt (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪<⟫ e₂) = (e₁.eval ctx < e₂.eval ctx : bool) :=
by simp [(⟪<⟫), Expr.eval]
@[simp] lemma Expr.eval_le (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪≤⟫ e₂) = (e₁.eval ctx ≤ e₂.eval ctx : bool) :=
by simp [(⟪≤⟫), Expr.eval]
@[simp] lemma Expr.eval_gt (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪>⟫ e₂) = (e₂.eval ctx < e₁.eval ctx : bool) :=
by simp [(⟪>⟫), Expr.eval]
@[simp] lemma Expr.eval_ge (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪≥⟫ e₂) = (e₂.eval ctx ≤ e₁.eval ctx : bool) :=
by { simp [(⟪≥⟫), Expr.eval] }

@[simp] lemma Expr.eval_eq (e₁ e₂ : Expr nn) (ctx : EContext) :
  Expr.eval ctx (e₁ ⟪=⟫ e₂) = (e₁.eval ctx = e₂.eval ctx : bool) :=
by simp [(⟪=⟫), Expr.eval]
@[simp] lemma Expr.eval_and (e₁ e₂ : Expr bb) (ctx : EContext) :
  (e₁ ⊓ e₂).eval ctx = e₁.eval ctx && e₂.eval ctx :=
by { simp [has_inf.inf, Expr.eval] }
@[simp] lemma Expr.eval_or  (e₁ e₂ : Expr bb) (ctx : EContext) :
  (e₁ ⊔ e₂).eval ctx = e₁.eval ctx || e₂.eval ctx :=
by { simp [has_sup.sup, Expr.eval] }

@[simp] lemma Expr.eval_not (e : Expr bb) (ctx : EContext) :
  e.not.eval ctx = !(e.eval ctx) :=
by { simp [Expr.not, Expr.eval] }

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

@[simp] def Prog.eval : Prog → EContext → EContext
| Prog.skip ctx := ctx
| (Prog.store dst val) ctx := ctx.update dst (val.eval ctx)
| (Prog.store_arr dst ind val) ctx :=
  let i : ℕ := ind.eval ctx in
  if i < (ctx.heap.get dst).length then ctx.update_arr dst i (val.eval ctx) else ctx
| (Prog.seq a b) ctx := b.eval (a.eval ctx)
| (Prog.branch condition a b) ctx := cond (condition.eval ctx) (a.eval ctx) (b.eval ctx)
| (Prog.loop n c b) ctx :=
(λ ctx, cond (c.eval ctx) (b.eval ctx) ctx)^[(n ctx)] ctx

@[simp] def Prog.frame : Prog → Frame
| Prog.skip := ∅
| (Prog.store dst val) := insert (sigma.mk _ dst) val.frame
| (Prog.store_arr dst ind val) := insert (sigma.mk _ dst) (ind.frame ∪ val.frame)
| (Prog.seq a b) := a.frame ∪ b.frame
| (Prog.branch c a b) := c.frame ∪ a.frame ∪ b.frame
| (Prog.loop n c b) := c.frame ∪ b.frame

end Prog

local infixr ` <;> `:1 := Prog.seq
local notation a ` ::= `:20 c := Prog.store a c
local notation a ` ⟬ `:9000 i ` ⟭ ` ` ::= `:20 c := Prog.store_arr a i c
local notation x ` ⟬ `:9000 i ` ⟭ ` := Expr.access x i

class TRAble (α : Type*) (β : out_param Type*) :=
(tr : EContext → α → β)

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

parameter {R}
variables {ι α ι' β : Type}

@[ext]
lemma BoundedStreamGen.ext {s₁ s₂ : BoundedStreamGen ι α} (h₁ : s₁.current = s₂.current)
  (h₂ : s₁.value = s₂.value) (h₃ : s₁.ready = s₂.ready) (h₄ : s₁.next = s₂.next) (h₅ : s₁.valid = s₂.valid)
  (h₆ : s₁.bound = s₂.bound) (h₇ : s₁.initialize = s₂.initialize) : s₁ = s₂ :=
by { cases s₁, cases s₂, dsimp only at *, subst_vars, }

section functorality

@[simps]
instance : bifunctor BoundedStreamGen :=
{ bimap := λ _ _ _ _ f g s, { s with current := f s.current, value := g s.value } }

instance : is_lawful_bifunctor BoundedStreamGen :=
{ id_bimap := by { intros, ext; simp, },
  bimap_bimap := by { intros, ext; simp, } }

end functorality

@[simps]
def BoundedStreamGen.to_stream_aux  [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α) :
  Stream ι' β :=
{ σ := EContext,
  valid := λ ctx, s.valid.eval ctx,
  ready := λ ctx, s.valid.eval ctx && s.ready.eval ctx,
  next := λ ctx h, s.next.eval ctx,
  index := λ ctx h, tr ctx s.current,
  value := λ ctx h, tr ctx s.value }

@[simps]
def BoundedStreamGen.to_stream [TRAble ι ι'] [TRAble α β] (ctx₀ : EContext) (s : BoundedStreamGen ι α) : StreamExec ι' β :=
{ stream := s.to_stream_aux,
  bound := s.bound (s.initialize.eval ctx₀),
  state := s.initialize.eval ctx₀,
  bound_valid := sorry, }

instance eval_stream [TRAble ι ι'] [TRAble α β] : TRAble (BoundedStreamGen ι α) (StreamExec ι' β) :=
{ tr := BoundedStreamGen.to_stream }

section translate
open_locale classical

structure tr_to_stream [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α)
  (t : Stream ι' β) (f : EContext → t.σ) (ctx : EContext) : Prop :=
(hvalid : s.valid.eval ctx ↔ t.valid (f ctx))
(hready' : s.valid.eval ctx → t.valid (f ctx) → (s.ready.eval ctx ↔ t.ready (f ctx)))
(hnext : s.valid.eval ctx → ∀ h, f (s.next.eval ctx) = t.next (f ctx) h)
(hcurr : s.valid.eval ctx → ∀ h, tr ctx s.current = t.index (f ctx) h)
(hval : s.valid.eval ctx → s.ready.eval ctx → ∀ h, tr ctx s.value = t.value (f ctx) h)

lemma tr_to_stream.hready [TRAble ι ι'] [TRAble α β] {s : BoundedStreamGen ι α}
  {t : Stream ι' β} {f : EContext → t.σ} {ctx : EContext} (h : tr_to_stream s t f ctx)
  (hv : t.valid (f ctx)) : s.ready.eval ctx ↔ t.ready (f ctx) := h.hready' (h.hvalid.mpr hv) hv

@[simp] def EContext.is_length {b : Types} (ctx : EContext) (arr : Ident b) (len : Ident nn) : Prop :=
(ctx.heap.get arr).length = ctx.store.get len

def preserves (next : Prog) (inv : EContext → Prop) : Prop :=
∀ {c}, inv c → inv (next.eval c)

@[mk_iff]
structure EContext.unmodified (inv : NameSpace) (c₀ : EContext) (ctx : EContext) : Prop :=
(h : ∀ {b : Types} (v : Vars), ctx.heap.get (inv∷v : Ident b) = c₀.heap.get inv∷v)
(s : ∀ {b : Types} (v : Vars), ctx.store.get (inv∷v : Ident b) = c₀.store.get inv∷v)

@[refl] lemma EContext.unmodified.rfl (inv : NameSpace) (c₀ : EContext) :
  c₀.unmodified inv c₀ :=
⟨λ _ v, rfl, λ _ v, rfl⟩

section preserves
variables {next : Prog} {ctx : EContext} {p₁ p₂ : EContext → Prop}
lemma preserves.and (h₀ : preserves next p₁) (h₁ : preserves next p₂) : (preserves next (λ c, p₁ c ∧ p₂ c)) :=
by { rw [preserves] at *, tauto, }

--#check
lemma preserves.unmodified (c₀ : EContext) {b} {inv : Ident b}
(h : {⟨_, inv⟩} # next.frame) :
  preserves next (c₀.unmodified inv) := sorry -- FOOTPRINT: nothing in `inv` is modified

lemma preserves.unmodified (c₀ : EContext) {inv : NameSpace} (h : inv ∉ next.frame.image (λ x : Σ b, Ident b, x.2.ns)) :
  preserves next (c₀.unmodified inv) := sorry -- FOOTPRINT: nothing in `inv` is modified

lemma preserves.is_length {b : Types} (v : Ident b) (e : Ident nn)  (h : (sigma.mk _ e) ∉ next.frame) :
  preserves next (λ c, c.is_length v e) := sorry -- FOOTPRINT: If `e` (length variable) is not modified, this is preserved

end preserves

structure tr_to [TRAble ι ι'] [TRAble α β] (s : BoundedStreamGen ι α)
  (t : StreamExec ι' β) (f : EContext → t.stream.σ) (ctx : EContext) : Type :=
(inv : EContext → Prop)
(to_stream : ∀ c, inv c → tr_to_stream s t.stream f c)
(hinit : f (s.initialize.eval ctx) = t.state)
(init_inv : inv (s.initialize.eval ctx))
(hbound : s.bound (s.initialize.eval ctx) = t.bound)
(preserves : preserves s.next inv)


variables [TRAble ι ι'] [TRAble α β] {s : BoundedStreamGen ι α}
  {t : Stream ι' β} {f : EContext → t.σ} {ctx : EContext}
  [add_zero_class β]

lemma tr_to_stream.eval₀ (h : tr_to_stream s t f ctx) (h₀ h₁) :
  s.to_stream_aux.eval₀ ctx h₀ =
  t.eval₀ (f ctx) h₁ :=
begin
  simp [Stream.eval₀, h.hready h₁, h.hvalid, h₁],
  split_ifs with h₂,
  { /- If both are ready -/ rw [h.hcurr, h.hval]; simpa [h.hready h₁, h.hvalid], },
  { /- If both are not ready -/ refl, },
end

lemma tr_to_stream.eval_steps_eq {inv : EContext → Prop}
  (hinv : ∀ {c}, inv c → inv (s.next.eval c)) (hc : inv ctx)
  (h : ∀ {c}, inv c → tr_to_stream s t f c) (n : ℕ) :
  s.to_stream_aux.eval_steps n ctx =
  t.eval_steps n (f ctx) :=
begin
  induction n with n ih generalizing ctx, { refl, },
  specialize h hc,
  simp [StreamExec.valid, h.hvalid],
  split_ifs with hv, swap, { refl, },
  congr' 1, swap,   { /- The first step is the same -/ rw tr_to_stream.eval₀ h, },
  /- The rest of the steps are the same -/
  rw [ih, h.hnext (h.hvalid.mpr hv)],
  exact hinv hc,
end

lemma tr_to.eval_finsupp_eq {t : StreamExec ι' β} {f : EContext → t.stream.σ} (h : tr_to s t f ctx) :
  StreamExec.eval (tr ctx s) = t.eval :=
by { dsimp [StreamExec.eval, BoundedStreamGen.to_stream, tr], simp [h.hbound, tr_to_stream.eval_steps_eq h.preserves h.init_inv h.to_stream, h.hinit], }

end translate

instance eval_unit : TRAble unit unit := ⟨λ _ _, ()⟩

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
  initialize := i ::= 0, }

def contract (x : BoundedStreamGen ι α) : BoundedStreamGen unit α :=
bifunctor.fst default x

@[simp] lemma contract_spec [TRAble ι ι'] [TRAble α β] (x : BoundedStreamGen ι α)
  (ctx : EContext) :
  tr ctx (contract x) = contract_stream (tr ctx x) := rfl

section sparse_vectors
open NameSpace (reserved) Vars (ind₀ vals len)

@[mk_iff]
structure externSparseVecCond (ctx : EContext) : Prop :=
(inds_len : (ctx.heap.get reserved∷ₙind₀).length = ctx.store.get reserved∷ₙlen)
(vals_len : (ctx.heap.get reserved∷ᵣvals).length = ctx.store.get reserved∷ₙlen)

lemma externSparseVec_tr_to_stream (scratch : NameSpace) (c : EContext) {l : ℕ} (is : vector ℕ l) (vs : vector R l)
  (hc₁ : c.heap.get reserved∷ₙind₀ = is.to_list) (hc₂ : c.heap.get reserved∷ᵣvals = vs.to_list) (hc₃ : c.store.get reserved∷ₙlen = l) :
  tr_to_stream (externSparseVec scratch) (primitives.externSparseVec_stream is vs)
    (λ ctx, ctx.store.get scratch∷ₙVars.i) c :=
{ hvalid := by simp [externSparseVec, primitives.externSparseVec_stream, hc₁, hc₂, hc₃],
  hready' := by simp [externSparseVec, primitives.externSparseVec_stream, hc₁, hc₂, hc₃],
  hnext := by { intros, simp [externSparseVec, primitives.externSparseVec_stream, hc₁, hc₂, hc₃], },
  hcurr := by { simp [externSparseVec, primitives.externSparseVec_stream, hc₁, hc₂, hc₃, vector.nth_eq_nth_le], intros, rw list.nth_le_nth, },
  hval := by { simp [externSparseVec, primitives.externSparseVec_stream, hc₁, hc₂, hc₃, vector.nth_eq_nth_le], intros, rw list.nth_le_nth, } }

def externSparseVec_tr (scratch : NameSpace) (hs : reserved ≠ scratch) (c : EContext)
  (hc : externSparseVecCond c) :
  tr_to (externSparseVec scratch) (primitives.externSparseVec ⟨c.heap.get reserved∷ₙind₀, hc.inds_len⟩ ⟨c.heap.get reserved∷ᵣvals, hc.vals_len⟩)
    (λ ctx, ctx.store.get scratch∷ₙVars.i) c :=
{ inv := c.unmodified reserved,
  to_stream := λ c' hc', by apply externSparseVec_tr_to_stream scratch c'; simp [hc'.h, hc'.s],
  hinit := by simp [primitives.externSparseVec, externSparseVec],
  init_inv := by { apply preserves.unmodified, { simpa [externSparseVec], }, refl, },
  hbound := by simp [primitives.externSparseVec, externSparseVec, hc],
  preserves := by { apply preserves.unmodified, simpa [externSparseVec], } }

open_locale big_operators

@[simp] lemma externSparseVec_spec (scratch : NameSpace) (hs : reserved ≠ scratch) (c : EContext) (hc : externSparseVecCond c) :
  StreamExec.eval (tr c (externSparseVec scratch)) = ∑ i : fin (c.store.get reserved∷ₙlen), finsupp.single ((c.heap.get reserved∷ₙind₀).nth_le i (by rw hc.1; exact i.prop)) ((c.heap.get reserved∷ᵣvals).nth_le i (by rw hc.2; exact i.prop)) :=
by { simp [(externSparseVec_tr scratch hs c hc).eval_finsupp_eq, vector.nth_eq_nth_le], }

end sparse_vectors


def BoundedStreamGen.body (x : BoundedStreamGen unit (Expr rr)) : Prog :=
Prog.branch x.ready
  (reserved∷ᵣoutput ::= reserved∷ᵣoutput + x.value)
/- else -/ Prog.skip <;>
x.next

def compile_scalar (x : BoundedStreamGen unit (Expr rr)) : Prog :=
let out : Ident rr := reserved∷output in
out ::= 0 <;>
x.initialize <;>
Prog.loop x.bound x.valid x.body


section compile_sound

lemma eval_body (x : BoundedStreamGen unit (Expr rr)) (c c' : EContext)
  (hc : c.heap = c'.heap ∧ ∀ v, v ≠ reserved∷ᵣoutput → c.store.get v = c'.store.get v)
  (h : x.to_stream_aux.valid c') (h' : x.valid.eval c') :
  (x.body.eval c).store.get reserved∷ᵣoutput = (x.to_stream_aux.eval₀ c' h ()) + (c.store.get reserved∷ᵣoutput) :=
begin
  have F₁ : x.ready.eval c' = x.ready.eval c := sorry, -- FOOTPRINT: `out ∉ ready.footprint`
  have F₂ : ∀ ctx, (x.next.eval ctx).store.get reserved∷ᵣoutput = ctx.store.get reserved∷ᵣoutput := sorry, -- FOOTPRINT: out ∉ next.footprint
  have F₃ : x.value.eval c' = x.value.eval c := sorry, -- FOOTPRINT: `out ∉ value.footprint`
  simp [BoundedStreamGen.body, Stream.eval₀, h', F₁],
  cases H : x.ready.eval c; simp [H, F₂, F₃, punit_eq_star (tr _ _), add_comm],
end

lemma iterate_body (x : BoundedStreamGen unit (Expr rr)) (c c' : EContext)
  (hc : c.heap = c'.heap ∧ ∀ v, v ≠ reserved∷ᵣoutput → c.store.get v = c'.store.get v)
  (n : ℕ) :
  ((λ ctx, cond (x.valid.eval ctx) (x.body.eval ctx) ctx)^[n] c).store.get reserved∷ᵣoutput =
    (Stream.eval_steps x.to_stream_aux n c' ()) + (c.store.get reserved∷ᵣoutput) :=
begin
  induction n with n ih generalizing c c', { simp, },
  simp,
  have F₁ : x.valid.eval c' = x.valid.eval c := sorry, -- FOOTPRINT: `out ∉ valid.footprint`
  cases H : x.valid.eval c,
  { /- Invalid: both are `0` -/ simp [H, F₁], rw function.iterate_fixed, simp [H], },
  simp [H, F₁],
  rw ih _ (x.next.eval c'), swap,
  { simp [BoundedStreamGen.body], sorry, /- FOOTPRINT: `next` preserves all variables besides `out` -/},
  rw [add_assoc, eval_body x c c' hc],
  simp [F₁, H],
end

lemma compile_scalar_sound (x : BoundedStreamGen unit (Expr rr)) (ctx : EContext) :
  ((compile_scalar x).eval ctx).store.get (reserved∷output : Ident rr) = StreamExec.eval (tr ctx x) () :=
begin
  simp [compile_scalar],
  set ctx' : EContext := ctx.update reserved∷ᵣoutput 0,
  simp [tr, StreamExec.eval],
  rw iterate_body x (x.initialize.eval ctx') (x.initialize.eval ctx),
  have F₁ : (x.initialize.eval ctx').store.get reserved∷ᵣoutput = ctx'.store.get reserved∷ᵣoutput := sorry, -- FOOTPRINT:
  have F₂ : x.bound (x.initialize.eval ctx') = x.bound (x.initialize.eval ctx) := sorry, -- FOOTPRINT:
  { dsimp [BoundedStreamGen.to_stream], simp [F₁, F₂], },
  sorry, /- FOOTPRINT: since `ctx` and `ctx'` only differ in `out`, `init ctx` and `init ctx'` can only differ in `out`
            (since `init` does not read/write from `out`) -/
end

end compile_sound

end stream

end compiler

section examples
open TRAble (tr)

parameters [add_comm_monoid R] [has_one R] [has_mul R]

open_locale big_operators

def sum_vec (scratch : NameSpace) : BoundedStreamGen unit (Expr rr) :=
contract (externSparseVec scratch)

@[simp] lemma sum_vec_spec (scratch : NameSpace) (hs : reserved ≠ scratch) (ctx : EContext) (hctx : externSparseVecCond ctx) :
  StreamExec.eval (tr ctx (sum_vec scratch)) = finsupp.single () (ctx.heap.get reserved∷ᵣvals).sum :=
begin
  simp [sum_vec, *],
  rw [map_sum],
  simp [finset.sum, multiset.map_nth_le hctx.2],
end

lemma sum_vec_compile_spec (scratch : NameSpace) (hs : reserved ≠ scratch) (ctx : EContext) (hctx : externSparseVecCond ctx) :
  ((compile_scalar (sum_vec scratch)).eval ctx).store.get reserved∷ᵣoutput = (ctx.heap.get reserved∷ᵣvals).sum :=
by { rw [compile_scalar_sound, sum_vec_spec _ hs _ hctx], simp, }



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
