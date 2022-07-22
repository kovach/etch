import data.vector
import data.fin.vec_notation
import data.list.of_fn
import data.list.alist
import data.finsupp.basic
import control.bifunctor
import tactic.derive_fintype
import tactic.fin_cases
import finsupp_lemmas
import frames

section
-- This is just some experiments I'm doing, unofficial
-- Anything that works out will go back into compile.lean

parameters {R : Type} [add_zero_class R] [has_one R] [has_mul R]
parameter (R)
-- Same thing as `ℕ ⊕ R` TODO: change or keep?
inductive ExprVal
| nat (n : ℕ)
| rval (r : R)

parameter {R}
namespace ExprVal
instance : inhabited ExprVal := ⟨nat 0⟩

instance [has_to_string R] : has_to_string ExprVal :=
⟨λ v, match v with
| (nat n) := "(" ++ (to_string n) ++ " : ℕ)"
| (rval r) := "(" ++ (to_string r) ++ " : R)"
end⟩

@[simp]
def add : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := nat (n₁ + n₂)
| (rval f₁) (rval f₂) := rval (f₁ + f₂)
| _ _ := arbitrary _

@[simp]
def and : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := if n₁ = 0 then nat 0 else nat n₂
| _ _ := arbitrary _

@[simp]
def mul : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := nat (n₁ * n₂)
| (rval f₁) (rval f₂) := rval (f₁ * f₂)
| _ _ := arbitrary _

@[simp]
def not : ExprVal → ExprVal
| (nat n₁) := if n₁ = 0 then nat 1 else nat 0
| _ := arbitrary _

@[simp]
def to_nat : ExprVal → ℕ
| (nat n₁) := n₁
| _ := default

@[simp]
def eq : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := if n₁ = n₂ then nat 1 else nat 0
| _ _ := arbitrary _

@[simp]
def lt : ExprVal → ExprVal → ExprVal
| (nat n₁) (nat n₂) := if n₁ < n₂ then nat 1 else nat 0
| _ _ := arbitrary _

@[simp]
def to_r : ExprVal → R
| (nat n) := n
| (rval r) := r

@[simp]
def cast_r (v : ExprVal) : ExprVal := rval v.to_r

end ExprVal
section Ident

section vars
@[derive decidable_eq, derive fintype, derive inhabited]
inductive Vars
| i | j | k | w | x | y | z | ind₀ | ind₁ | ind₂ | break | output

open Vars
instance : has_to_string Vars :=
⟨λ v, match v with 
-- S.split(" | ").map(s => s + ' := "' + s + '"')
| i := "i" | j := "j" | k := "k" | w := "w" | x := "x" | y := "y" | z := "z" | ind₀ := "ind₀" | ind₁ := "ind₁" | ind₂ := "ind₂" | break := "break" | output := "output"
end⟩
end vars

section NameSpace
@[derive decidable_eq, derive inhabited, derive has_to_string, reducible]
def NameSpace := ℕ

def NameSpace.reserved : NameSpace := 0

def fresh (S : finset NameSpace) : NameSpace :=
S.max.iget + 1

theorem not_fresh_mem (S : finset NameSpace) : fresh S ∉ S :=
begin
  simp only [fresh],
  cases hn : S.max,
  { rw [finset.max_eq_none] at hn, subst hn, exact finset.not_mem_empty _, },
  intro h, simpa using finset.le_max_of_mem h hn,
end

theorem not_fresh_reserved (S : finset NameSpace) : fresh S ≠ NameSpace.reserved :=
by simp [fresh, NameSpace.reserved]

attribute [irreducible] NameSpace
end NameSpace

@[derive decidable_eq]
structure Ident :=
(ns : NameSpace)
(name : Vars)

@[simp] lemma Ident_ns (ns : NameSpace) (name : Vars) :
  (Ident.mk ns name).ns = ns := rfl

@[simp] lemma Ident_name (ns : NameSpace) (name : Vars) :
  (Ident.mk ns name).name = name := rfl
-- def Ident.of : string → Ident := Ident.name
instance : has_to_string Ident :=
⟨λ i, "n" ++ (to_string i.ns) ++ "_" ++ (to_string i.name)⟩

@[simp] lemma Ident_ns_range : set.range Ident.ns = set.univ :=
by { ext, simp, exact ⟨⟨x, default⟩, rfl⟩, }

parameter (R)
inductive IdentVal
| base (val : ExprVal) : IdentVal
| arr (val : list (ExprVal)) : IdentVal
instance : inhabited IdentVal := ⟨IdentVal.base default⟩ 

parameter {R}
def IdentVal.get : IdentVal → option ℕ → ExprVal
| (IdentVal.base val) none := val
| (IdentVal.arr val) (some i) := val.inth i
| _ _ := arbitrary _ 

@[simp] lemma IdentVal.get_none (b : ExprVal) : (IdentVal.base b).get none = b := rfl
@[simp] lemma IdentVal.get_ind (arr : list ExprVal) (n : ℕ) :
  (IdentVal.arr arr).get (some n) = arr.inth n := rfl

def IdentVal.update : IdentVal → option ℕ → ExprVal → IdentVal
| (IdentVal.arr val) (some i) newval := IdentVal.arr (val.modify_nth (λ _, newval) i)
| _ none newval := IdentVal.base newval
| _ _ _ := arbitrary _

@[simp] lemma IdentVal.update_none (i : IdentVal) (x : ExprVal) :
  i.update none x = IdentVal.base x := by cases i; simp [IdentVal.update]
@[simp] lemma IdentVal.update_ind (arr : list ExprVal) (n : ℕ) (x : ExprVal) :
  (IdentVal.arr arr).update (some n) x = IdentVal.arr (arr.modify_nth (λ _, x) n) := rfl

end Ident


inductive Op
| add | mul | and | or | not | eq | lt | cast_r

namespace Op
instance : has_to_string Op := ⟨λ v, match v with
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

@[simp]
def eval : ∀ o : Op, (fin o.arity → ExprVal) → ExprVal
| add := λ x, (x 0).add (x 1)
| mul := λ x, (x 0).mul (x 1)
| and := λ x, (x 0).and (x 1)
| or := λ x, ((x 0).not.and $ (x 1).not).not -- TODO
| not := λ x, (x 0).not
| eq := λ x, (x 0).eq (x 1)
| lt := λ x, (x 0).lt (x 1)
| cast_r := λ x, (x 0).cast_r
end Op

parameter (R)
inductive Expr
| lit : ExprVal → Expr
| ident : Ident → Expr
| access : Ident → Expr → Expr
| call : ∀ o : Op, (fin o.arity → Expr) → Expr

parameter {R}
local notation a ` ⟪+⟫ `:80 b := Expr.call Op.add ![a, b]
local notation a ` ⟪*⟫ `:80 b := Expr.call Op.mul ![a, b]
local notation a ` ⟪&&⟫ `:80 b := Expr.call Op.and ![a, b]
local notation a ` ⟪||⟫ `:80 b := Expr.call Op.or ![a, b]
local notation a ` ⟪<⟫ `:80 b := Expr.call Op.lt ![a, b]
local notation a ` ⟪=⟫ `:80 b := Expr.call Op.eq ![a, b]

@[simp]
def Expr.eval  (ctx : Ident → IdentVal) : Expr → ExprVal
| (Expr.lit r) := r
| (Expr.ident x) := (ctx x).get none
| (Expr.access x i) := (ctx x).get (some i.eval.to_nat)
| (Expr.call o args) := o.eval (λ i, (args i).eval)

instance has_coe_from_nat : has_coe ℕ Expr := ⟨λ n, Expr.lit $ ExprVal.nat n⟩
instance has_coe_From_R : has_coe R Expr := ⟨λ r, Expr.lit $ ExprVal.rval r⟩
instance has_coe_from_expr : has_coe Ident Expr := ⟨Expr.ident⟩

example : Expr := (0 : ℕ)
example : Expr := (0 : R)

@[simp] lemma Expr.eval_const_nat (ctx : Ident → IdentVal) (n : ℕ) :
  Expr.eval ctx n = ExprVal.nat n := rfl

@[simp] lemma Expr.eval_const_r (ctx : Ident → IdentVal) (r : R) :
  Expr.eval ctx r = ExprVal.rval r := rfl

@[simp] lemma Expr.eval_coe_ident (ctx : Ident → IdentVal) (i : Ident) :
  Expr.eval ctx i = (ctx i).get none := rfl


/-- Pretty print repr of indices; ignores [] (scalar), represents only
    vector indices -/
-- def idcs_repr (idcs : list string) : string :=
-- if idcs.length = 0 then "" else "[" ++ ", ".intercalate idcs ++ "]"

def expr_repr [has_to_string R] : Expr → string
| (Expr.lit r) := to_string r
| (Expr.ident x) := to_string x
| (Expr.access x i) := (to_string x) ++ "[" ++ (expr_repr i) ++ "]"
| (Expr.call o args) := (to_string o) ++ "(" ++ ", ".intercalate (vector.of_fn (λ i, expr_repr $ args i)).to_list ++ ")"

instance [has_to_string R] : has_to_string Expr := ⟨expr_repr⟩
-- Because ambiguous whether R or ℕ
-- instance : has_zero (Expr R) := ⟨Expr.lit 0⟩
-- instance : has_one (Expr R) := ⟨Expr.lit 1⟩

parameter (R)
structure LoopBound :=
(frame : finset Ident)
(to_fun : (Ident → IdentVal) → ℕ)
(has_frame : function.has_frame to_fun frame)

parameter {R}
instance : has_coe_to_fun LoopBound (λ _, (Ident → IdentVal) → ℕ) :=
⟨LoopBound.to_fun⟩

@[simp] lemma to_fun_eq_coe (f : LoopBound) (ctx : Ident → IdentVal) : f.to_fun = ⇑f := rfl

@[simp] lemma to_fun_apply (frame : finset Ident) (to_fun : (Ident → IdentVal) → ℕ) (h) (ctx : Ident → IdentVal) :
  (LoopBound.mk frame to_fun h) ctx = to_fun ctx := rfl

theorem LoopBound.frame_sound (f : LoopBound) {ctx₀ ctx₁ : Ident → IdentVal} (h : ∀ v ∈ f.frame, ctx₀ v = ctx₁ v) :
  f ctx₀ = f ctx₁ := function.has_frame_iff.mp f.has_frame h

parameter (R)
inductive Prog
| skip : Prog
| store (dst : Ident) (ind : option Expr) (val : Expr)
| seq (a : Prog) (b : Prog)
| branch (cond : Expr) (a : Prog) (b : Prog)
| loop (n : LoopBound) (b : Prog)

parameter {R}
def prog_repr [has_to_string R] : Prog → list string
| Prog.skip := [";"]
| (Prog.store dst ind val) := [(to_string dst) ++ (ind.elim "" (λ i, "[" ++ to_string i ++ "]")) ++ " := " ++ (to_string val) ++ ";"]
| (Prog.seq a b) := (prog_repr a) ++ (prog_repr b)
| (Prog.branch c a b) := ["if " ++ (to_string c)]
    ++ (prog_repr a).map (λ s, "  " ++ s)
    ++ ["else"]
    ++ (prog_repr b).map (λ s, "  " ++ s)
| (Prog.loop n b) := ["for at most some bounded # of times"]
    ++ (prog_repr b).map (λ s, "  " ++ s)

instance [has_to_string R] : has_to_string Prog := ⟨λ p, "\n".intercalate (prog_repr p)⟩



def Prog.eval : Prog → (Ident → IdentVal) → (Ident → IdentVal)
| Prog.skip ctx := ctx
| (Prog.store dst ind val) ctx := function.update ctx dst ((ctx dst).update (ind.map (λ i : Expr, (i.eval ctx).to_nat)) (val.eval ctx))
| (Prog.seq a b) ctx := b.eval (a.eval ctx)
| (Prog.branch cond a b) ctx := if 0 < (Expr.eval ctx cond).to_nat then a.eval ctx else b.eval ctx
| (Prog.loop n b) ctx := (nat.iterate b.eval (n ctx)) ctx

def alist.ilookup {α β : Type*} [decidable_eq α] [inhabited β] (s : alist (λ _ : α, β)) (a : α) : β :=
(s.lookup a).iget

-- Faster version of eval
-- TODO: which one should be the "main" one
def Prog.eval' : Prog → (alist (λ _ : Ident, IdentVal)) → (alist (λ _ : Ident, IdentVal))
| Prog.skip ctx := ctx
| (Prog.store dst ind val) ctx := ctx.insert dst ((ctx.ilookup dst).update (ind.map (λ i : Expr, (i.eval ctx.ilookup).to_nat)) (val.eval ctx.ilookup))
| (Prog.seq a b) ctx := b.eval' (a.eval' ctx)
| (Prog.branch cond a b) ctx := if 0 < (cond.eval ctx.ilookup).to_nat then a.eval' ctx else b.eval' ctx
| (Prog.loop n b) ctx := (nat.iterate b.eval' (n ctx.ilookup)) ctx

section frame

@[simp]
def Expr.frame : Expr → finset Ident
| (Expr.lit r) := ∅
| (Expr.ident i) := {i}
| (Expr.access x n) := insert x n.frame
| (Expr.call o args) := finset.bUnion finset.univ (λ i, (args i).frame)

@[simp] lemma Expr_frame_coe_nat (n : ℕ) : (n : Expr).frame = ∅ := rfl
@[simp] lemma Expr_frame_coe_R (r : R) : (r : Expr).frame = ∅ := rfl
@[simp] lemma Expr_frame_coe_ident (i : Ident) : (i : Expr).frame = {i} := rfl

/-- The evaluation of an Expr depends only on the values in its frame -/
theorem frame_sound_Expr {e : Expr} {ctx₀ ctx₁ : Ident → IdentVal}
  (h : ∀ v ∈ e.frame, ctx₀ v = ctx₁ v) : e.eval ctx₀ = e.eval ctx₁ :=
begin
  induction e,
  case Expr.lit : { simp, },
  case Expr.ident : i { simp [h i _], },
  case Expr.access : x n ih { simp at h ⊢, specialize ih h.2, simp [ih, h.1], },
  case Expr.call : o args ih 
  { simp, congr, ext i, apply ih, refine (λ v hv, h v _), simp, refine ⟨_, hv⟩, }
end

theorem Expr.has_frame (e : Expr) : function.has_frame (λ ctx, e.eval ctx : (Ident → IdentVal) → ExprVal) e.frame :=
by { rw function.has_frame_iff, intros c₁ c₂, apply frame_sound_Expr, }

@[simp]
def Prog.frame : Prog → finset Ident
| Prog.skip := ∅
| (Prog.store dst none val) := insert dst val.frame
| (Prog.store dst (some ind) val) := insert dst (ind.frame ∪ val.frame)
| (Prog.seq a b) := a.frame ∪ b.frame
| (Prog.branch cond a b) := cond.frame ∪ a.frame ∪ b.frame
| (Prog.loop n b) := n.frame ∪ b.frame

/-- Ident's not in the frame remain unchanged -/
theorem not_mem_Prog_frame {p : Prog} {s} (hs : s ∉ p.frame) (ctx : Ident → IdentVal) :
  p.eval ctx s = ctx s :=
begin
  induction p generalizing ctx,
  case Prog.skip : { simp [Prog.eval], },
  case Prog.store : dst ind val
  { suffices : s ≠ dst, { simp [Prog.eval, this] },
    rintro rfl, cases ind; simpa using hs, },
  case Prog.seq : a b ih₁ ih₂
  { simp [decidable.not_or_iff_and_not] at hs, 
    simp [Prog.eval, ih₂ hs.2, ih₁ hs.1], },
  case Prog.branch : cond a b ih₁ ih₂
  { simp [decidable.not_or_iff_and_not] at hs, 
    simp [Prog.eval], split_ifs, exacts [ih₁ hs.2.1 _, ih₂ hs.2.2 _], },
  case Prog.loop : n b ih
  { simp [Prog.eval],
    generalize : n ctx = n',
    induction n' with n' ihn', { refl, },
    simp [function.iterate_succ_apply'],
    rwa ih, simp [decidable.not_or_iff_and_not] at hs, exact hs.2, }
end

/-- If two contexts agree on a set S ⊇ p.frame, then they agree after the evaluation as well. -/
theorem frame_sound_Prog {p : Prog} {ctx₀ ctx₁ : Ident → IdentVal} {S : finset Ident} (hS : p.frame ⊆ S)
  (h : ∀ v ∈ S, ctx₀ v = ctx₁ v) {s} (hs : s ∈ S) : p.eval ctx₀ s = p.eval ctx₁ s :=
begin
  induction p generalizing ctx₀ ctx₁ s,
  case Prog.skip : { simpa [Prog.eval] using h _ hs, },
  case Prog.store : dst ind val
  { by_cases s_eq : s = dst, swap, { simpa [Prog.eval, s_eq] using h _ hs, },
    subst s_eq, simp [Prog.eval], congr' 1, { exact h _ hs, },
    { cases ind; simp, congr' 1, apply frame_sound_Expr, refine λ v hv, h v _, simp [finset.subset_iff] at hS, apply hS.2, left, exact hv, },
    apply frame_sound_Expr, refine λ v hv, h v _, cases ind; simp [finset.subset_iff] at hS, exacts [hS.2 _ hv, hS.2 _ (or.inr hv)], },
  case Prog.seq : a b ih₁ ih₂
  { simp [Prog.eval],
    simp at hS, refine ih₂ (finset.union_subset_right hS) _ hs,
    intros v hv, exact ih₁ (finset.union_subset_left hS) h hv, },
  case Prog.branch : cond a b ih₁ ih₂
  { have : cond.eval ctx₀ = cond.eval ctx₁,
    { apply frame_sound_Expr, refine λ v hv, h v _,
      simp [finset.subset_iff] at hS, exact hS (or.inl hv), },
    simp [Prog.eval, this], simp at hS, split_ifs,
    { exact ih₁ (finset.union_subset_left (finset.union_subset_right hS)) h hs, },
    exact ih₂ (finset.union_subset_right (finset.union_subset_right hS)) h hs, },
  case Prog.loop : n b ih
  { have : n ctx₀ = n ctx₁,
    { apply LoopBound.frame_sound, refine λ v hv, h v _, simp [finset.subset_iff] at hS, exact hS (or.inl hv), },
    simp [Prog.eval, this],
    generalize : n ctx₁ = n',
    induction n' with n' ihn generalizing s, { exact h _ hs, },
    simp [function.iterate_succ_apply'], 
    refine ih _ @ihn hs, simp at hS, exact finset.union_subset_right hS, }
end

def Expr.to_loop_bound (e : Expr) : LoopBound :=
{ frame := e.frame,
  to_fun := λ ctx, (e.eval ctx).to_nat,
  has_frame := (Expr.has_frame e).postcomp _ }

@[simp] lemma Expr.to_loop_bound_to_fun (e : Expr) (ctx : Ident → IdentVal) : e.to_loop_bound ctx = (e.eval ctx).to_nat :=
by simp [Expr.to_loop_bound]


end frame

local infixr ` <;> `:1 := Prog.seq
local notation a ` ::= `:20 c := Prog.store a none c
local notation a ` ⟬ `:9000 i ` ⟭ ` ` ::= `:20 c := Prog.store a (some i) c
local notation x ` ⟬ `:9000 i ` ⟭ ` := Expr.access x i 
local infix `∷`:9000 := Ident.mk

parameter (R)
structure BoundedStreamGen (ι α : Type) :=
(current : ι)
(value : α)
(ready : Expr)
(next : Prog)
(valid : Expr)
(bound : Expr)
(initialize : Prog)

parameter {R}
@[ext]
theorem BoundedStreamGen.ext {ι α} {x y : BoundedStreamGen ι α} (h₀ : x.current = y.current)
  (h₁ : x.value = y.value) (h₂ : x.ready = y.ready) (h₃ : x.next = y.next) (h₄ : x.valid = y.valid)
  (h₅ : x.bound = y.bound) (h₆ : x.initialize = y.initialize) : x = y :=
by { cases x, cases y, dsimp only at *, subst_vars, }

variables {ι α : Type}

section functorality

@[simps]
instance : bifunctor BoundedStreamGen :=
{ bimap := λ _ _ _ _ i v g, { g with value := v g.value, current := i g.current } }

instance : is_lawful_bifunctor BoundedStreamGen :=
{ id_bimap := λ _ _ g, by ext; simp [bimap],
  bimap_bimap := λ _ _ _ _ _ _ i i' v v' g, by ext; simp [bimap] }

infixr ` <$₁> `:1 := bifunctor.fst
infixr ` <$₂> `:1 := bifunctor.snd

-- TODO: find a better way
variables {ι' α' : Type} (f : ι → ι') (g : α → α') (s : BoundedStreamGen ι α)
@[simp] lemma BSG_fst_value : (f <$₁> s).value = s.value := rfl 
@[simp] lemma BSG_fst_ready : (f <$₁> s).ready = s.ready := rfl
@[simp] lemma BSG_fst_next : (f <$₁> s).next = s.next := rfl
@[simp] lemma BSG_fst_valid : (f <$₁> s).valid = s.valid := rfl
@[simp] lemma BSG_fst_bound : (f <$₁> s).bound = s.bound := rfl
@[simp] lemma BSG_fst_init : (f <$₁> s).initialize = s.initialize := rfl
@[simp] lemma BSG_snd_current : (g <$₂> s).current = s.current := rfl 
@[simp] lemma BSG_snd_ready : (g <$₂> s).ready = s.ready := rfl
@[simp] lemma BSG_snd_next : (g <$₂> s).next = s.next := rfl
@[simp] lemma BSG_snd_valid : (g <$₂> s).valid = s.valid := rfl
@[simp] lemma BSG_snd_bound : (g <$₂> s).bound = s.bound := rfl
@[simp] lemma BSG_snd_init : (g <$₂> s).initialize = s.initialize := rfl

@[simp] lemma BSG_fst_current : (f <$₁> s).current = f s.current := rfl
@[simp] lemma BSG_snd_value : (g <$₂> s).value = g s.value := rfl

attribute [functor_norm] bifunctor.fst_snd bifunctor.snd_fst

end functorality

@[pattern]
def Prog.if1 (cond : Expr) (b : Prog) := Prog.branch cond b Prog.skip

def BoundedStreamGen.compile (g : BoundedStreamGen unit Prog) : Prog :=
g.initialize <;>
Ident.mk default Vars.break ::= (0 : ℕ) <;>
Prog.loop (Expr.to_loop_bound g.bound) $
  Prog.if1 (Expr.call Op.not ![Ident.mk default Vars.break]) $
    Prog.if1 g.ready g.value <;>
    Prog.branch g.valid g.next (Ident.mk default Vars.break ::= (1 : ℕ))

parameter (R)
/-- Indicates that things of type α (which typically involve Expr R)'s can eval
  to things of type β given a context ctx : Ident → IdentVal R -/
class StreamEval (α β: Type) :=
(eval : α → (Ident → IdentVal) → β)

/-- An Compileable.compile (f, e) indicates that f describes how to compile e to a program -/
class Compileable (α β : Type) :=
(compile : α → β → Prog)

parameter {R}
-- This is ind_eval, but we need to support recursion so we extract it specifically
-- Mathlib's lack of computability bites here;
-- since finsupp is noncomputable (this is actually a controversial-ish decision from what I gather from the Zulip)
-- it poisons "eval_stream"
-- We only use +, finsupp.single and finsupp.zero (zero is computable), so maybe a TODO is a computable implementation
@[simp]
noncomputable def eval_stream {ι β : Type} [add_zero_class β] :
  ℕ → (Ident → IdentVal) → (BoundedStreamGen ((Ident → IdentVal) → ι) ((Ident → IdentVal) → β)) → (ι →₀ β)
| 0 _ _ := 0
| (n+1) ctx s :=
if (s.valid.eval ctx).to_nat = 1 then
  (if (s.ready.eval ctx).to_nat = 1 then finsupp.single (s.current ctx) (s.value ctx) else 0)
    + (eval_stream n (s.next.eval ctx) s)
else 0

instance base_eval : StreamEval Expr ExprVal :=
⟨λ e ctx, e.eval ctx⟩

instance base_eval_nat : StreamEval Expr ℕ :=
⟨λ e ctx, (e.eval ctx).to_nat⟩

instance base_eval_R : StreamEval Expr R :=
⟨λ e ctx, (e.eval ctx).to_r⟩

instance refl_eval {α : Type} : StreamEval α α := ⟨λ x _, x⟩

noncomputable instance ind_eval {ι ι' α β : Type} [StreamEval ι ι'] [StreamEval α β] [add_zero_class β] :
  StreamEval (BoundedStreamGen ι α) (ι' →₀ β) :=
{ eval := λ s ctx, eval_stream (s.bound.eval ctx).to_nat (s.initialize.eval ctx) 
  (StreamEval.eval <$₁> StreamEval.eval <$₂> s) }

/- Convenience instance for `unit` so we don't have to write `unit → R` and can directly go to R
TODO: Remove? -/
noncomputable instance unit_eval {α β : Type} [StreamEval α β] [add_zero_class β] :
  StreamEval (BoundedStreamGen unit α) β :=
{ eval := λ s ctx, (StreamEval.eval s ctx : unit →₀ β) () }

instance base_compile : Compileable (Expr → Prog) Expr := 
⟨λ c e, c e⟩

section laws
-- Law 1: eval frame should be frame
structure BoundedStreamGen.has_frame (x : BoundedStreamGen ι α) (ι' β) [StreamEval ι ι'] [StreamEval α β] (S : set Ident) :=
(current : function.has_frame (StreamEval.eval x.current : _ → ι') S)
(value : function.has_frame (StreamEval.eval x.value : _ → β) S)
(ready : ↑x.ready.frame ⊆ S)
(next : ↑x.next.frame ⊆ S)
(valid : ↑x.valid.frame ⊆ S)
(bound : ↑x.bound.frame ⊆ S)
(initialize : ↑x.initialize.frame ⊆ S)

theorem eval_has_frame_of_has_frame {ι' β S} [StreamEval ι ι'] [StreamEval α β] [add_zero_class β] {x : BoundedStreamGen ι α} (hx : x.has_frame ι' β S) :
  function.has_frame (StreamEval.eval x : _ → (ι' →₀ β)) S :=
begin
  sorry,
end


-- Law 2: eval for bound steps should make invalid

end laws

section variable_state

structure WithFrame (α : Type) : Type :=
(val : α)
(frame : finset NameSpace)

instance WithFrame_coe {α : Type} : has_coe (WithFrame α) α := ⟨WithFrame.val⟩

@[simp] lemma WithFrame_coe_val (x : WithFrame α) : x.val = (x : α) := rfl

@[simp] lemma WithFrame.val_eq (val : α) (frame : finset NameSpace) :
  (WithFrame.mk val frame : α) = val := rfl

@[simp] lemma WithFrame.frame_eq (val : α) (frame : finset NameSpace) :
  (WithFrame.mk val frame).frame = frame := rfl

parameter (R)
def WithFrame.is_sound (x : WithFrame α) (β : Type) [StreamEval α β] : Prop :=
function.has_frame (StreamEval.eval (x : α) : (Ident → IdentVal) → β) (Ident.ns⁻¹' x.frame)

parameter {R}
def WithFrame.fresh {β : Type} (x : finset NameSpace) (f : NameSpace → β) : WithFrame β :=
⟨f (fresh x), insert (fresh x) x⟩

lemma WithFrame.fresh_spec (x : finset NameSpace) ⦃v : Ident⦄ (hx : v.ns ∈ x) (v' : Vars) :
  v ≠ (fresh x)∷v' :=
by { rintro rfl, exact not_fresh_mem _ hx, }

lemma WithFrame.is_sound_of_fresh₁ {ι' β} [add_zero_class β] [StreamEval ι ι'] [StreamEval α β] (x : finset NameSpace) {f : NameSpace → BoundedStreamGen ι α} 
  (hf : BoundedStreamGen.has_frame (f (fresh x)) ι β (Ident.ns⁻¹' (insert (fresh x) x))) :
  WithFrame.is_sound (WithFrame.fresh x f) (ι →₀ β) :=
begin
  simp [WithFrame.is_sound], sorry,
end

lemma WithFrame.is_sound_of_fresh₂ {β} [add_zero_class β] [StreamEval α β] (x : finset NameSpace) {f : NameSpace → (BoundedStreamGen unit α)} 
  (hf : BoundedStreamGen.has_frame (f (fresh x)) unit β (Ident.ns⁻¹' (insert (fresh x) x))) :
  WithFrame.is_sound (WithFrame.fresh x f) β :=
begin
  simp [WithFrame.is_sound], sorry,
end


-- (current : ι)
-- (value : α)
-- (ready : Expr)
-- (next : Prog)
-- (valid : Expr)
-- (bound : Expr)
-- (initialize : Prog)

end variable_state
-- example (i : Ident) :  := rfl

section singleton
open Vars (i)

def BoundedStreamGen.singleton (a : WithFrame α) : WithFrame (BoundedStreamGen unit α) :=
WithFrame.fresh a.frame $ λ ns,
{ current := (),
  value := a,
  ready := (1 : ℕ),
  valid := ns∷i ⟪<⟫ (1 : ℕ),
  bound := (1 : ℕ),
  next := ns∷i ::= (1 : ℕ),
  initialize := ns∷i ::= (0 : ℕ) }

theorem singleton_spec {β : Type} [add_zero_class β] [StreamEval α β] (ctx : Ident → IdentVal) (a : WithFrame α)
  (h : WithFrame.is_sound a β) :
  (StreamEval.eval (BoundedStreamGen.singleton a).val ctx : β) = StreamEval.eval a.val ctx :=
begin
  simp only [BoundedStreamGen.singleton, WithFrame.fresh],
  have := WithFrame.fresh_spec a.frame, set ns := fresh a.frame,
  simp [StreamEval.eval, Prog.eval], rw [WithFrame.is_sound, function.has_frame_iff] at h,
  apply h, intros x hx, simp [this hx],
end

theorem singleton_frame_sound {β : Type} [add_zero_class β] [StreamEval α β] {a : WithFrame α}
  (h : WithFrame.is_sound a β) : WithFrame.is_sound (BoundedStreamGen.singleton a) β :=
begin
  simp only [BoundedStreamGen.singleton], apply WithFrame.is_sound_of_fresh₂,
  split,
  { simp [StreamEval.eval], apply function.has_frame.mono, apply function.has_frame.const, exact set.empty_subset _, },
  { simp, apply function.has_frame.mono, exact h, simp [set.preimage_subset_preimage_iff], },
  all_goals { simp [fin.forall_fin_two], },
end

end singleton



def BoundedStreamGen.expr_to_prog (inp : BoundedStreamGen unit Expr) : BoundedStreamGen unit Prog :=
{ current := (),
  value := NameSpace.reserved∷Vars.output ::= NameSpace.reserved∷Vars.output ⟪+⟫ inp.value,
  ready := inp.ready,
  next := inp.next,
  valid := inp.valid,
  bound := inp.bound,
  initialize := inp.initialize <;> NameSpace.reserved∷Vars.output ::= (0 : R) }

-- section example_singleton

-- def test : BoundedStreamGen ℤ unit (Expr ℤ) := M.get (BoundedStreamGen.singleton (10 : ℤ))

-- lemma test_eval : (StreamEval.eval (λ _, arbitrary (IdentVal ℤ)) test : ℤ) = 10 :=
-- by { simp [StreamEval.eval, test, Prog.eval, BoundedStreamGen.singleton], }

-- end example_singleton

section range

def range (n : Expr) (var : Ident) : BoundedStreamGen Expr Expr :=
{ current := var,
  value := Expr.call Op.cast_r ![var],
  ready := var ⟪<⟫ n,
  valid := var ⟪<⟫ n,
  next := var ::= var ⟪+⟫ (1 : ℕ),
  bound := n,
  initialize := var ::= (0 : ℕ), }



end range

section contract

def contract (g : BoundedStreamGen ι α) : BoundedStreamGen unit α :=
(λ _, ()) <$₁> g

lemma contract_aux [add_comm_monoid α] (n : ℕ) (ctx : Ident → IdentVal) 
  (g : BoundedStreamGen ((Ident → IdentVal) → ι) ((Ident → IdentVal) → α)) :
  (eval_stream n ctx ((λ _ _, ()) <$₁> g)) () = (eval_stream n ctx g).sum_range :=
begin
  induction n with n ih generalizing ctx, { simp, },
  simp,
  split_ifs,
  { simp [← ih (g.next.eval ctx)], }, -- Valid and ready
  { simp [← ih (g.next.eval ctx)], }, -- Valid but not ready
  refl, -- Invalid, both are 0
end

theorem contract_spec {β ι' : Type} [add_comm_monoid β] [StreamEval α β] [StreamEval ι ι']
  (s : BoundedStreamGen ι α) (ctx : Ident → IdentVal) :
  StreamEval.eval (contract s) ctx = (StreamEval.eval s ctx : ι' →₀ β).sum_range :=
by simpa [StreamEval.eval, contract, bifunctor.fst] with functor_norm
using contract_aux (s.bound.eval ctx).to_nat (s.initialize.eval ctx)
      (StreamEval.eval <$₁> StreamEval.eval <$₂> s)

end contract

section repeat

end repeat

def flatten {ι₁ ι₂ α : Type} (outer : BoundedStreamGen ι₁ (BoundedStreamGen ι₂ α)) :
  BoundedStreamGen (ι₁ × ι₂) α :=
let inner := outer.value in
{ current := (outer.current, inner.current),
  value := inner.value,
  ready := outer.ready ⟪&&⟫ inner.ready,
  next := let next_outer := outer.next <;> inner.initialize in
  Prog.branch outer.ready 
    (Prog.branch inner.valid inner.next next_outer) 
    next_outer,
  valid := outer.valid,
  bound := outer.bound ⟪*⟫ inner.bound, -- TODO: fix
  initialize := outer.initialize <;> inner.initialize }

-- def test₂ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := range (40 : ℕ) vars.x
-- #eval trace_val $ to_string $ (contract test₂).expr_to_prog.compile
-- #eval (((contract test₂).expr_to_prog.compile.eval' ∅).ilookup vars.output).get none

def externVec (len : Expr) (inp : Ident) (inp_idx : Ident) : BoundedStreamGen Expr Expr :=
{ current := inp_idx,
  value := inp⟬ inp_idx ⟭,
  ready := inp_idx ⟪<⟫ len,
  next := inp_idx ::= inp_idx ⟪+⟫ (1 : ℕ),
  valid := inp_idx ⟪<⟫ len,
  bound := len,
  initialize := inp_idx ::= (0 : ℕ) }

def externCSRMat (l₁ l₂ : Expr) (rows cols data : Ident) (i j k : Ident) :
  BoundedStreamGen (Expr × Expr) Expr :=
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
  initialize := i ::= (0 : ℕ) <;> j ::= (0 : ℕ) <;> k ::= (0 : ℕ), }


-- def test₃ : BoundedStreamGen ℤ (Expr ℤ) (Expr ℤ) := externVec (10 : ℕ) (Ident.of "input") (Ident.of "idx") 

-- #eval trace_val $ to_string $ (contraction (Ident.of "acc") test₃).expr_to_prog.compile

end

-- Examples

-- section example_prog
-- namespace vars

-- abbreviation x := Ident.of "x"
-- abbreviation y := Ident.of "y"
-- abbreviation z := Ident.of "z"
-- abbreviation s := Ident.of "s"
-- abbreviation i := Ident.of "i"
-- abbreviation acc := Ident.of "acc"
-- abbreviation output := Ident.of "output"

-- end vars

-- open Expr Prog vars

-- def pow_prog : Prog ℤ :=
-- z ::= (1 : ℤ) <;>
-- loop ⟨_, _, function.has_frame.const _ _ 4⟩ (z ::= x ⟪*⟫ z)

-- def pow_prog_input (i : Ident) : IdentVal ℤ :=
--   if i = x then IdentVal.base (ExprVal.rval 3)
--   else if i = y then IdentVal.base (ExprVal.nat 4)
--   else arbitrary _

-- def arr_prog : Prog ℤ :=
-- s ::= (0 : ℤ) <;>
-- i ::= (0 : ℕ) <;>
-- loop (Expr.to_loop_bound y) $
--   s ::= s ⟪+⟫ x⟬i⟭ <;>
--   i ::= i ⟪+⟫ (1 : ℕ)

-- def arr_prog_input (i : Ident) : IdentVal ℤ :=
--   if i = x then IdentVal.arr [ExprVal.rval 30, ExprVal.rval (-1), ExprVal.rval 4]
--   else if i = y then IdentVal.base (ExprVal.nat 3)
--   else arbitrary _

-- def range_sum : Prog ℤ :=
-- s ::= (0 : ℤ) <;>
-- i ::= (0 : ℕ) <;>
-- loop ⟨_, _, function.has_frame.const _ _ 500⟩ $
--   s ::= s ⟪+⟫ (Expr.call Op.cast_r ![i]) <;>
--   i ::= i ⟪+⟫ (1 : ℕ)


-- end example_prog
