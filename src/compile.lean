import tactic
import data.list.alist
import control.monad.basic
import control.monad.writer

def debug : bool := ff
def disablePathCondition : bool := ff

def Ident := string
def Label := string
--def IVar := string

@[derive [decidable_eq, fintype]]
inductive BinOp
| add
| mul
| lt
| eq
| and
| or
| min

--#eval fintype.elems BinOp

/-- Expressions for a simple imperative language. -/
@[derive decidable_eq]
inductive E
| lit : ℕ → E
| ident : Ident → E
| bin_op : BinOp → E → E → E
| record_access : E → Ident → E
| call0 : E → E
| call1 : E → E → E
| call2 : E → E → E → E
| deref : E → E
| ternary : E → E → E → E

instance : has_zero E := ⟨E.lit 0⟩
instance : has_one E := ⟨E.lit 1⟩
instance : has_add E := ⟨E.bin_op BinOp.add⟩
instance : has_mul E := ⟨E.bin_op BinOp.mul⟩

@[pattern] def E.false : E := E.lit 0
@[pattern] def E.true : E := E.lit 1

def BinOp.mk_type : BinOp → Type
| _ := E → E → E

def BinOp.mk : Π (b : BinOp), BinOp.mk_type b
| BinOp.and := λ x y,
  match x, y with
  | E.true, y := y
  | x, E.true := x
  | x, y := E.bin_op BinOp.and x y
  end
| BinOp.or := λ x y,
  match x, y with
  | E.false, y := y
  | x, E.false := x
  | x, y := E.bin_op BinOp.or x y
  end
| b := E.bin_op b

instance : has_coe_to_fun BinOp BinOp.mk_type := ⟨BinOp.mk⟩

infixl ` && `:70 := BinOp.and
infixl ` || `:65 := BinOp.or

--#reduce (1024 : E)

/-- Statements for a simple imperative language, including sequencing. -/
inductive Prog
| expr (e : E)
--| put : E → list E → E → Prog
| accum (dst : E) (val : E)
| store (dst : E) (val : E)
| next (stream : E)
| «if» (b : E) (cons : Prog) (alt : Prog)
| seq (a b : Prog)
| block : Prog → Prog -- scope
| label (l : Label)
| labels (labels : list Label)
| jump (l : Label)
| inline_code (code : string)
| debug_code (code : string)
| skip
| comment (c : string)
| error (msg : string)

@[pattern]
def Prog.if1 (b : E) (cons : Prog) : Prog := Prog.if b cons Prog.skip

infixr ` <;> `:1 := Prog.seq

/-
inductive Typ | O | C
open Typ

inductive BBlock : Typ → Typ → Type
| seq {a c : Typ} (b1 : BBlock a O) (b2 : BBlock O c) : BBlock a c
| jmp (l : Label) : BBlock O C
| label (s : string) : BBlock C O

def prog := list (BBlock C C)

def BBlock.get_label : Π {t : Typ}, BBlock C t → string
| _ b@(BBlock.seq b1 b2) :=
  have BBlock.sizeof C (psigma.fst ⟨O, b1⟩) b1 <
    1 + 1 + _x.sizeof + BBlock.sizeof C O b1 +
    BBlock.sizeof O (psigma.fst ⟨_x, b1.seq b2⟩) b2,
    from by linarith,
  b1.get_label
| _ (BBlock.label s) := s
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ p, sizeof p.2)⟩] }
-/

structure Gen (ι α : Type) :=
(current : ι)
(value : α)
(ready : E)
(empty : E)
(next (ifEmpty : unit → Prog) (ifNonempty : Prog → Prog) : Prog)
(reset : Prog)
(initialize : Prog)

structure LGen (ι α : Type) :=
(gen : Gen ι α)
(locate : ι → Prog)

instance (ι : Type) : functor (Gen ι) :=
{ map := λ _ _ f g, { g with value := f g.value } }

instance (ι : Type) : functor (LGen ι) :=
{ map := λ _ _ f lg, { lg with gen := f <$> lg.gen } }

def imap {ι ι' α : Type} (f : ι → ι') (g : Gen ι α) : Gen ι' α :=
{ g with current := f g.current }

def loopT (g : Gen unit Prog) : Prog :=
let loop := "loop", done := "done" in
Prog.block $
  Prog.labels [loop, done] <;>
  g.reset <;>
  Prog.debug_code "__i = 0;" <;>
  Prog.label loop <;>
  Prog.debug_code "__i++;" <;>
  Prog.if g.ready g.value Prog.skip <;>
  (g.next (λ _, Prog.jump done) (<;> Prog.jump loop)) <;>
  Prog.label done <;>
  if debug then Prog.debug_code "printf(\"loops: %d\\n\", __i);\n" else Prog.skip

/-! ### Gen combinators -/

section combinators
variables {ι ι' α β : Type}

def emptyGen [has_top ι] [inhabited α] : Gen ι α :=
{ current := ⊤,
  value := default,
  ready := E.false,
  empty := E.true,
  next := λ a _, a (),
  reset := Prog.skip,
  initialize := Prog.skip }

def singletonGen (a : α) : Gen unit α :=
{ current := (),
  value := a,
  ready := E.true,
  empty := E.true,
  next := λ a _, a (),
  reset := Prog.skip,
  initialize := Prog.skip }

def range (n var : E) : Gen E E :=
{ current := var,
  value := var,
  ready := BinOp.lt var n,
  empty := BinOp.eq var n,
  next := λ kn ks, Prog.if (BinOp.lt var n) (ks $ Prog.next var) (kn ()),
  reset := Prog.store var 0,
  initialize := Prog.skip }

def repeat (var : E) (val : Gen ι α) : Gen E (Gen ι α) :=
{ current := var,
  value := val,
  ready := E.true,
  empty := E.false,
  next := λ kn ks, ks (Prog.next var <;> val.reset),
  reset := Prog.store var 0,
  initialize := val.initialize }

def mulGen [has_mul α] (a b : Gen E α) : Gen E α :=
{ current := BinOp.min a.current b.current,
  value := a.value * b.value,
  ready := BinOp.eq a.current b.current && a.ready && b.ready,
  empty := a.empty || b.empty,
  next := λ kn ks, Prog.if (a.empty || b.empty) (kn ()) $
      Prog.if (BinOp.lt a.current b.current) (a.next kn ks) (b.next kn ks),
  reset := a.reset <;> b.reset,
  initialize := a.initialize <;> b.initialize }

def mulUnitGen [has_mul α] (a b : Gen unit α) : Gen unit α :=
{ current := (),
  value := a.value * b.value,
  ready := a.ready && b.ready,
  empty := a.empty || b.empty,
  next := λ kn ks,
    let warning := Prog.error
      "multiplied unit generators must be static singletons. did you forget to aggregate?"
    in
      a.next
      (λ _, b.next kn (λ _, warning))
      (λ _, warning),
  reset := a.reset <;> b.reset,
  initialize := a.initialize <;> b.initialize }

instance mulGen.has_mul [has_mul α] : has_mul (Gen E α) := ⟨mulGen⟩
instance mulUnitGen.has_mul [has_mul α] : has_mul (Gen unit α) := ⟨mulUnitGen⟩

def externGen (x : E) : Gen E E :=
let call op := E.call0 (E.record_access x op),
    check op (kn : unit → Prog) (ks : Prog → Prog) :=
      Prog.if (call "done") (kn ()) (ks $ Prog.expr $ call op) in
{ current := call "current",
  value := call "value",
  ready := E.true,
  empty := call "done",
  next := check "next",
  reset := Prog.expr $ call "reset",
  initialize := Prog.skip }

def externStorageGen (x : E) : LGen E E :=
let g := externGen x in
{ gen := { g with value := E.call0 (E.record_access x "value") },
  locate := λ i, Prog.expr $ E.call1 (E.record_access x "skip") i }

def flatten (outer : Gen ι (Gen ι' α)) : Gen (ι × ι') α :=
let inner := outer.value,
    reset_inner := Prog.if1 outer.ready inner.reset in
{ current := (outer.current, inner.current),
  value := inner.value,
  ready := outer.ready && inner.ready,
  empty := outer.empty,
  next := λ kn ks,
    let next_outer := outer.next kn (λ s, ks (s <;> reset_inner)) in
    Prog.if outer.ready
      (inner.next (λ _, next_outer) ks)
      next_outer,
  reset := outer.reset <;> reset_inner,
  initialize := outer.initialize <;> inner.initialize }

def flatten_snd : Gen ι (Gen ι' α) → Gen ι' α :=
imap prod.snd ∘ flatten

class Accumulable (l r : Type) (out : out_param $ Type) :=
(accum : l → r → out)

export Accumulable

instance : Accumulable E (Gen unit E) (Gen unit Prog) :=
{ accum := (<$>) ∘ Prog.accum }

-- basic idea: when we step r, locate a new spot in l to store the result
instance Storable.map {l r out : Type} [Accumulable l r out] :
  Accumulable (LGen ι l) (Gen ι r) (Gen unit out) :=
{ accum := λ l r,
  { current := (),
    value := accum l.gen.value r.value,
    ready := r.ready,
    empty := r.empty,
    next := λ kn ks, r.next kn $ λ s, ks (s <;> Prog.if1 r.ready (l.locate r.current)),
    reset := l.gen.reset <;> r.reset <;>
      Prog.if1 r.ready (l.locate r.current),
    initialize := l.gen.initialize <;> r.initialize } }

def contraction (acc : E) (v : Gen E (Gen unit E)) : Gen unit E :=
{ singletonGen acc with
  initialize := v.initialize,
  reset := v.reset <;> Prog.store acc 0 <;> loopT (accum acc (flatten_snd v)) }

end combinators


/-! ### Code output -/

section codegen

structure Context :=
(true_conditions : list E)
(false_conditions : list E)

inductive SemiringType | SInt | SFloat

open SemiringType

inductive TensorType
| TTAtom (ty : SemiringType)
| TTStorage (ty : TensorType)
| TTSparse (ty : TensorType)

open TensorType

inductive CType
| CDouble | CInt | CStorage (ty : CType) | CSparse (ty : CType)

open CType

namespace TensorType

def toCType : TensorType → CType
| (TTAtom SInt) := CInt
| (TTAtom SFloat) := CDouble
| (TTStorage t) := CStorage (toCType t)
| (TTSparse t) := CSparse (toCType t)

end TensorType

@[reducible] def SymbolTable := alist (λ (s : string), TensorType)

def mstring := string
instance : has_one mstring := ⟨""⟩
instance : has_mul mstring := ⟨string.append⟩

@[reducible] def M := state_t (ℕ × SymbolTable) (writer_t mstring (reader Context))

def emptyContext := Context.mk [] []

def symbolType (s : string) : M TensorType :=
do
  (_, m) ← get,
  match m.lookup s with
  | some r := return r
  | none := return (TTAtom SInt) -- todo
  end

def runM (m : M unit) : SymbolTable × string :=
((prod.snd <$> m.run (0, ∅)).run.run emptyContext).map prod.snd id

def emit (s : string) : M unit := tell s

def wrapm {α : Type*} (s : M α) : M α :=
emit "(" *> s <* emit ")"

def wrap (s : string) : string := "(" ++ s ++ ")"

/-! evalTrivial: janky path condition simulator -/

-- \forall c \in cPC e, (!e -> !c)
def false_conds_of_false : E → list E
| e@(E.bin_op BinOp.or a b) := e :: false_conds_of_false a ++ false_conds_of_false b
| e := [e]

def false_conds_of_true : E → list E
| e@(E.bin_op BinOp.eq a b) := [BinOp.lt a b, BinOp.lt b a]
| e@(E.bin_op BinOp.lt a b) := [BinOp.eq a b, BinOp.eq b a, BinOp.lt b a]
| e := []

def E.pushTrue (e : E) (c : Context) : Context :=
if disablePathCondition then c else
{ true_conditions := e :: c.true_conditions,
  false_conditions := false_conds_of_true e ++ c.false_conditions }

def E.pushFalse (e : E) (c : Context) : Context :=
if disablePathCondition then c else
{ true_conditions := c.true_conditions,
  false_conditions := false_conds_of_false e ++ c.false_conditions }

def E.trueElem (e : E) (c : Context) : bool := e ∈ c.true_conditions
def E.falseElem (e : E) (c : Context) : bool := e ∈ c.false_conditions

def evalTrivial : Prog → M (option Prog)
| Prog.skip := return none
| (Prog.if c t e) := do
  pathCondition ← read,
  if c.trueElem pathCondition
  then evalTrivial t
  else if c.falseElem pathCondition
  then evalTrivial e
  else do
    ttriv ← adapt_reader c.pushTrue (evalTrivial t),
    etriv ← adapt_reader c.pushFalse (evalTrivial e),
    return $ match ttriv, etriv with
    | none, none := none
    | _, _ := some $ Prog.if c (ttriv.get_or_else Prog.skip) (etriv.get_or_else Prog.skip)
    end
| (Prog.comment _) := return none
| (Prog.seq a b) := do
  ma ← evalTrivial a,
  mb ← adapt_reader (λ _, emptyContext) (evalTrivial b),
  return $ match ma, mb with
  | none, none := none
  | some a', none := some a'
  | none, some b' := some b'
  | some a', some b' := a' <;> b'
  end
| e := return (some e)

--def e2c : E → string
--| (E.lit i) := showT i
--| (E.ident i) := i
--| (E.bin_op op e1 e2) := wrap $ e2c e1 <> op <> e2c e2
--| (E.call f es        -> e2c f <> (wrap $ intercalate "," $ map e2c es)
--  RecordAccess e f -> e2c e <> "." <> f
--  Deref e          -> wrap $ "*" <> e2c e
--  Ternary c t e    -> wrap $ wrap (e2c c) <> "?" <> e2c t <> ":" <> e2c e
--  And a b          -> wrap $ e2c a <> "&&" <> e2c b
--  Or a b           -> wrap $ e2c a <> "||" <> e2c b

end codegen
