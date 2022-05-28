import tactic
import data.list.alist
import control.monad.basic

def debug : bool := ff
def disablePathCondition : bool := ff
def disablePrinting := ff
def disableMatrixPrinting := ff
def disableClangFormat := ff
def matrixFile := "data/smallM.mtx"
--def matrixFile := "data/cavity11.mtx"
def vectorFile := "data/smallV.mtx"
--def vectorFile := "data/cavity_ones.mtx"

@[reducible] def Ident := string
@[reducible] def Label := string

@[derive [decidable_eq, fintype]]
inductive BinOp | add | mul | lt | eq | and | or | min

--#eval fintype.elems BinOp

/-- Expressions for a simple imperative language. -/
@[derive decidable_eq]
inductive E
| lit : ℕ → E
| ident : Ident → E
| bin_op : BinOp → E → E → E
| record_access : E → Ident → E
| value : E → E
| current : E → E
| call0 : E → E
| call1 : E → E → E
| call2 : E → E → E → E
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
  | E.true, _ := E.true
  | _, E.true := E.true
  | x, y := E.bin_op BinOp.or x y
  end
| b := E.bin_op b

instance : has_coe_to_fun BinOp BinOp.mk_type := ⟨BinOp.mk⟩

infixl ` && `:70 := BinOp.and
infixl ` || `:65 := BinOp.or

/-- Statements for a simple imperative language, including sequencing. -/
inductive Prog
| expr (e : E)
| accum (dst : E) (val : E)
| store (dst : E) (val : E)
| next (stream : E)
| incr (a : E)
| «if» (b : E) (cons : Prog) (alt : Prog)
| seq (a b : Prog)

| block (body : Prog) : Prog -- only used to produce scoped labels
| label (l : Label)
| labels (labels : list Label)
| jump (l : Label)
| skip

| inline_code (code : string)
| debug_code (code : string)
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

def loop (g : Gen unit Prog) : Prog :=
let loopLabel := "loop", doneLabel := "done" in
Prog.block $
  Prog.labels [loopLabel, doneLabel] <;>
  g.reset <;>
  Prog.debug_code "__i = 0;" <;>
  Prog.label loopLabel <;>
  Prog.debug_code "__i++;" <;>
  Prog.if g.ready g.value Prog.skip <;>
  (g.next (λ _, Prog.jump doneLabel) (<;> Prog.jump loopLabel)) <;>
  Prog.label doneLabel <;>
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

-- "iota"
def range (n var : E) : Gen E E :=
{ current := var,
  value := var,
  ready := BinOp.lt var n,
  empty := BinOp.eq var n,
  next := λ kn ks, Prog.if (BinOp.lt var n) (ks $ Prog.incr var) (kn ()),
  reset := Prog.store var 0,
  initialize := Prog.skip }

def repeat (var : E) (val : Gen ι α) : Gen E (Gen ι α) :=
{ current := var,
  value := val,
  ready := E.true,
  empty := E.false,
  next := λ kn ks, ks (Prog.incr var <;> val.reset),
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
    next (kn : unit → Prog) (ks : Prog → Prog) :=
      Prog.if (call "done") (kn ()) (ks $ Prog.next x) in
{ current := x.current,
  value := x.value,
  ready := E.true,
  empty := call "done",
  next  := next,
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
    let next_outer := outer.next kn (ks ∘ (<;> reset_inner)) in
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
  reset := v.reset <;> Prog.store acc 0 <;> loop (accum acc (flatten_snd v)) }

end combinators

/-! ### Code output -/

section codegen

inductive ValueType | int | float

open ValueType

inductive TensorType
| atom (ty : ValueType)
| storage (ty : TensorType)
| sparse (ty : TensorType)

open TensorType

inductive CType
| double | int | storage (ty : CType) | sparse (ty : CType)

namespace TensorType

def toCType : TensorType → CType
| (atom ValueType.int) := CType.int
| (atom ValueType.float) := CType.double
| (storage t) := CType.storage (toCType t)
| (sparse t) := CType.sparse (toCType t)

end TensorType

@[reducible] def SymbolTable := alist (λ (s : string), TensorType)

def SymbolTable.to_list : SymbolTable → list (string × TensorType)
| st := st.entries.map (λ p, (p.1, p.2))

structure Context :=
(true_conditions : list E)
(false_conditions : list E)

def emptyContext := Context.mk [1] [0]

structure MState :=
(counter : ℕ)
(symbolTable : SymbolTable)
(buffer : buffer char)

instance : has_emptyc MState := ⟨⟨0, ∅, buffer.nil⟩⟩

-- note: inserting a writer_t for collecting output code kills performance
@[reducible] def M := state_t MState (reader Context)

def symbolType (var : string) : M TensorType :=
do
  s ← get,
  match s.symbolTable.lookup var with
  | some r := return r
  | none := return (atom ValueType.int) -- todo
  end

def runM {α} (m : M α) : α := ((m.run ∅).run emptyContext).fst
def runInfo (m : M unit) : SymbolTable × buffer char :=
(λ s : MState, (s.symbolTable, s.buffer)) ((m.run ∅).run emptyContext).snd

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

def Prog.evalTrivial : Prog → M (option Prog)
| Prog.skip := return none
| (Prog.if c t e) := do
  pathCondition ← read,
  if c.trueElem pathCondition
  then t.evalTrivial
  else if c.falseElem pathCondition
  then e.evalTrivial
  else do
    ttriv ← adapt_reader c.pushTrue  t.evalTrivial,
    etriv ← adapt_reader c.pushFalse e.evalTrivial,
    return $ match ttriv, etriv with
    | none, none := none
    | _, _ := some $ Prog.if c (ttriv.get_or_else Prog.skip) (etriv.get_or_else Prog.skip)
    end
| (Prog.comment _) := return none
| (Prog.seq a b) := do
  ma ← a.evalTrivial,
  mb ← adapt_reader (λ _, emptyContext) b.evalTrivial,
  return $ match ma, mb with
  | none, none := none
  | some a', none := a'
  | none, some b' := b'
  | some a', some b' := a' <;> b'
  end
| (Prog.block a) := do a ← a.evalTrivial, return (Prog.block <$> a)
| e := return (some e)

def BinOp.to_c : BinOp → string
| BinOp.add := "+"
| BinOp.mul := "*"
| BinOp.lt := "<"
| BinOp.eq := "=="
| BinOp.and := "&&"
| BinOp.or := "||"
| BinOp.min := "min"

def wrap (s : string) : string := "(" ++ s ++ ")"

def E.to_c : E → string
| (E.lit i)                  := repr i
| (E.ident i)                := i
| (E.value i)                := i.to_c ++ ".value()"
| (E.current i)                := i.to_c ++ ".current()"
| (E.bin_op BinOp.min e1 e2) := BinOp.min.to_c ++ (wrap $ e1.to_c ++ "," ++ e2.to_c)
| (E.bin_op op e1 e2)        := wrap $ e1.to_c ++ op.to_c ++ e2.to_c
| (E.call0 f)                := f.to_c ++ wrap ""
| (E.call1 f a1)             := f.to_c ++ (wrap a1.to_c)
| (E.call2 f a1 a2)          := f.to_c ++ (wrap $ a1.to_c ++ "," ++ a2.to_c)
| (E.record_access e f)      := e.to_c ++ "." ++ f
| (E.ternary c t e)          := wrap $ wrap c.to_c ++ "?" ++ t.to_c ++ ":" ++ e.to_c

def emit (str : string) : M unit := modify $ λ s : MState,
{ s with buffer := s.buffer.append_string str }
def emitLine (s : string) : M unit := do emit $ s ++ ";"

namespace Prog

def to_c : Prog → M unit
| (expr e)        := emitLine $ e.to_c
| (accum dst val) := emitLine $ dst.to_c ++ " += " ++ val.to_c
| (store dst val) := emitLine $ dst.to_c ++ " = " ++ val.to_c
| (incr stream)   := emitLine $ stream.to_c ++ "++"
| (next stream)   := emitLine $ stream.to_c ++ ".next()"
| (seq a b)       := a.to_c >> b.to_c
| (block t)       := emit "{" >> t.to_c >> emit "}"
| (label l)       := emit $ "\n" ++ l ++ ":;\n"
| (labels ls)     := emitLine $ "__label__ " ++ string.intercalate "," ls
| (jump  l)       := emit $ "goto " ++ l ++ ";"
| (inline_code s) := emit s
| (debug_code s)  := emit s
| (skip)          := emit ""
| (comment s)     := emit $ "// " ++ s ++ "\n"
| (error s)       := emit "invalid program"
| («if» c t e)    := do
    emit "if (" >> emit c.to_c >> emit ") {",
      t.to_c,
    emit "}", emit " else {",
      e.to_c,
    emit "}"

def to_c_opt (p : Prog) : M unit := do
  mp ← evalTrivial p,
  (mp.get_or_else Prog.skip).to_c

end Prog

def CType.to_c : CType → string
| CType.double := "num"
| CType.int := "index"
| (CType.storage t) := "SparseStorageArray<" ++ t.to_c ++ ">"
| (CType.sparse t) := "SparseArray<" ++ t.to_c ++ ">"

def toDecl : string × CType → string | (name, ctype) :=
  match ctype with
  | CType.double := "num " ++ name ++ " = 0;\n"
  | CType.int := "index " ++ name ++ " = 0;\n"
  | t := t.to_c ++ " " ++ name ++ ";\n"
  end

def insertDecls : SymbolTable -> string :=
string.join ∘ list.map (toDecl ∘ prod.map id TensorType.toCType) ∘ SymbolTable.to_list

def toPrintStatement : string × CType → option string | (name, ctype) :=
match ctype with
| CType.storage (CType.storage CDouble) :=
if disableMatrixPrinting then none else some $ "printMat_(" ++ name ++ ");\n"
| CType.storage CDouble :=
if disableMatrixPrinting then none else some $ "printArray_(" ++ name ++ ");\n"
| CType.double := some $ "printf(\"" ++ name ++ ": %f\\n\"," ++ name ++ ");\n"
| _ := none
end

def insertPrintf : SymbolTable -> string :=
string.join ∘ list.filter_map (toPrintStatement ∘ prod.map id TensorType.toCType) ∘ SymbolTable.to_list

def addHeaderFooter : SymbolTable × string → string
| (st, s)
  := "#include \"prefix.cpp\"\n"
  ++ insertDecls st
  ++ s
  ++ (if disablePrinting then "" else "printf(\"results:\\n\");" ++ insertPrintf st)
  ++ "#include \"suffix.cpp\"\n"

-- compiles, writes, and formats program
def compile (prog : M Prog) : io unit :=
  let outName := "out_lean.cpp" in do
  handle ← io.mk_file_handle outName io.mode.write,
  let result : string := addHeaderFooter $ (runInfo (prog >>= Prog.to_c)).map id buffer.to_string,
  io.fs.write handle result.to_char_buffer,
  io.fs.close handle,
  if disableClangFormat then return () else io.cmd {cmd := "clang-format", args := ["-i", outName]} >> return ()

--#eval compile (return $ Prog.expr $ E.lit 222)

end codegen

section input_combinators

def fresh : string -> TensorType -> M string | n t := do
  s ← get,
  let name := n ++ s.counter.repr,
  modify $ λ (s : MState), {s with counter := s.counter+1, symbolTable := s.symbolTable.insert name t},
  return $ name

open TensorType
def cdouble := TensorType.atom ValueType.float
def cint := TensorType.atom ValueType.int
def cstorage (x : TensorType) := TensorType.storage x
def csparse (x : TensorType) := TensorType.sparse x

@[reducible] def VectorGen := Gen E (Gen unit E)
@[reducible] def MatrixGen := Gen E (Gen E (Gen unit E))
@[reducible] def CubeGen   := Gen E (Gen E (Gen E (Gen unit E)))

def m (var : string) : M MatrixGen := do
  let file := matrixFile,
  var ← E.ident <$> fresh var (csparse (csparse cdouble)),
  let gen := functor.map (functor.map singletonGen) $ functor.map externGen (externGen $ var),
  return $ {gen with initialize := Prog.store var (E.call1 (E.ident "loadmtx")
    (E.ident $ "\"" ++ file ++ "\""))}

def v (var : string) : M VectorGen := do
  let file := vectorFile,
  var ← E.ident <$> fresh var (csparse cdouble),
  let gen := singletonGen <$> externGen var,
  return $ { gen with initialize := Prog.store var
    $ E.call1 (E.ident "loadvec") (E.ident $ "\"" ++ file ++ "\"") }

def vvar  := do
  var <- E.ident <$> fresh "t" (cstorage cdouble),
  return $ externStorageGen var
def mvar  := do
  var <- E.ident <$> fresh "t" (cstorage (cstorage cdouble)),
  return $ externStorageGen <$> (externStorageGen var)
def floatVar := E.ident <$> fresh "v" cdouble
def intVar := E.ident <$> fresh "v" cint
end input_combinators

variables {ι ι' α : Type}

-- is this already defined?
def applicative.map2 {α β γ} {m} [applicative m] (f : α → β → γ) : m α → m β → m γ
| a b := f <$> a <*> b

infixl ` <.> `:70 := applicative.map2 (*)

def contractionM : M (Gen E (Gen unit E) → Gen unit E) := do
  acc <- E.ident <$> fresh "acc" cdouble,
  return $ contraction acc
def sum1 (x : M VectorGen) := contractionM <*> x
def sum2 (x : M MatrixGen) : M VectorGen := do
  g ← x,
  c ← contractionM,
  return (c <$> g)
def sum3 (x : M CubeGen) : M MatrixGen := do
  c ← contractionM,
  g ← x,
  return $ functor.map (functor.map c) g

def M.repl1  (x : M (Gen ι α)) : M (Gen E (Gen ι α)) := repeat <$> intVar <*> x
def M.repl2  (x : M (Gen ι (Gen ι' α))) : M (Gen ι (Gen E (Gen ι' α))) := do
i ← intVar, (functor.map (repeat i)) <$> x

def down : Gen unit (Gen unit α) → Gen unit α := flatten_snd
def down2 : Gen unit (Gen unit (Gen unit α)) → Gen unit α := down ∘ down
prefix ` ↓ `: 19 := functor.map down
prefix ` ↓ `: 19 := functor.map down2
infixl ` <~ `:20 := applicative.map2 Accumulable.accum

-- write output and clang_format it
def go (mgen : M (Gen unit Prog)) : io unit := compile $ do
  gen <- mgen,
  return $ gen.initialize <;> (loop gen)

section examples

instance flatten_snd.has_lift {α} : has_coe (Gen unit (Gen unit α)) (Gen unit α) := ⟨flatten_snd⟩
instance M.has_lift {α β} [has_coe α β] : has_coe (M α) (M β) := ⟨functor.map coe⟩

@[reducible] def mgup := M (Gen unit Prog)
def M.toProg (g : M (Gen unit Prog)) : Prog := let g := runM g in g.initialize <;> loop g
def M.toStr' (g : M (Gen unit Prog)) : string :=
  let g := runInfo $ do g ← g, (g.initialize <;> loop g).to_c in g.snd.to_string
def M.toStr (g : M (Gen unit Prog)) : string :=
  let g := runInfo $ do g ← g, (g.initialize <;> loop g).to_c_opt in g.snd.to_string

def egV    : mgup := ↓ vvar <~ v "u"
def egVV   : mgup := ↓ vvar <~ v "u" <.> v "v"
def egMM   : mgup := ↓ mvar <~ m "u" <.> m "v"
def egVVV  : mgup := ↓ vvar <~ v "u" <.> v "v" <.> v "w"
-- AB^t
def egmul2 : mgup := ↑ (mvar <~ sum3 ((m "A").repl2 <.> (m "B").repl1))

#eval egVV.toStr
--#eval go egmul2

end examples

-- todo: addGen
