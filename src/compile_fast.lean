import tactic
import data.list.alist
import control.monad.basic

def disableClangFormat := ff

class has_hmul (α β : Type*) (γ : out_param Type*) :=
  (mul : α → β → γ)
instance hmul_of_mul {α : Type*} [has_mul α] : has_hmul α α α := ⟨has_mul.mul⟩
infix ` ⋆ `:71 := has_hmul.mul

@[reducible] def Ident := string
@[reducible] def Label := string

@[derive [decidable_eq, fintype]]
inductive BinOp | add | sub | mul | lt | eq | lit_eq | and | or | min | max

/-- Expressions for a simple imperative language. -/
@[derive decidable_eq]
inductive E
| lit     : ℕ → E
| ident   : Ident → E
| not     : E → E
| bin_op  : BinOp → E → E → E
| access  : E → E → E
| ternary : E → E → E → E
| inline_code : string → E

-- todo simplify
| incr  : E → E
| attr  : E → E → E
| arrow_op : E → E → E
| call0 : E → E
| call1 : E → E → E
| call2 : E → E → E → E


/-- Statements for a simple imperative language, including sequencing. -/
inductive Prog
| skip
| accum (dst : E) (val : E)
| store (dst : E) (val : E)
| «if» (b : E) (cons : Prog) (alt : Prog)
| seq (a b : Prog)

| block (body : Prog)
| time  (n : string) (body : Prog)

| while (cond : E) (body : Prog)
| for (var bound : E) (body : Prog)

-- todo simplify
| declare (var : E) (initializer : E)
| auto (var : E) (initializer : E)

| inline_code (code : string)
| expr : E → Prog
| comment (c : string)

--def Prog.accum := λ l r, Prog.store l (l + r)

@[pattern]
def Prog.if1 (b : E) (cons : Prog) : Prog := Prog.if b cons Prog.skip

@[pattern] def E.false : E := E.lit 0
@[pattern] def E.true  : E := E.lit 1

namespace E

def neg : E → E
| (E.true) := E.false
| (E.false) := E.true
| e := e.not

infixr ` <;> `:1 := Prog.seq
infixr ` ;; `:1 := Prog.seq
infixr (name := seq) ` ; `:1 := Prog.seq
--instance : has_andthen Prog Prog Prog := ⟨Prog.seq⟩

instance : has_zero E := ⟨E.lit 0⟩
instance : has_one E  := ⟨E.lit 1⟩
instance : inhabited E := ⟨0⟩

instance : has_coe string E := ⟨E.ident⟩
end E

def BinOp.mk_type : BinOp → Type
| _ := E → E → E

-- a little smart
def BinOp.mk : Π (b : BinOp), BinOp.mk_type b
| BinOp.and := λ x y,
  match x, y with
  | E.true, y := y
  | x, E.true := x
  | E.false, y := E.false
  | x, E.false := E.false
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
| BinOp.add := λ x y,
  match x, y with
  | E.lit a, E.lit b := E.lit (a+b)
  | E.lit 0, x := x
  | x, E.lit 0 := x
  | _, _ := E.bin_op BinOp.add x y
  end
| BinOp.mul := λ x y,
  match x, y with
  | E.lit a, E.lit b := E.lit (a*b)
  | E.lit 0, x := E.lit 0
  | x, E.lit 0 := E.lit 0
  | E.lit 1, x := x
  | x, E.lit 1 := x
  | _, _ := E.bin_op BinOp.mul x y
  end
| b := E.bin_op b

instance : has_coe_to_fun BinOp BinOp.mk_type := ⟨BinOp.mk⟩

instance : has_add E := ⟨BinOp.add⟩
instance : has_sub E := ⟨BinOp.sub⟩
instance : has_mul E := ⟨BinOp.mul⟩


namespace E
def store   : E → E → Prog := Prog.store
def accum   : E → E → Prog := Prog.accum
def declare : E → E → Prog := Prog.declare
end E

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
structure Context :=
(true_conditions  : list E)
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
def BinOp.to_c : BinOp → string
| BinOp.add := "+"
| BinOp.sub := "-"
| BinOp.mul := "*"
| BinOp.lt := "int_lt"
| BinOp.eq := "int_eq"
| BinOp.lit_eq := "=="
| BinOp.and := "&&"
| BinOp.or := "||"
| BinOp.min := "min"
| BinOp.max := "max"

def wrap (s : string) : string := "(" ++ s ++ ")"

def E.to_c : E → string
| (E.lit i)                  := repr i
| (E.ident i)                := i
| (E.incr i)                 := wrap $ i.to_c ++ "++"
| (E.not i)                  := "!" ++ wrap i.to_c
| (E.bin_op BinOp.min e1 e2) := BinOp.min.to_c ++ (wrap $ e1.to_c ++ "," ++ e2.to_c)
| (E.bin_op BinOp.max e1 e2) := BinOp.max.to_c ++ (wrap $ e1.to_c ++ "," ++ e2.to_c)
| (E.bin_op BinOp.lt e1 e2)  := BinOp.lt.to_c ++ (wrap $ e1.to_c ++ "," ++ e2.to_c)
| (E.bin_op BinOp.eq e1 e2)  := BinOp.eq.to_c ++ (wrap $ e1.to_c ++ "," ++ e2.to_c)
| (E.bin_op op e1 e2)        := wrap $ e1.to_c ++ op.to_c ++ e2.to_c
| (E.ternary c t e)          := wrap $ wrap c.to_c ++ "?" ++ t.to_c ++ ":" ++ e.to_c
| (E.access e i)             := e.to_c ++ "[" ++ i.to_c ++ "]"
| (E.attr e i)               := e.to_c ++ "." ++ i.to_c
| (E.arrow_op e i)              := e.to_c ++ "->" ++ i.to_c
| (E.inline_code s)          := s
| (E.call0 f)                := f.to_c ++ wrap ""
| (E.call1 f a1)             := f.to_c ++ (wrap a1.to_c)
| (E.call2 f a1 a2)          := f.to_c ++ (wrap $ a1.to_c ++ "," ++ a2.to_c)

def emit (str : string) : M unit := modify $ λ s : MState,
{ s with buffer := s.buffer.append_string str }
def emitLine (s : string) : M unit := do emit $ s ++ ";"

namespace Prog

def to_c : Prog → M unit
| (expr e)          := emitLine $ e.to_c
| (accum dst val)   := emitLine $ dst.to_c ++ " += " ++ val.to_c
| (store dst val)   := emitLine $ dst.to_c ++ " = " ++ val.to_c
| (declare dst val) := emitLine $ "index " ++ dst.to_c ++ " = " ++ val.to_c
| (auto dst val)    := emitLine $ "auto " ++ dst.to_c ++ " = " ++ val.to_c
| (seq a b)         := a.to_c >> b.to_c
| (while c body)    := emit ("while" ++ wrap c.to_c ++ "{") >> body.to_c >> emit "}"
| (for i n body)    := emit ( "for" ++ wrap (i.to_c ++ "= 0;" ++ i.to_c ++ "<" ++ n.to_c ++ ";" ++ i.to_c++"++") ++ "{"
                          ) >> body.to_c >> emit "}"
| (inline_code s)   := emit s
| (skip)            := emit ""
| (comment s)       := emit $ "// " ++ s ++ "\n"
| (if1 E.false t)   := emit ""
| (if1 E.true t)    := t.to_c
| (if1 c t)         := do
    emit "if (" >> emit c.to_c >> emit ") {",
      t.to_c,
    emit "}"
| («if» c t e)      := do
    emit "if (" >> emit c.to_c >> emit ") {",
      t.to_c,
    emit "}", emit " else {",
      e.to_c,
    emit "}"
| (block p)         := emit "{" >> p.to_c >> emit "}"
| (time n p)          :=
  emit "{" >>
  ( emit ("cout << \"\\ntiming (" ++ n ++ "):\" << endl;") >>
    emit "out_val = 0.0; auto t1 = std::chrono::high_resolution_clock::now();" >>
    p.to_c >>
    emit "auto t2 = std::chrono::high_resolution_clock::now();" >>
    emit "cout << \"out: \" << out_val << endl;" >>
    emit "std::cout << \"took: \" << std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count() << std::endl;"
  ) >> emit "}"
end Prog

def M.runInfo {α} (m : M α) : SymbolTable × buffer char :=
(λ s : MState, (s.symbolTable, s.buffer)) ((m.run ∅).run emptyContext).snd

def M.runBuffer {α} (m : M α) : string := m.runInfo.snd.to_string

def addHeaderFooter : string → string :=
λ s, "#include \"prefix.cpp\"\n" ++ s ++ "#include \"suffix.cpp\"\n"

def compile (progs : (list Prog)) : io unit :=
  let outName := "out_lean.cpp" in do
  handle ← io.mk_file_handle outName io.mode.write,
  let result : string := addHeaderFooter $ (progs.mmap (Prog.to_c ∘ Prog.block)).runBuffer,
  io.fs.write handle result.to_char_buffer,
  io.fs.close handle,
  if disableClangFormat then return () else io.cmd {cmd := "clang-format", args := ["-i", outName]} >> return ()

def comp : Prog → io unit := compile ∘ pure

-- #check monad.mapm

end codegen

section G

variables {α ι γ β : Type}

local infixl (name := and) ` && `:70 := BinOp.and
local infixl (name := or)  ` || `:65 := BinOp.or
local infix  (name := lt)  ` < `:71  := BinOp.lt
infix  (name := eq)  ` == `:71 := BinOp.eq
infix  (name := teq) ` === `:71 := BinOp.lit_eq
infix  (name := ne)  ` != `:71 := λ a b, (BinOp.eq a b).neg
@[pattern] def E.le : E → E → E := λ a b, BinOp.or (a < b) (a == b)
local infix  (name := le) ` ≤ `:71  := E.le

--notation e `⟦` k `⟧` := e.access k

structure G (ι α : Type) :=
  (index : ι)   (value : α)
  (ready : E)   (valid : E)
  (init : Prog) (next : Prog)

def G.empty [inhabited ι] [inhabited α] : G ι α :=
{ index := default, value := default, ready := E.false, valid := E.false, init := Prog.skip, next := Prog.skip }

structure View (ι α : Type) := (value : ι → α)

def constView (ι : Type) (v : α) : View ι α := ⟨λ _, v⟩
prefix (name := const) ` ⇑ ` := constView
-- instance : has_coe (α → β) (View α β) := ⟨View.mk⟩

instance {ι : Type*} : functor (G ι) :=
{ map := λ _ _ f g, { g with value := f g.value } }

instance {ι : Type*} : functor (View ι) :=
{ map := λ _ _ f v, { v with value := f ∘ v.value } }

instance View.has_hmul [has_hmul α β γ] : has_hmul (View ι α) (View ι β) (View ι γ) :=
⟨λ a b, ⟨λ i, a.value i ⋆ b.value i⟩⟩

namespace G
def iv {ι ι' α α'} (i : ι → ι') (v : α → α') : G ι α → G ι' α'
:= λ g, { g with value := v g.value, index := i g.index }

def mul [has_hmul α β γ] (a : G E α) (b : G E β) : G E γ :=
{ index := BinOp.max a.index b.index,
  value := a.value ⋆ b.value,
  ready := a.ready && b.ready && a.index == b.index,
  next  := Prog.if (a.index < b.index ||
                   (a.index == b.index && a.ready.neg))
                        a.next
                        b.next,
  valid := a.valid && b.valid,
  init  := a.init; b.init,
}
instance [has_hmul α β γ] : has_hmul (G E α) (G E β) (G E γ) := ⟨mul⟩

instance smul_G [has_smul E α] : has_smul E (G E α) :=
⟨λ s v, { v with value := s • v.value } ⟩
instance smul_unit [has_smul E α] : has_smul E (G unit α) :=
⟨λ s v, { v with value := s • v.value } ⟩
instance smul_base [has_hmul E α α] : has_smul E α := ⟨(⋆)⟩

example : has_smul E E := infer_instance

def add [has_smul E α] [has_mul α] [has_add α] (a b : G E α) : G E α :=
let current := BinOp.min a.index b.index in
{ index := current,
  value := (a.index == current) • a.value + (b.index == current) • b.value,
  ready := a.ready || b.ready,
  next  := Prog.if (a.index < b.index ||
                   (a.index == b.index && a.ready.neg && b.ready)) -- ($) <$>
             a.next
             $ (Prog.if (b.index < a.index ||
                        (a.index == b.index && b.ready.neg && a.ready))
                  b.next
                  (a.next; b.next)),
  valid := a.valid || b.valid,
  init  := a.init; b.init,
}

instance [has_mul α] [has_smul E α] [has_add α] : has_add (G E α) := ⟨add⟩

def mul_unit_const_r [has_hmul α β γ] (a : G unit α) (b : β) : G unit γ := (⋆ b) <$> a
def mul_unit_const_l [has_hmul α β γ] (a : α) (b : G unit β) : G unit γ := (λ v, a ⋆ v) <$> b
def mulViewR [has_hmul α β γ] (a : G ι α) (b : View ι β) : G ι γ :=
(⋆ b.value a.index) <$> a
def mulViewL [has_hmul α β γ] (a : View ι α) (b : G ι β) : G ι γ :=
(λ v, a.value b.index ⋆ v) <$> b

instance GV.has_hmul [has_hmul α β γ] : has_hmul (G ι α) (View ι β) (G ι γ) := ⟨G.mulViewR⟩
instance VG.has_hmul [has_hmul α β γ] : has_hmul (View ι α) (G ι β) (G ι γ) := ⟨G.mulViewL⟩
instance unit_const_r.has_hmul [has_hmul α β γ] : has_hmul (G unit α) β (G unit γ) := ⟨mul_unit_const_r⟩
instance unit_const_l.has_hmul [has_hmul α β γ] : has_hmul α (G unit β) (G unit γ) := ⟨mul_unit_const_l⟩
instance [has_mul α] : has_mul (G E α) := ⟨(⋆)⟩

end G

section simple_streams

def interval (i : E) (counter : E) (lower upper : E) : G E E :=
{ index := i.access counter, value := counter, ready := E.true, valid := counter < upper,
  init  := counter.declare lower, next  := counter.accum 1,
}

def range (counter bound : E) : G E E :=
{ index := counter, value := counter, ready := E.true, valid := counter < bound,
  init  := counter.declare 0, next  := counter.accum 1 }

def View.to_gen (counter bound : E) (view : View E α) : G E α := view.value <$> range counter bound

end simple_streams

section csr

/- implementation of composable sparse rval level -/
section rval

-- in TACO terminology, i = n_crd, v = n_pos. var indexes i.
structure csr := (i v var : E)

def csr.of (name : string) (n : ℕ) : csr :=
  let field (x : string) := E.ident $ name ++ n.repr ++ x in
  { i := field "_crd", v := field "_pos", var := field "_i" }

def csr'.of (name : string) (n : ℕ) : csr :=
  let field  (x : string) := E.ident $ name ++ n.repr ++ x in
  let field' (x : string) := E.ident $ name ++ (n+1).repr ++ x in
  { i := field "_crd", v := field' "_pos", var := field "_i" }

def csr.level : csr → E → G E E := λ csr loc,
interval csr.i csr.var (csr.v.access loc) (csr.v.access (loc+1))
def G.level   : csr → G E E → G E (G E E) := functor.map ∘ csr.level
def G.leaf    :   E → G E E → G E E       := functor.map ∘ E.access -- λ v, functor.map $ λ i, E.access v i

end rval

/- csr lval v3 -/
/- implementation of composable sparse lval level -/
section csr_lval
@[reducible] def loc := E
structure il :=
  (crd  : loc → E)
  (push : E → (loc → Prog) → Prog × loc)
structure vl  (α : Type) :=
  (pos  : loc → α)
  (init : loc → Prog)
structure lvl (α : Type) extends il, vl α.
instance : functor lvl := { map := λ _ _ f l, { l with pos := f ∘ l.pos } }

def sparse_index (indices : E) (bounds : E × E) : il :=
let upper := bounds.2, lower := bounds.1, current := indices.access (upper-1) in
let loc := upper-1 in
{ crd  := indices.access,
  push := λ i init,
    let prog := Prog.if1 (lower == upper || i != current)
                      ((upper.accum 1); init loc);
                     current.store i
    in (prog, loc) }

def dense_index (dim : E) (counter : E) (base : E) : il :=
{ crd  := id,
  push := λ i init,
    let l i  : loc := base * dim + i,
        prog : Prog := Prog.while (counter ≤ i) (init (l counter); counter.accum 1)
    in (prog, l i) }

def interval_vl (array : E) : vl (E × E) :=
let fn := array.access in
{ pos  := λ loc, (array.access loc, array.access (loc + 1)),
  init := λ loc, (fn (loc + 1)).store (fn loc) }

def dense_vl    (array : E) : vl E :=
{ pos := λ loc, array.access loc,
  init := λ loc, (array.access loc).store 0 }

def implicit_vl : vl E := { pos := id, init := λ _, Prog.skip }

-- def base (array : E) : lvl E := { i_shift := λ _ i, array.access i,  }

def rev_fmap_comp {f} [functor f] (x : α → f β) (y : β → f γ) := functor.map y ∘ x
infixr ` ⊚ `:90 := rev_fmap_comp
def rev_app : α → (α → β) → β := function.swap ($)
infixr ` & `:9 := rev_app

-- this combinator combines an il with a vl to form a lvl.
-- the extra parameter α is used to thread the primary argument to a level through ⊚.
--   see dcsr/csr_mat/dense below
def with_values : (α → il) → vl β → α → lvl β := λ i v e, lvl.mk (i e) v

def dense_mat (d₁ d₂ : E) := 0 &
  (with_values (dense_index d₁ "i1") implicit_vl) ⊚
  (with_values (dense_index d₂ "i2") $ dense_vl "values")

def cube_lvl := 0 &
  (with_values (dense_index 11 "i1") implicit_vl) ⊚
  (with_values (dense_index 7 "i2") implicit_vl) ⊚
  (with_values (dense_index 5 "i3") $ dense_vl "values")

def sparse_vec := (0, E.ident "size") &
  (with_values (sparse_index "A1_crd") (dense_vl "A_vals"))

def dcsr := (interval_vl "A1_pos").pos 0 &
  (with_values (sparse_index "A1_crd") (interval_vl "A2_pos")) ⊚
  (with_values (sparse_index "A2_crd") (dense_vl "A_vals"))

def csr_mat := 0 &
  (with_values (dense_index 2000 "i1") (interval_vl "B2_pos")) ⊚
  (with_values (sparse_index "B2_crd") (dense_vl "B_vals"))

end csr_lval

/- csr lval v2. TODO remove -/
structure lval (α : Type) := (push : E → Prog × α)
instance : functor lval := { map := λ _ _ f l, { l with push := prod.map id f ∘ l.push } }

def csr.base (csr : csr) : E×E := ((csr.v.access 0), (csr.v.access 1))
def csr.lval (csr : csr) (bounds : E×E) : lval (E×E)  :=
let upper := bounds.2, lower := bounds.1 in
{ push := λ i,
  let prog := Prog.if1 (lower == upper || (i != csr.i.access (upper-1) &&
                                            (csr.v.access upper != csr.v.access (upper-1))))
                 (upper.accum 1; (csr.v.access upper).store (csr.v.access (upper-1)));
               (csr.i.access (upper-1)).store i,
      value := ((csr.v.access (upper-1)), (csr.v.access upper)) in (prog, value)
}

def csr.vec (csr : csr) (bounds : E×E) : lval E :=
let upper := bounds.2, lower := bounds.1 in
{ push := λ i, (Prog.if1 (lower == upper || (i != csr.i.access (upper-1) &&
                                            (0 != csr.v.access (upper-1))))
                 (upper.accum 1; (csr.v.access (upper-1)).store 0);
               (csr.i.access (upper-1)).store i, csr.v.access (upper-1))
}

/- csr lval v1. TODO remove -/
structure pre  := (pre : Prog)
structure new  := (new : Prog) -- (acc : E → α)
structure post := (post : Prog)

-- push values at the leaf level
def push_value (var val_array outer_var : E) : new × post × E :=
({new := (val_array.access outer_var).store 0}, ⟨Prog.skip⟩, (val_array.access var))

-- if pack is true, we allow for an rval that produces duplicate coordinates and de-duplicate them as they are aggregated
def push_level_pack' (pack : bool) (csr : csr) (k : E → new × post × α) : (E → new × post × (E → pre × α))
:= λ outer_var,
( { new := (csr.v.access outer_var).store (csr.var+1) },
  { post := (csr.v.access (outer_var+1)).store (csr.var+1); (k csr.var).2.1.post },
   λ i, (⟨(if pack then Prog.if1 (csr.var < csr.v.access outer_var || i != csr.i.access csr.var) else id) $
             csr.var.accum 1; (csr.i.access csr.var).store i; (k csr.var).1.new⟩,
         (k csr.var).2.2))

def push_level_pack : csr → (E → new × post × α) → (E → new × post × (E → pre × α)) :=
push_level_pack' tt
def push_level      : csr → (E → new × post × α) → (E → new × post × (E → pre × α)) :=
push_level_pack' ff

def vec_lval' (n : string) :=
prod.snd $ (push_level_pack (csr.of n 1) $ push_value (csr.of n 1).var (E.ident $ n ++ "_vals")) 0
def mat_lval' (n : string) :=
prod.snd $ (push_level_pack (csr.of n 1) $ push_level_pack (csr.of n 2) $ push_value (csr.of n 2).var (E.ident $ n ++ "_vals")) 0
def mval (n : string) :=
prod.snd $ (push_level (csr.of n 1) $ push_level (csr.of n 2) $ push_value (csr.of n 2).var (E.ident $ n ++ "_vals")) 0
def cub_lval' (n : string) :=
prod.snd $ (push_level_pack (csr.of n 1) $ push_level_pack (csr.of n 2) $ push_level_pack (csr.of n 3) $ push_value (csr.of n 3).var (E.ident $ n ++ "_vals")) 0
def cub_lval'' (n : string) :=
prod.snd $ (push_level (csr.of n 1) $ push_level (csr.of n 2) $ push_level (csr.of n 3) $ push_value (csr.of n 3).var (E.ident $ n ++ "_vals")) 0
#check mat_lval'

end csr

def indexed_mat_lval (var : E) (i j v : E) := ((var.access i).access j).accum v

def fmap1 {α β f} [functor f] : (α → β) → f α → f β := functor.map
def fmap2 {α β f} [functor f] : (α → β) → f (f α) → f (f β) := functor.map ∘ functor.map

class Compile (l r : Type) := (eval : l → r → Prog)
class Scalar (α : Type) := (fold : α → E → Prog) (value : α → E)
instance : Scalar E := ⟨λ l r, l.accum r, id⟩

-- offset into array:
instance : Scalar (E × E) := ⟨λ l r, (l.2.access l.1).accum r, λ l, l.2.access l.1⟩

--instance discard.eval : Compile unit E := ⟨λ _ _, Prog.skip⟩
instance base.eval [Scalar α] : Compile α E :=
{ eval := λ l v, Scalar.fold l v }
-- todo remove
instance base.eval' : Compile (E → Prog) E :=
{ eval := λ acc v, acc v }

instance unit.eval [Compile α β] : Compile α (G unit β) :=
{ eval := λ acc v,
    v.init; Prog.while v.valid
      (Prog.if1 v.ready (Compile.eval acc v.value) ; v.next) }

instance lvl.eval [Compile α β] : Compile (lvl α) (G E β) :=
{ eval := λ storage v,
    let (push_i, loc) := storage.push v.index storage.init in
    v.init ;
    Prog.while v.valid
      (Prog.if1 v.ready
        (push_i;
         Compile.eval (storage.pos loc) v.value);
      v.next) }

instance lval.eval [Compile α β] : Compile (lval α) (G E β) :=
{ eval := λ acc v,
    let loop_body := acc.push v.index in
    v.init ;
    Prog.while v.valid
      (Prog.if1 v.ready
        (loop_body.1;
         Compile.eval loop_body.2 v.value);
      v.next) }

-- instance unit.bool [Scalar α] [Compile α β] : Compile α (G unit β) :=
-- { eval := λ acc v,
--     v.init; Prog.while (v.valid && (Scalar.value acc).neg)
--       (Prog.if1 v.ready (Compile.eval acc v.value) ; v.next) }

instance level.eval  [Compile α β] : Compile (E → α) (G E β) :=
{ eval := λ acc v,
    v.init; Prog.while v.valid
      (Prog.if1 v.ready (Compile.eval (acc v.index) v.value);
      v.next) }

instance level_pre.eval [Compile α β] : Compile (E → pre × α) (G E β) :=
{ eval := λ acc v,
    let loop_body := acc v.index in
    v.init ;
    Prog.while v.valid
      (Prog.if1 v.ready
        (loop_body.1.pre;
         Compile.eval loop_body.2 v.value);
      v.next) }

instance level_outer_post.eval [Compile α β] : Compile (post × α) β :=
{ eval := λ lhs v, let (x, acc) := lhs in Compile.eval acc v; x.post }

-- janky map-based generator:
-- i   = get<0>(x->first)
-- j   = get<1>(x->first)
-- val = x.second
def coo_rval (n : ℕ) (matrix var : E) : (G E E) :=
let call (a b : E) := E.call0 (a.attr b) in
{ index := E.call1 (E.ident $ "get<" ++ n.repr ++ ">") $ var.arrow_op "first",
  value := var.arrow_op "second",
  ready := E.true,
  valid := E.neg $ var === call matrix "end",
  init  := Prog.auto var $ call matrix "begin",
  next  := Prog.expr $ var.incr,
}
def coo_rval_inner (n : ℕ) (matrix var : E) : (G E E) :=
{ coo_rval n matrix var with
  next := Prog.inline_code "break;",
  valid := E.true,
  init := Prog.skip }

def coo_vector_rval (matrix var : E) : (G E E) := coo_rval 0 matrix var
def coo_matrix_rval (matrix var : E) : G E (G E E) :=
fmap1 (λ _, coo_rval_inner 1 matrix var) $ coo_vector_rval matrix var
def coo_cube_rval   (matrix var : E) : G E (G E (G E E)) :=
fmap2 (λ _, coo_rval_inner 2 matrix var) $ coo_matrix_rval matrix var

namespace G
def contract (g : G ι α) : G unit α := { g with index := () }
def sum1 : G E α → G unit α := contract
def sum2 : (G E (G E α)) → (G unit (G unit α)) :=
(functor.map $ sum1) ∘ contract
def sum2' : (G E (G E E)) → (G unit (G unit E)) :=
(functor.map $ sum1) ∘ contract
def sum3'  : G E (G E (G E α)) → G unit (G unit (G unit α)) :=
(functor.map $ sum2) ∘ contract
def sum3 : G E (G E (G E E)) → G unit (G unit (G unit E)) :=
(functor.map $ sum2) ∘ contract
def sum_inner : G E (G E (G E E)) → G E (G E (G unit E)) := functor.map $ functor.map G.contract

end G

def v  : G E E       := G.leaf "V_vals" $ ((csr.of "V" 1).level 0)
def A  : G E (G E E) := (csr.of "A" 1).level 0 & G.level (csr.of "A" 2) ⊚ G.leaf "A_vals"
def A_csr  : G E (G E E) :=
  let dense : G E E := range "_i" 2000 in
  dense & G.level (csr.of "A" 2) ⊚ G.leaf "A_vals"
def B_csr  : G E (G E E) :=
  let dense : G E E := range "_i" 2000 in
  dense & G.level (csr.of "B" 2) ⊚ G.leaf "B_vals"
def B  : G E (G E E) := (csr.of "B" 1).level 0 & G.level (csr.of "B" 2) ⊚ G.leaf "B_vals"
def C  : G E (G E (G E E)) := (csr.of "C" 1).level 0 & G.level (csr.of "C" 2) ⊚ G.level (csr.of "C" 3) ⊚ G.leaf "C_vals"
def D  : G E (G E (G E E)) := (csr.of "D" 1).level 0 & G.level (csr.of "D" 2) ⊚ G.level (csr.of "D" 3) ⊚ G.leaf "D_vals"
def M_  : G E (G E E) := G.leaf "M_vals" <$> ((csr.of "M" 1).level 0).level (csr.of "M" 2)

def exec {l r} [Compile l r] := @Compile.eval l r

def single (x : α) := (⇑ E x).to_gen "i" 1
#eval (single (3 : E)).ready.to_c
def eg00  := exec (E.ident "out") (E.lit 2)
def eg00' := exec (E.ident "out") (v.contract)
def eg01 := exec (Prog.accum "out") (G.contract <$> A.contract)
def eg02 := exec (Prog.accum "out") (G.sum2 $ A⋆B)
def eg03 := exec (Prog.accum "out") (G.sum2 $ (⇑ E v) ⋆ A)
def eg04 := exec (Prog.accum "out") (G.sum3 $ ((⇑ E) <$> A) ⋆ ⇑ E B ) -- (i,k)*(j,k)

def inner_prod := (fmap1 (⇑ E) A) ⋆ ⇑ E B -- (i,k)*(j,k)
-- (i,j)*(j,k)
def comb_rows : G E (G E (G unit E)) := G.sum_inner $ (fmap2 (⇑ E) A) ⋆ ⇑ E B

def me := Prog.time "me"
def ta := Prog.time "taco"

def c0 : csr := { i := "", v := "A1_pos", var := "" }
def c1 : csr := csr'.of "A" 1
def c2 : csr := { i := "A2_crd", v := "A_vals", var := "" }
def A_lval := c0.base & ( c1.lval ⊚ c2.vec )

def out : E := "out_val"

def eg05 := exec (Prog.accum "out") $ G.sum3 $ (fmap2 (⇑ E) A) ⋆ (fmap1 (⇑ E) B) -- (i,j)*(i,k)
def matsum := comb_rows.sum2
def eg06 := exec (Prog.accum "out") matsum
def eg07 := exec (indexed_mat_lval "out") (A⋆B)
def ref_vector (n : string) := (coo_vector_rval (E.ident $ n ++ ".data") "entry")
def ref_matrix (n : string) := (coo_matrix_rval (E.ident $ n ++ ".data") "entry")
def ref_cube   (n : string) := (coo_cube_rval   (E.ident $ n ++ ".data") "entry")
def ref_x := ref_matrix "x"
def ref_y := ref_matrix "y"
def ref_M := ref_matrix "M"
def eg18 := exec (λ (_ _ : E), Prog.accum "out") A
def load_AB' := [exec (mat_lval' "A") ref_x, exec (mat_lval' "B") ref_x]
def load_AB : list Prog := [
  Prog.time "gen A" $ exec (mat_lval' "A") (ref_matrix "x"),
  Prog.time "gen B" $ exec (mat_lval' "B") (ref_matrix "y") ]
def eg19 := load_AB' ++ [Prog.time "me" $ exec (mat_lval' "out") $ A⋆B]
def taco_ijk := Prog.inline_code "taco_ijk_sum();"
def eg21 := exec (vec_lval' "out") v
def eg22 := me $ exec (mat_lval' "out") A
def eg23 := load_AB' ++ [Prog.time "me" $ exec (mval "out") $ inner_prod.sum_inner]
def eg24 := exec (λ i, (Prog.accum $ out.access i)) ((λ (i : E), 2*i) <$> (range "i" 10))
def eg25 := exec (Prog.accum out) ((λ (i : E), 2*i) <$> (range "i" 10)).contract
def eg20 := load_AB ++ [me $ eg06, Prog.time "taco" $ taco_ijk]
def eg26 := load_AB ++ [me $ exec out $ G.sum2 (comb_rows), Prog.time "taco" $ taco_ijk]
def eg27 := load_AB ++ [me $ exec (mval "out") $ comb_rows]

def load := [
  exec A_lval (ref_matrix "x"),
  exec (mat_lval' "B") (ref_matrix "y"),
  exec (cub_lval' "C") (ref_cube "c"),
  exec (cub_lval' "D") (ref_cube "c"),
  exec (vec_lval' "V") (ref_vector "v")]

def eg28 := load_AB ++ [
  Prog.time "me" $ exec (mval "out") $ inner_prod.sum_inner,
  Prog.time "taco" $ Prog.inline_code "taco_ikjk();" ]

def eg29 := load ++ [exec (mval "out") (A + B)]
def eg30 := exec out (C + D).sum3

--#eval comp $ exec A_lval A
--#eval compile $ [exec A_lval (ref_matrix "x"), me $ exec out $ G.sum2 $ A ]
--#eval compile $ [exec sparse_vec (ref_vector "v")] -- , me $ exec out $ G.sum2 $ A ]
--#eval compile $ [exec dcsr (ref_matrix "x"), me $ exec out $ G.sum2 $ A ]

-- compare dcsr anc csr:
def eg31 := compile $
[ exec dcsr (ref_matrix "x"),
  exec csr_mat (ref_matrix "x"),
  me $ exec out $ B_csr.sum2,
  me $ exec out $ (ref_matrix "x").sum2 ]
--#eval eg31

end G
