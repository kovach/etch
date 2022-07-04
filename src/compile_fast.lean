import tactic
import data.list.alist
import control.monad.basic

def disableClangFormat := ff

class has_hmul (α β : Type*) (γ : out_param Type*) :=
  (mul : α → β → γ)
instance hmul_of_mul {α : Type*} [has_mul α] : has_hmul α α α := ⟨has_mul.mul⟩
instance mul_of_hmul {α : Type*} [has_hmul α α α] : has_mul α := ⟨has_hmul.mul⟩
infix ` ⋆ `:71 := has_hmul.mul

@[reducible] def Ident := string
@[reducible] def Label := string

@[derive [decidable_eq, fintype]]
inductive BinOp | add | sub | mul | lt | eq | and | or | min | max

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
| pattr : E → E → E
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
| time  (body : Prog)

| while (cond : E) (body : Prog)
| for (var bound : E) (body : Prog)

-- todo simplify
| declare (var : E) (initializer : E)
| auto (var : E) (initializer : E)

| inline_code (code : string)
| expr : E → Prog
| comment (c : string)

@[pattern]
def Prog.if1 (b : E) (cons : Prog) : Prog := Prog.if b cons Prog.skip

def E.store : E → E → Prog := Prog.store
def E.accum : E → E → Prog := Prog.accum
def E.declare : E → E → Prog := Prog.declare

infixr ` <;> `:1 := Prog.seq
instance : has_andthen Prog Prog Prog := ⟨Prog.seq⟩

def BinOp.mk_type : BinOp → Type
| _ := E → E → E

instance : has_zero E := ⟨E.lit 0⟩
instance : has_one E := ⟨E.lit 1⟩
@[pattern] def E.false : E := E.lit 0
@[pattern] def E.true : E := E.lit 1

instance : has_coe string E := ⟨E.ident⟩

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
| BinOp.add := λ x y,
  match x, y with
  | E.lit a, E.lit b := E.lit (a+b)
  | E.lit 0, x := x
  | x, E.lit 0 := x
  | _, _ := E.bin_op BinOp.add x y
  end
| BinOp.mul := λ x y,
  match x, y with
  | E.lit a, E.lit b := E.lit (a+b)
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


infixl ` && `:70 := BinOp.and
infixl ` || `:65 := BinOp.or
infix  ` < `:71  := BinOp.lt
infix  ` == `:71 := BinOp.eq
infix  ` != `:71 := λ a b, (BinOp.eq a b).not
infix  ` ** `:71 := has_hmul.mul
notation e `⟦` k `⟧` := e.access k

prefix `i!`:100 := E.ident

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
| BinOp.lt := "<"
| BinOp.eq := "=="
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
| (E.bin_op op e1 e2)        := wrap $ e1.to_c ++ op.to_c ++ e2.to_c
| (E.ternary c t e)          := wrap $ wrap c.to_c ++ "?" ++ t.to_c ++ ":" ++ e.to_c
| (E.access e i)             := e.to_c ++ "[" ++ i.to_c ++ "]"
| (E.attr e i)               := e.to_c ++ "." ++ i.to_c
| (E.pattr e i)              := e.to_c ++ "->" ++ i.to_c
| (E.inline_code s)          := s
| (E.call0 f)                := f.to_c ++ wrap ""
| (E.call1 f a1)             := f.to_c ++ (wrap a1.to_c)
| (E.call2 f a1 a2)          := f.to_c ++ (wrap $ a1.to_c ++ "," ++ a2.to_c)

def emit (str : string) : M unit := modify $ λ s : MState,
{ s with buffer := s.buffer.append_string str }
def emitLine (s : string) : M unit := do emit $ s ++ ";"

namespace Prog

def to_c : Prog → M unit
| (expr e)        := emitLine $ e.to_c
| (accum dst val) := emitLine $ dst.to_c ++ " += " ++ val.to_c
| (store dst val) := emitLine $ dst.to_c ++ " = " ++ val.to_c
| (declare dst val) := emitLine $ "index " ++ dst.to_c ++ " = " ++ val.to_c
| (auto dst val) := emitLine $ "auto " ++ dst.to_c ++ " = " ++ val.to_c
| (seq a b)       := a.to_c >> b.to_c
| (while c body)  := emit ("while" ++ wrap c.to_c ++ "{") >> body.to_c >> emit "}"
| (for i n body)  := emit ( "for" ++ wrap (i.to_c ++ "= 0;" ++ i.to_c ++ "<" ++ n.to_c ++ ";" ++ i.to_c++"++") ++ "{"
                          ) >> body.to_c >> emit "}"
| (inline_code s) := emit s
| (skip)          := emit ""
| (comment s)     := emit $ "// " ++ s ++ "\n"
| (if1 E.false t) := emit ""
| (if1 E.true t)  := t.to_c
| (if1 c t)       := do
    emit "if (" >> emit c.to_c >> emit ") {",
      t.to_c,
    emit "}"
| («if» c t e)    := do
    emit "if (" >> emit c.to_c >> emit ") {",
      t.to_c,
    emit "}", emit " else {",
      e.to_c,
    emit "}"
| (block p)       := emit "{" >> p.to_c >> emit "}"
| (time p)        := emit "{" >>
  ( emit "auto t1 = std::chrono::high_resolution_clock::now();" >>
    p.to_c >>
    emit "auto t2 = std::chrono::high_resolution_clock::now();" >>
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

#check monad.mapm

end codegen

section G
variables {α ι γ β : Type}

structure G (ι α : Type) :=
  (index : ι)
  (value : α)
  (ready : E)
  (valid : E)
  (init : Prog)
  (next : Prog)

structure View (ι α : Type) :=
  (value : ι → α)

def constView (ι : Type) (v : α) : View ι α := ⟨λ _, v⟩

prefix ` ⇑ ` := constView

instance : has_coe (α → β) (View α β) := ⟨View.mk⟩
--instance : has_coe (View α β) (α → β) := ⟨View.value⟩

instance {ι : Type*} : functor (G ι) :=
{ map := λ _ _ f g, { g with value := f g.value } }

instance {ι : Type*} : functor (View ι) :=
{ map := λ _ _ f v, { v with value := f ∘ v.value } }

def G.iv {ι ι' α α'} (i : ι → ι') (v : α → α') : G ι α → G ι' α'
:= λ g, { g with value := v g.value, index := i g.index }

def G.mul [has_hmul α β γ] (a : G E α) (b : G E β) : G E γ :=
{ index := BinOp.max a.index b.index,
  value := a.value ⋆ b.value,
  ready := a.ready && b.ready && a.index == b.index,
  next  := Prog.if (a.index < b.index ||
                        (a.index == b.index && a.ready.not))
                  a.next
                  b.next,
  valid := a.valid && b.valid,
  init  := a.init <;> b.init,
}

def G.mulViewR [has_hmul α β γ] (a : G ι α) (b : View ι β) : G ι γ :=
(⋆ b.value a.index) <$> a
def G.mulViewL [has_hmul α β γ] (a : View ι α) (b : G ι β) : G ι γ :=
(λ v, a.value b.index ⋆ v) <$> b

instance [has_hmul α β γ] : has_hmul (G E α) (G E β) (G E γ) := ⟨G.mul⟩
instance GV.has_hmul [has_hmul α β γ] : has_hmul (G ι α) (View ι β) (G ι γ) := ⟨G.mulViewR⟩
instance VG.has_hmul [has_hmul α β γ] : has_hmul (View ι α) (G ι β) (G ι γ) := ⟨G.mulViewL⟩

def range (counter bound : E) : G E E :=
{ index := counter,
  value := counter,
  ready := E.true,
  valid := counter < bound,
  init  := Prog.declare counter 0,
  next  := Prog.accum counter 1,
}

/- implementation of (nested) CSR iteration -/
section csr
def interval (i : E) (counter : E) (lower upper : E) : G E E :=
{ index := i.access counter,
  value := counter,
  ready := E.true,
  init  := counter.declare lower,
  valid := counter < upper,
  next  := counter.accum 1,
}

def View.to_gen (counter bound : E) : View E α → G E α := λ view,
view.value <$> range counter bound

structure csr := (i v var : E)

def csr.level : csr → E → G E E := λ csr loc, interval csr.i csr.var (csr.v.access loc) (csr.v.access (loc+1))
def G.level   : csr → G E E → G E (G E E) := functor.map ∘ csr.level
def G.leaf    :   E → G E E → G E E       := functor.map ∘ E.access -- λ v, functor.map $ λ i, E.access v i

def csr.of (name : string) (n : ℕ) : csr :=
let field (x : string) := E.ident $ name ++ n.repr ++ x in
{ i   := field "_crd",
  v   := field "_pos",
  var := field "_i" }

structure pre := (pre : Prog)

-- def push_i (var var' crd_one pos_two : E) : α → E → pre × α := λ k rval_i,
-- (⟨(crd_one.access var).store rval_i;
--  (pos_two.access var).store var';
--  var.accum 1⟩, k)

def push_i' (var var' crd_one pos_two : E) : α → Prog × (E → pre × α) :=
λ k, let push_pos : Prog := (pos_two.access var).store var' in
(push_pos, λ rval_i, ({pre := (crd_one.access var).store rval_i; push_pos; var.accum 1}, k))

def push_i_accum (var var' crd_one pos_two : E) : α → Prog × (E → pre × α) :=
λ k, let push_pos : Prog := (pos_two.access var).store var' in
(push_pos, λ rval_i, ({pre :=
  Prog.if1 (var == 0 || rval_i != crd_one.access (var-1)) $ (crd_one.access var).store rval_i; push_pos; var.accum 1}, k))

def push_i :  E → E → E → E → α → Prog × (E → pre × α) := push_i_accum

def push_v (var crd_n val_array: E) : E → E → Prog := λ rval_i rval_v,
(crd_n.access var).store rval_i;
(val_array.access var).accum rval_v;
Prog.accum var 1


/- current -/
structure lval := (new : E → Prog) -- (acc : E → α)

-- def push_i0 : csr → (lval × α) → lval × (E → pre × Prog × α) := λ csr k,
-- ( { new := λ i, (csr.v.access i).store (csr.var+1) },
--   λ i, ({pre := csr.var.accum 1; (csr.i.access csr.var).store i; k.1.new csr.var /-; csr.var.accum 1-/}, (k.1.new csr.var, k.2)) )

-- def push_i0_acc : csr → (lval × α) → lval × (E → pre × Prog × α) := λ csr k,
-- ( { new := λ i, (csr.v.access i).store (csr.var+1) },
--   λ i, ({pre := Prog.if1 (csr.var < 0 || i != csr.i.access csr.var) $
--                   csr.var.accum 1; (csr.i.access csr.var).store i; k.1.new csr.var /-; csr.var.accum 1-/}, (k.1.new csr.var, k.2)) )

structure post := (post : Prog)
def push_v0_post (var val_array: E) : lval × (E → Prog) :=
({ new := λ i, (val_array.access i).store 0 }, λ rval_v, (val_array.access var).accum rval_v)
def push_i0_acc_post : csr → (lval × α) → lval × (E → post × α) := λ csr k,
({ new := λ i, (csr.v.access (i)).store (csr.var) },
   λ i, (⟨Prog.if1 (csr.var < 0 || i != csr.i.access csr.var) $
                    (csr.i.access csr.var).store i; csr.var.accum 1; k.1.new (csr.var)⟩,
         k.2))


def push_v0 (var val_array: E) : lval × (E → Prog) :=
({ new := λ i, (val_array.access i).store 0 }, λ rval_v, (val_array.access var).accum rval_v)
def push_i0_acc : csr → (lval × α) → lval × (E → pre × α) := λ csr k,
({ new := λ i, (csr.v.access (i)).store (csr.var+1); k.1.new (csr.var+1) },
   λ i, ({ pre := Prog.if1 (csr.var < 0 || i != csr.i.access csr.var) $
                    csr.var.accum 1; (csr.i.access csr.var).store i; k.1.new csr.var },
         k.2))

def mat_lval' (n : string) :=
push_i0_acc (csr.of n 1) $ push_i0_acc (csr.of n 2) $ push_v0 (csr.of n 2).var (E.ident $ n ++ "_vals")
def vec_lval' (n : string) :=
push_i0_acc_post (csr.of n 2) $ push_v0_post (csr.of n 2).var (E.ident $ n ++ "_vals")


def vec_lval := push_v "iout" "out_crd2" "out_vals"
def out_mat_lval :=
push_i "iout" "jout" "out1_crd" "out2_pos" $ push_v "jout" "out2_crd" "out_vals"
def out_cub_lval :=
push_i' "_out" "iout" "out0_crd" "out1_pos" $ push_i' "iout" "jout" "out1_crd" "out2_pos" $ push_v "jout" "out2_crd" "out_vals"
def mat_lval (n : string) :=
  push_i (E.ident $ "i" ++ n) (E.ident $ "j"++n) (E.ident $ n++"1_crd") (E.ident $ n ++ "2_pos") $
  push_v  (E.ident $ "j" ++ n) (E.ident $ n ++ "2_crd") (E.ident $ n ++ "_vals")
def cub_lval (n : string) :=
  push_i (E.ident $ "_" ++ n) (E.ident $ "i"++n) (E.ident $ n++"0_crd") (E.ident $ n ++ "1_pos") $
  push_i (E.ident $ "i" ++ n) (E.ident $ "j"++n) (E.ident $ n++"1_crd") (E.ident $ n ++ "2_pos") $
  push_v  (E.ident $ "j" ++ n) (E.ident $ n ++ "2_crd") (E.ident $ n ++ "_vals")

end csr

def csr_t := csr.of "A"

-- def v1 := G.leaf "v" $ interval "i1" "x" 0 10
-- def v1' : G E E := G.leaf "v" $ ((csr_t 1).level "i1")
-- def v2  : G E (G E E) := G.leaf "v" <$> ((csr_t 1).level 0).level (csr_t 2)
def v  : G E E       := G.leaf "v_vals"  $  ((csr.of "v" 1).level 0)
def A  : G E (G E E) := G.leaf "A_vals" <$> ((csr.of "A" 1).level 0).level (csr.of "A" 2)
def B  : G E (G E E) := G.leaf "B_vals" <$> ((csr.of "B" 1).level 0).level (csr.of "B" 2)

def indexed_mat_lval (var : E) (i j v : E) := ((var.access i).access j).accum v

def gmap1 {α β} : (α → β) → G E α → G E β := functor.map
def gmap2 {α β} : (α → β) → G E (G E α) → G E (G E β) := functor.map ∘ functor.map

class Ev (l r: Type) := (eval : l → r → Prog)
instance base.eval : Ev ((E → Prog)) E :=
{ eval := λ acc v, acc v }
instance base.eval' : Ev (Prog × (E → Prog)) E :=
{ eval := λ acc v, acc.2 v }
instance unit.eval [Ev α β] : Ev α (G unit β) :=
{ eval := λ acc v,
  v.init ; Prog.while v.valid
    (Prog.if1 v.ready (Ev.eval acc v.value) ; v.next) }
instance level.eval  [Ev α β] : Ev (E → α) (G E β) :=
{ eval := λ acc v, v.init;
    Prog.while v.valid
      (Prog.if1 v.ready (Ev.eval (acc v.index) v.value);
      v.next) }
instance level_p.eval [Ev α β] : Ev (E → pre × α) (G E β) :=
{ eval := λ acc v, v.init ;
    Prog.while v.valid
      (Prog.if1 v.ready ((acc v.index).1.pre ; Ev.eval (acc v.index).2 v.value) ;
      v.next) }

instance level_post.eval [Ev α β] : Ev (E → post × α) (G E β) :=
{ eval := λ acc v, v.init ;
    Prog.while v.valid
      (Prog.if1 v.ready (Ev.eval (acc v.index).2 v.value; (acc v.index).1.post) ;
      v.next) }

-- todo remove:
instance level_pp.eval [Ev α β] : Ev (Prog × (E → pre × α)) (G E β) :=
{ eval := λ lhs v, let (post, acc) := lhs in
    v.init ; Prog.while v.valid
      (Prog.if1 v.ready ((acc v.index).1.pre ; Ev.eval (acc v.index).2 v.value) ;
      v.next);
    post }

-- instance level_pp'.eval [Ev α β] : Ev (lval × (E → pre × α)) (G E β) :=
-- { eval := λ lhs v, let (x, acc) := lhs in
--     v.init ; Prog.while v.valid
--       (Prog.if1 v.ready ((acc v.index).1.pre ; Ev.eval (acc v.index).2 v.value) ;
--       v.next);
--     x.new 1 }

instance level_outer_lval.eval [Ev α β] : Ev (lval × α) β :=
{ eval := λ lhs v, let (x, acc) := lhs in
    Ev.eval acc v;
    x.new 1 }

def G.contract (g : G ι α) : G unit α := { g with index := () }

-- class Contractible (α β : Type) := (contract : α → β)
-- instance contract_base : Contractible (G E α) (G unit α) := ⟨G.contract⟩
-- instance contract [Contractible α β] : Contractible (G E α) (G E β) :=
-- ⟨functor.map Contractible.contract⟩
-- def G.sum [Contractible α β] : α → β := Contractible.contract

def G.sum2 : G E (G E E) → G unit (G unit E) := λ v, G.contract <$> v.contract
def G.sum3 : G E (G E (G E E)) → G unit (G unit (G unit E)) :=
(functor.map $ functor.map G.contract) ∘ (functor.map G.contract) ∘ (G.contract)
def G.sum_inner : G E (G E (G E E)) → G E (G E (G unit E)) := functor.map $ functor.map G.contract
def matrix_rval (var : E) : View E (View E E) := View.mk $ λ i, View.mk $ λ j , var.access (E.call2 "make_tuple" i j)

-- Janky!
-- i   = get<0>(x.first)
-- j   = get<1>(x.first)
-- val = x.second
def coo_matrix_rval (matrix var : E) : G E (G E E) :=
let
call (a b : E) := E.call0 (a.attr b) in
{ index := E.call1 "get<0>" $ var.pattr "first",
  value :=
  { index := E.call1 "get<1>" $ var.pattr "first",
    value := var.pattr "second",
    ready := E.true,
    valid := E.true,
    init  := Prog.skip,
    next  := Prog.inline_code "break;" },
  ready := E.true,
  valid := E.not $ var == call matrix "end",
  init  := Prog.auto var $ call matrix "begin",
  next  := Prog.expr $ var.incr,
  --next  := Prog.expr $ call var "next",
}


def single (x : α) := (⇑ E x).to_gen "i" 1
def eg01 := Ev.eval (Prog.accum "out") (G.contract <$> A.contract)
def eg02 := Ev.eval (Prog.accum "out") (G.sum2 $ A⋆B)
def eg03 := Ev.eval (Prog.accum "out") (G.sum2 $ (⇑ E v) ⋆ A)
def eg04 := Ev.eval (Prog.accum "out") (G.sum3 $ ((⇑ E) <$> A) ⋆ ⇑ E B ) -- (i,k)*(j,k)
def inner_prod := ((⇑ E) <$> A) ⋆ ⇑ E B
def eg05 := Ev.eval (Prog.accum "out") $ G.sum3 $ (gmap2 (⇑ E) A) ⋆ (gmap1 (⇑ E) B) -- (i,j)*(i,k)
def comb_rows := (gmap2 (⇑ E) A) ⋆ ⇑ E B -- (i,j)*(j,k)
def matsum := (G.sum3 $ (gmap2 (⇑ E) A) ⋆ ⇑ E B ) -- (i,j)*(j,k)
def eg06 := Ev.eval (Prog.accum "out") matsum
def eg07 := Ev.eval (indexed_mat_lval "out") (A⋆B)
def eg08 := Ev.eval vec_lval v
def eg09 := Ev.eval out_mat_lval A
def eg10 := Ev.eval out_mat_lval (A⋆B)
def rng1 := (λ _, (λ _, (1 : E)) <$> range "j" 10) <$> range "i" 20
def eg11 := Ev.eval out_mat_lval $ rng1 ⋆ matrix_rval "x.data"
def eg12 := Ev.eval out_mat_lval $ coo_matrix_rval "x.data" "entry"
def eg13 := λ a, Ev.eval (mat_lval a) $ coo_matrix_rval "x.data" (E.ident $ "entry" ++ a)
def eg14 := Ev.eval out_cub_lval $ (⇑ E A).to_gen "i" 1
def eg15 := [eg13 "A", eg13 "B", eg10]
def ref_matrix := (coo_matrix_rval "x.data" "entry")
def eg16 := λ a, Ev.eval (cub_lval a) $ single (coo_matrix_rval "x.data" (E.ident $ "entry" ++ a))
def eg17 := [eg16 "A", eg16 "B", Prog.time $ Ev.eval out_cub_lval $ single inner_prod.sum_inner]
def eg18 := Ev.eval (mat_lval' "out") A
def eg19 := [Ev.eval (mat_lval' "A") ref_matrix, Ev.eval (mat_lval' "B") ref_matrix, Prog.time $ Ev.eval (mat_lval' "out") $ A⋆B]
def eg20 := [Ev.eval (mat_lval' "A") ref_matrix, Ev.eval (mat_lval' "B") ref_matrix, Prog.time $ eg06]
def eg21 := Ev.eval (vec_lval' "out") v

--#eval comp eg06

#eval comp eg21


-- -- todo errors, don't crash on empty file
-- def readFile (name : string) : G unit E :=
-- let getline := Prog.inline_code $ "getline" ++ wrap ("file" ++ ",line") ++ ";" in
-- { index := (),
--   value := "line", -- line
--   ready := E.true,
--   valid := E.not $ E.inline_code $ "file_empty(file)", -- eof check
--   init  := Prog.inline_code ("ifstream file("++name++"); string line;") ; getline,
--   next  := getline,
-- }
-- --#eval comp $ Ev.eval (λ (line : E), Prog.inline_code $ "cout << " ++ line.to_c ++ "<< endl;") $ readFile "\"test.txt\""

end G

-- [x] multiply
-- [x] repeat
-- [x] MM (sum)
-- [x] read file
-- [x] CSR lval
-- [x] initialize variables
-- [x] read std::map into CSR lval
-- do pre+post.
-- [x] accumulate same indices in new lval

-- generate wrapper code
-- run MM (sum)
-- run TACO
-- dense level, test ds * ds
-- dense lval
-- label indices, then do indexed contraction
-- shorthand notation
-- database comparison? binary_search
