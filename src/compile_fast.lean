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

/-- Statements for a simple imperative language, including sequencing. -/
inductive Prog
| skip
| accum (dst : E) (val : E)
| store (dst : E) (val : E)
| «if» (b : E) (cons : Prog) (alt : Prog)
| seq (a b : Prog)

| while (cond : E) (body : Prog)
| for (var bound : E) (body : Prog)

| inline_code (code : string)
| comment (c : string)

@[pattern]
def Prog.if1 (b : E) (cons : Prog) : Prog := Prog.if b cons Prog.skip

def E.store : E → E → Prog := Prog.store
def E.accum : E → E → Prog := Prog.accum

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
| (E.not i)                  := "!" ++ wrap i.to_c
| (E.bin_op BinOp.min e1 e2) := BinOp.min.to_c ++ (wrap $ e1.to_c ++ "," ++ e2.to_c)
| (E.bin_op BinOp.max e1 e2) := BinOp.max.to_c ++ (wrap $ e1.to_c ++ "," ++ e2.to_c)
| (E.bin_op op e1 e2)        := wrap $ e1.to_c ++ op.to_c ++ e2.to_c
| (E.ternary c t e)          := wrap $ wrap c.to_c ++ "?" ++ t.to_c ++ ":" ++ e.to_c
| (E.access e i)             := e.to_c ++ "[" ++ i.to_c ++ "]"
| (E.inline_code s)          := s

def emit (str : string) : M unit := modify $ λ s : MState,
{ s with buffer := s.buffer.append_string str }
def emitLine (s : string) : M unit := do emit $ s ++ ";"

namespace Prog

def to_c : Prog → M unit
| (accum dst val) := emitLine $ dst.to_c ++ " += " ++ val.to_c
| (store dst val) := emitLine $ dst.to_c ++ " = " ++ val.to_c
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
end Prog

def M.runInfo {α} (m : M α) : SymbolTable × buffer char :=
(λ s : MState, (s.symbolTable, s.buffer)) ((m.run ∅).run emptyContext).snd

def M.runBuffer {α} (m : M α) : string := m.runInfo.snd.to_string

def addHeaderFooter : string → string :=
λ s, "#include \"prefix.cpp\"\n" ++ s ++ "#include \"suffix.cpp\"\n"

def compile (prog : M Prog) : io unit :=
  let outName := "out_lean.cpp" in do
  handle ← io.mk_file_handle outName io.mode.write,
  let result : string := addHeaderFooter $ (prog >>= Prog.to_c).runBuffer,
  io.fs.write handle result.to_char_buffer,
  io.fs.close handle,
  if disableClangFormat then return () else io.cmd {cmd := "clang-format", args := ["-i", outName]} >> return ()

def comp : Prog → io unit := compile ∘ pure

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

-- def range (bound counter : E) : G E E :=
-- { index := counter,
--   value := counter,
--   ready := E.true,
--   valid := counter < bound,
--   init  := Prog.store counter 0,
--   next  := Prog.accum counter 1,
-- }

/- implementation of (nested) CSR iteration -/
section csr
def interval (i : E) (counter : E) (lower upper : E) : G E E :=
{ index := i.access counter,
  value := counter,
  ready := E.true,
  init  := counter.store lower,
  valid := counter < upper,
  next  := counter.accum 1,
}

structure csr := (i v var : E)

def csr.level : csr → E → G E E := λ csr loc, interval csr.i csr.var (csr.v.access loc) (csr.v.access (loc+1))
def G.level   : csr → G E E → G E (G E E) := functor.map ∘ csr.level
def G.leaf    :   E → G E E → G E E       := functor.map ∘ E.access -- λ v, functor.map $ λ i, E.access v i

def csr.of (name : string) (n : ℕ) : csr :=
let field (x : string) := E.ident $ name ++ x ++ n.repr in
{ i   := field "_crd",
  v   := field "_pos",
  var := field "_i" }

-- TODO check if new I
def push_i (var var' crd_one pos_two : E) : (E → E → Prog) → E → Prog × (E → E → Prog) := λ k rval_i,
((crd_one.access var).store rval_i;
 (pos_two.access var).store var';
 var.accum 1 , k)

-- TODO check if new I
def push_v (var crd_n val_array: E) : E → E → Prog := λ rval_i rval_v,
(crd_n.access var).store rval_i;
(val_array.access var).accum rval_v;
Prog.accum var 1

def vec_lval1 := push_v "iout" "out_crd2" "out_vals"
def mat_lval1 := push_i "iout" "jout" "out1_crd" "out2_pos" $
         push_v "jout" "out2_crd" "out_vals"

end csr

def csr_t := csr.of "A"

def v1 := G.leaf "v" $ interval "i1" "x" 0 10
def v1' : G E E := G.leaf "v" $ ((csr_t 1).level "i1")
def v2  : G E (G E E) := G.leaf "v" <$> ((csr_t 1).level 0).level (csr_t 2)
def v  : G E E       := G.leaf "v_vals"  $  ((csr.of "v" 1).level 0)
def A  : G E (G E E) := G.leaf "A_vals" <$> ((csr.of "A" 1).level 0).level (csr.of "A" 2)
def B  : G E (G E E) := G.leaf "B_vals" <$> ((csr.of "B" 1).level 0).level (csr.of "B" 2)

def gmap1 {α β} : (α → β) → G E α → G E β := functor.map
def gmap2 {α β} : (α → β) → G E (G E α) → G E (G E β) := functor.map ∘ functor.map

structure lv (γ : Type) :=
  (put : E → γ)

class Ev (l r: Type) := (eval : l → r → Prog)
instance base.eval : Ev (E → Prog) E :=
{ eval := λ acc v, acc v }
instance level.eval [Ev α β] : Ev (E → α) (G E β) :=
{ eval := λ acc v,
  v.init ; Prog.while v.valid
    (Prog.if1 v.ready (Ev.eval (acc v.index) v.value) ; v.next) }
instance level'.eval [Ev α β] : Ev (E → Prog × α) (G E β) :=
{ eval := λ acc v, v.init ;
    Prog.while v.valid
      (Prog.if1 v.ready ((acc v.index).1 ; Ev.eval (acc v.index).2 v.value) ;
      v.next) }
instance unit.eval [Ev α β] : Ev α (G unit β) :=
{ eval := λ acc v,
  v.init ; Prog.while v.valid
    (Prog.if1 v.ready (Ev.eval acc v.value) ; v.next) }
def G.contract (g : G ι α) : G unit α := { g with index := () }

-- class Contractible (α β : Type) := (contract : α → β)
-- instance contract_base : Contractible (G E α) (G unit α) := ⟨G.contract⟩
-- instance contract [Contractible α β] : Contractible (G E α) (G E β) :=
-- ⟨functor.map Contractible.contract⟩
-- def G.sum [Contractible α β] : α → β := Contractible.contract

--#eval comp $ Ev.eval (λ i v, Prog.accum ((E.ident "out").access i) v) v1'
--#eval comp $ Ev.eval (λ (_ _ v : E), Prog.accum "out" v) v2
--#eval comp $ Ev.eval (Prog.accum "out") (G.contract <$> v2.contract)
def G.sum2 : G E (G E E) → G unit (G unit E) := λ v, G.contract <$> v.contract
def G.sum3 : G E (G E (G E E)) → G unit (G unit (G unit E)) :=
(functor.map $ functor.map G.contract) ∘ (functor.map G.contract) ∘ (G.contract)
--#eval comp $ Ev.eval (Prog.accum "out") (G.contract <$> v2.contract)
--#eval comp $ Ev.eval (Prog.accum "out") (G.sum2 $ A⋆B)
--#eval comp $ Ev.eval (Prog.accum "out") (G.sum2 $ (⇑ E v) ⋆ A)
--#eval comp $ Ev.eval (Prog.accum "out") (G.sum3 $ ((⇑ E) <$> A) ⋆ ⇑ E B ) -- (i,k)*(j,k)
--#eval comp $ Ev.eval (Prog.accum "out") $ G.sum3 $ (gmap2 (⇑ E) A) ⋆ (gmap1 (⇑ E) B) -- (i,j)*(i,k)
--#eval comp $ Ev.eval (Prog.accum "out") (G.sum3 $ (gmap2 (⇑ E) A) ⋆ ⇑ E B ) -- (i,j)*(j,k)
--#eval comp $ Ev.eval vec_lval1 v
--#eval comp $ Ev.eval mat_lval1 A
#eval comp $ Ev.eval mat_lval1 (A⋆B)

def hmm (var : E) (i j v : E) := Prog.accum ((var.access i).access j) v

-- todo errors, don't crash on empty file
def readFile (name : string) : G unit E :=
let getline := Prog.inline_code $ "getline" ++ wrap ("file" ++ ",line") ++ ";" in
{ index := (),
  value := "line", -- line
  ready := E.true,
  valid := E.not $ E.inline_code $ "file_empty(file)", -- eof check
  init  := Prog.inline_code ("ifstream file("++name++"); string line;") ; getline,
  next  := getline,
}
--#eval comp $ Ev.eval (λ (line : E), Prog.inline_code $ "cout << " ++ line.to_c ++ "<< endl;") $ readFile "\"test.txt\""

end G

-- [x] multiply
-- [x] repeat
-- [x] MM (sum)
-- [x] read file
-- [x] CSR lval
-- [ ] initialize variables
-- [ ] read std::map into CSR lval
-- generate wrapper code
-- run MM (sum)
-- dense level, test ds * ds
-- dense lval
-- label indices, then do indexed contraction
-- shorthand notation
-- database comparison? binary_search
