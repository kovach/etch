import Etch.Benchmark.Basic
import Etch.Benchmark.SQL
import Etch.LVal
import Etch.Mul
import Etch.ShapeInference
import Etch.Stream

def RMin := R deriving Inhabited, TaggedC, Add, Mul, Zero, One
def RMin.ofR : R → RMin := id

def RMax := R deriving Inhabited, TaggedC, Add, Mul, Zero, One
def RMax.ofR : R → RMax := id

instance : Tagged RMin := ⟨ "min" ⟩
instance : Tagged RMax := ⟨ "max" ⟩

def Op.toMin : Op RMin where
  argTypes := ![R]
  spec := λ a => RMin.ofR (a 0)
  opName := tag_mk_fun R "toMin"

def Op.toMax : Op RMax where
  argTypes := ![R]
  spec := λ a => RMax.ofR (a 0)
  opName := tag_mk_fun R "toMax"

def Op.udf : Op RMin := { argTypes := ![ℕ, ℕ], spec := default, opName := "udf" }
def Op.udf_max : Op RMax where argTypes := ![ℕ, ℕ]; spec := default; opName := "int_max"
def Op.toGuard [Tagged α] [OfNat β 1] : Op β where argTypes := ![α]; spec := λ _ => 1; opName := tag_mk_fun α "toGuard"

section funs
variable
{ι : Type} [Tagged ι] [TaggedC ι] [DecidableEq ι] [LE ι] [@DecidableRel ι LE.le] [LT ι] [@DecidableRel ι LT.lt] [OfNat ι 0] [OfNat ι 1] [Add ι]
{ι' : Type} [Tagged ι'] [TaggedC ι'] [DecidableEq ι'] [LE ι'] [@DecidableRel ι' LE.le] [LT ι'] [@DecidableRel ι' LT.lt] [OfNat ι' 0] [OfNat ι' 1] [Add ι']

def toGuard {α β} [OfNat β (nat_lit 1)] : α → β := λ _ => 1
def binOp (f : E ι → E ι' → E α) : ι →ₛ ι' →ₛ E α := S.function "f1_" ⊚ S.function "f2_" $ f
def S.lt  : ℕ →ₛ ℕ →ₛ E R := binOp (. <ᵣ .)
def S.udf : ℕ →ₛ ℕ →ₛ E RMax := binOp fun a b => E.call .udf_max ![a,b]
end funs

section

variable {ι : Type} [Tagged ι] [DecidableEq ι]
[LT ι] [@DecidableRel ι LT.lt]
[LE ι] [@DecidableRel ι LE.le]
(is : ArrayVar ι)

-- todo: replace default interval
private def TACO.interval (pos : Var ℕ) (lower upper : E ℕ) : ι →ₛ (E ℕ) where
  σ := Var ℕ
  succ pos i := .store_var pos $ pos + .call Op.ofBool ![(E.access is pos.expr <= i)]
  skip pos i := .store_var pos $ pos + .call Op.ofBool ![(E.access is pos.expr << i)]
  value pos := pos.expr
  ready _   := 1
  index pos := .access is pos.expr
  valid pos := pos.expr << upper
  init  n   := let p := pos.fresh n; (p.decl lower, p)

private def csr.level' : csr ι ℕ → E ℕ → ι →ₛ E ℕ := λ csr loc => TACO.interval csr.i csr.var (.access csr.v loc) (csr.v.access (loc+1)) -- 1
private def TACO.level {f} [Functor f] : csr ι ℕ → f (E ℕ) → f (ι →ₛ (E ℕ)) := Functor.map ∘ csr.level'

end

namespace Etch.Benchmark.TACO

namespace Loading

def sqlCallback : (E ℕ × E R) :=
(.call Op.atoi ![.access "argv" 0],
 .call Op.atof ![.access "argv" 1])

def sqlCallback2 : (E ℕ × E ℕ × E R) :=
(.call Op.atoi ![.access "argv" 0],
 .call Op.atoi ![.access "argv" 1],
 .call Op.atof ![.access "argv" 2])

def sqlCallback3 : (E ℕ × E ℕ × E ℕ × E R) :=
(.call Op.atoi ![.access "argv" 0],
 .call Op.atoi ![.access "argv" 1],
 .call Op.atoi ![.access "argv" 2],
 .call Op.atof ![.access "argv" 3])

def l_dV  : lvl ℕ (MemLoc R)         := dense_vec "dV" "dim" "dV_i1_"
def l_sV  : lvl ℕ (MemLoc R)         := sparse_vec "sV"
def l_ssA : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssA"
def l_dsA : lvl ℕ (lvl ℕ (MemLoc R)) := csr_mat "dsA" "dim" "dsA_i1_"
def l_ssB : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssB"
def l_dsB : lvl ℕ (lvl ℕ (MemLoc R)) := csr_mat "dsB" "dim" "dsB_i1_" -- todo "i2"
def l_sssC : lvl ℕ (lvl ℕ (lvl ℕ (MemLoc R))) := tcsr "ssC"

def funcs : List (String × String) := [
  let name := "gen_taco_dV_callback";   (name, compileSqliteCb name [go l_dV sqlCallback]),
  let name := "gen_taco_sV_callback";   (name, compileSqliteCb name [go l_sV sqlCallback]),
  let name := "gen_taco_dsA_callback";  (name, compileSqliteCb name [go l_dsA sqlCallback2]),
  let name := "gen_taco_dsB_callback";  (name, compileSqliteCb name [go l_dsB sqlCallback2]),
  let name := "gen_taco_ssA_callback";  (name, compileSqliteCb name [go l_ssA sqlCallback2]),
  let name := "gen_taco_ssB_callback";  (name, compileSqliteCb name [go l_ssB sqlCallback2]),
  let name := "gen_taco_sssC_callback"; (name, compileSqliteCb name [go l_sssC sqlCallback3]) ]

end Loading

section funs
variable
{ι : Type} [Tagged ι] [TaggedC ι] [DecidableEq ι] [LE ι] [DecidableRel (LE.le : ι → ι → _)] [LT ι] [DecidableRel (LT.lt : ι → ι → _)] [OfNat ι 0] [OfNat ι 1] [Add ι]
{ι' : Type} [Tagged ι'] [TaggedC ι'] [DecidableEq ι'] [LE ι'] [DecidableRel (LE.le : ι' → ι' → _)] [LT ι'] [DecidableRel (LT.lt : ι' → ι' → _)] [OfNat ι' 0] [OfNat ι' 1] [Add ι']

def toGuard {α β} [OfNat β (nat_lit 1)] : α → β := λ _ => 1
def binOp (f : E ι → E ι' → E α) : ι →ₛ ι' →ₛ E α := S.function "f1_" ⊚ S.function "f2_" $ f
#check (1 : R)
def S.lt  : ℕ →ₛ ℕ →ₛ E R := binOp (. <ᵣ .)
def S.udf : ℕ →ₛ ℕ →ₛ E RMax := binOp λ a b => E.call .udf_max ![a,b]
end funs

def sVec   (f : String) : ℕ →ₛ E R := (csr.of f 1).level .step 0 & S.leaf (f ++ "_vals")
def dVec   (f : String) : ℕ →ₐ E R := range & S.leaf (f ++ "_vals")
def mat    (f : String) : ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level .step 0 & S.level .step (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def taco_mat (f : String) : ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level' 0 & TACO.level (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
--def taco_mat (f : String) : ℕ →ₜ ℕ →ₜ E R := (csr.of f 1).level' 0 & TACO.level (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def skip_mat   (f : String) : ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level .search 0 & S.level .step (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def mat3  (f : String) : ℕ →ₛ ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level .step 0 & S.level .step (csr.of f 2) ⊚ S.level .step (csr.of f 3) ⊚ S.leaf (f ++ "_vals")
def taco_mat3  (f : String) : ℕ →ₛ ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level' 0 & TACO.level (csr.of f 2) ⊚ TACO.level (csr.of f 3) ⊚ S.leaf (f ++ "_vals")
def dsMat (f : String) : ℕ →ₐ ℕ →ₛ E R := range & S.level .step (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def taco_dsMat (f : String) : ℕ →ₐ ℕ →ₛ E R := range & TACO.level (csr.of f 2) ⊚ S.leaf (f ++ "_vals")

def ssA' := taco_mat "ssA"
def dsA' := taco_dsMat "dsA"
def ssB' := taco_mat "ssB"
def dsB' := taco_dsMat "dsB"

def dV   := dVec "V"
def sV   := sVec "sV"

abbrev i := (0, ℕ)
abbrev j := (1, ℕ)
abbrev k := (2, ℕ)
abbrev l := (3, ℕ)

def ssA      : i ↠ₛ j ↠ₛ E R      := taco_mat "ssA"
def dsA      : i ↠ₐ j ↠ₛ E R      := taco_dsMat "dsA"
def ssB_ij   : i ↠ₛ j ↠ₛ E R      := taco_mat "ssB"
def ssB      : j ↠ₛ k ↠ₛ E R      := taco_mat "ssB"
def ssB_skip : j ↠ₛ k ↠ₛ E R      := skip_mat "ssB"
def dsB      : j ↠ₐ k ↠ₛ E R      := taco_dsMat "dsB"
def sssC     : i ↠ₛ j ↠ₛ k ↠ₛ E R := taco_mat3 "ssC"

def dsR : i ↠ₛ j ↠ₛ E R:= mat "dsR"
def dsS : j ↠ₛ k ↠ₛ E R:= mat "dsS"
def dsT : i ↠ₛ k ↠ₛ E R:= mat "dsT"

/- Benchmark Queries -/
def spmv      := ∑ i, j:    (ssA' : i ↠ₛ j ↠ₛ E R) * (dV : j ↠ₐ E R)
def mul       := ∑ i, j, k: (ssA' : i ↠ₛ j ↠ₛ E R) * (dsB' : j ↠ₐ k ↠ₛ E R)
def mul_ss    := ∑ i, j, k: ssA * ssB_skip
def mttkrp    := ∑ i, j, k, l: sssC * (dsA' : j ↠ₐ l ↠ₛ E R) * (dsB' : k ↠ₐ l ↠ₛ E R)
def mulInner  := ∑ i, j, k: (ssA' : i ↠ₛ k ↠ₛ E R) * (ssB' : j ↠ₛ k ↠ₛ E R)
def mulRowcb  := ∑ i, j, k: (ssA' : i ↠ₛ j ↠ₛ E R) * (ssB' : j ↠ₛ k ↠ₛ E R)
def udf       := ∑ i, j: ((λ _ : E R => 1) <$$> dsR) * (S.udf : i ↠ₛ j ↠ₛ E RMax)
def add_ss    := ∑ i, j: ((ssA' + ssB') : i ↠ₛ j ↠ₛ E R)
def inner     := ∑ i, j: ssA * ssB_ij

def threshold : Var R := "threshold"
def filterV    : j ↠ₛ E R := S.valFilter (fun e => threshold.expr << (e : E R)) sV
def filterSpMV := ∑ i, j: filterV * ssA

def funcs : List (String × String) :=
  Loading.funcs ++
  [ let fn := "etch_inner2ss";     ⟨fn, compileFun R fn inner⟩,
    let fn := "etch_sum_add2";     ⟨fn, compileFun R fn add_ss⟩,
    let fn := "etch_sum_mul2_csr"; ⟨fn, compileFun R fn mul⟩,
    let fn := "etch_sum_mul2";     ⟨fn, compileFun R fn mul_ss⟩,
    let fn := "etch_mttkrp";       ⟨fn, compileFun R fn mttkrp⟩,
    let fn := "etch_spmv";         ⟨fn, compileFun R fn spmv⟩,
    let fn := "etch_udf";          ⟨fn, compileFun RMax "udf" udf⟩]

def funcsMatmul : List (String × String) :=
  [ let fn := "gen_ssA_callback"; ⟨fn, compileSqliteCb fn [go Loading.l_ssA Loading.sqlCallback2]⟩,
    let fn := "gen_ssB_callback"; ⟨fn, compileSqliteCb fn [go Loading.l_ssB Loading.sqlCallback2]⟩,
    let fn := "mul_inner";        ⟨fn, compileFun R fn mulInner⟩,
    let fn := "mul_rowcb";        ⟨fn, compileFun R fn mulRowcb⟩ ]

def funcsFilterSpMV : List (String × String) :=
  [ let fn := "gen_ssA_callback"; ⟨fn, compileSqliteCb fn [go Loading.l_ssA Loading.sqlCallback2]⟩,
    let fn := "gen_sV_callback";  ⟨fn, compileSqliteCb fn [go Loading.l_sV  Loading.sqlCallback]⟩,
    let fn := "filter_spmv";      ⟨fn, compileFun R fn filterSpMV [.mk threshold]⟩ ]

end Etch.Benchmark.TACO
