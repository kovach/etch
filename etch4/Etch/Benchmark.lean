import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul
import Etch.Compile
import Etch.ShapeInference

/-
Tags:
 For type T to be usable as an index type, it needs to be Tagged and TaggedC.
 For type T to be usable as a value type, it needs to be Tagged and a semiring.
-/

def E.toMin (e : E R) : E RMin := E.call Op.toMin ![e]
def E.toMax (e : E R) : E RMax := E.call Op.toMax ![e]
def E.ofNat (e : E ℕ) : E R    := E.call Op.toNum ![e]

instance : TaggedC R := ⟨⟨"double"⟩⟩
instance : Mul R := ⟨fun _ _ => default⟩
instance : DecidableEq R := fun .mk .mk => .isTrue (by simp)
instance : Max R := ⟨fun _ _ => default⟩

section TACO

variable {ι : Type} [Tagged ι] [DecidableEq ι]
[LT ι] [DecidableRel (LT.lt : ι → ι → _)]
[LE ι] [DecidableRel (LE.le : ι → ι → _)]
(is : ArrayVar ι)

-- todo: replace default interval
def TACO.interval (pos : Var ℕ) (lower upper : E ℕ) : ι →ₛ (E ℕ) where
  σ := Var ℕ
  succ pos i := .store_var pos $ pos + .call Op.ofBool ![(E.access is pos.expr <= i)]
  skip pos i := .store_var pos $ pos + .call Op.ofBool ![(E.access is pos.expr << i)]
  value pos := pos.expr
  ready _   := 1
  index pos := .access is pos.expr
  valid pos := pos.expr << upper
  init  n   := let p := pos.fresh n; (p.decl lower, p)

def csr.level' : csr ι ℕ → E ℕ → ι →ₛ E ℕ := λ csr loc => TACO.interval csr.i csr.var (.access csr.v loc) (csr.v.access (loc+1)) -- 1
def TACO.level {f} [Functor f] : csr ι ℕ → f (E ℕ) → f (ι →ₛ (E ℕ)) := Functor.map ∘ csr.level'

end TACO

def List.sequence [Monad m] : List (m α) → m (List α) := List.mapM id

def IOp.compile' (f : String) (body : List String) : IO Unit := IO.FS.writeFile f $ String.join body
def compile_fun (name : String) (body : List String) : String :=
s!"double {name}()\{ double val = 0;\n {String.join body} return val; }"

def FSQLCallback : (E ℕ × E ℕ × E R) :=
(.call Op.atoi ![.access "argv" 0],
 .call Op.atoi ![.access "argv" 1],
 1)

def VSQLCallback : (E ℕ × E R) :=
(.call Op.atoi ![.access "argv" 0],
 .call Op.atof ![.access "argv" 1])

def SQLCallback : (E ℕ × E ℕ × E R) :=
(.call Op.atoi ![.access "argv" 0],
 .call Op.atoi ![.access "argv" 1],
 .call Op.atof ![.access "argv" 2])

def SQLCallback3 : (E ℕ × E ℕ × E ℕ × E R) :=
(.call Op.atoi ![.access "argv" 0],
 .call Op.atoi ![.access "argv" 1],
 .call Op.atoi ![.access "argv" 2],
 .call Op.atof ![.access "argv" 3])

def l_dV  : lvl ℕ (MemLoc R)         := dense_vec "dV" "dim" "i1_"
def l_sV  : lvl ℕ (MemLoc R)         := sparse_vec "sV"
def l_ssA : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssA"
def l_dsA : lvl ℕ (lvl ℕ (MemLoc R)) := csr_mat "dsA" "dim" "i1_"
def l_ssB : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssB"
def l_dsB : lvl ℕ (lvl ℕ (MemLoc R)) := csr_mat "dsB" "dim" "i1_" -- todo "i2"
def l_ssF : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssF"
def l_sssC : lvl ℕ (lvl ℕ (lvl ℕ (MemLoc R))) := tcsr "ssC"

def l_dsR : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "dsR" -- "dim" "i1_"
def l_dsS : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "dsS" -- "dim" "i1_"
def l_dsT : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "dsT" -- "dim" "i1_"

def outVar : Var R := "fout"
def outVal : Var R := "val"
def outVal_min : Var RMin := "val"
def outVal_max : Var RMax := "val"
def sum1 [TaggedC ι] : S ι α → Contraction α := S.contract
def sum2 [TaggedC ι] [TaggedC ι'] : S ι (S ι' α) → Contraction (Contraction α) := S.contract ⊚ sum1
def sum3 [TaggedC ι] [TaggedC ι'] [TaggedC ι''] : S ι (S ι' (S ι'' α)) → Contraction (Contraction (Contraction α)) := S.contract ⊚ sum2
def exp0 (ι : Type _) : α → ι →ₐ α := λ (v : α) => λ _ => v
def exp1 (ι'' : Type _) : (ι' →ₛ α) → (ι' →ₛ (ι'' →ₐ α)) := Functor.map $ exp0 ι''
def exp2 (ι'' : Type _) : S ι (S ι' α) → S ι (S ι' (Fun ι'' α)) := Functor.map $ exp1 ι''


--def S.snd [Tagged α] [Zero α] [Tagged β] [Zero β] : β →ₛ α →ₛ (E α) := S.function "f1_" ⊚ S.function "f2_" $ λ _ x => x
--def S.fst [Tagged α] [Zero α] [Tagged β] [Zero β] : α →ₛ β →ₛ (E α) := S.function "f1_" ⊚ S.function "f2_" $ λ x _ => x
--def S.attr [Tagged α] [Zero α] : α →ₛ (E α) := S.function "f1_" id
def S.attr (i : ℕ × Type _) : i ↠ₐ (E i.2) := StrF.fun id

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
example : HMul (ℕ →ₛ ℕ →ₐ E R) (ℕ →ₛ ℕ →ₛ E R) (ℕ →ₛ ℕ →ₛ E R) := inferInstance
--def mulAB := ((exp0 ℕ <$> .) <$> ssA) * (exp0 ℕ ssB)

--?def mulAB' := (exp2 ℕ ssA) * (exp0 ℕ ssB)

--def mulAB_csr := ((exp0 ℕ <$> .) <$> ssA) * (exp0 ℕ dsB)
--def mulAB_inner := (exp0 ℕ <$> ssA) * (exp0 ℕ ssB)
--def mulAB_ij := mulAB * (exp0 ℕ <$> S.lt)


def input_data :=
[ ("gen_query_dV.c", [go l_dV VSQLCallback]),
  ("gen_query_sV.c", [go l_sV VSQLCallback]),
  ("gen_query_dsA.c", [go l_dsA SQLCallback]),
  ("gen_query_dsB.c", [go l_dsB SQLCallback]),
  ("gen_query_ssA.c", [go l_ssA SQLCallback]),
  ("gen_query_ssB.c", [go l_ssB SQLCallback]),
  ("gen_query_sssC.c", [go l_sssC SQLCallback3]),
  ("gen_query_fires.c", [go l_ssF FSQLCallback]),
  ("gen_query_wcoj_R.c", [ go l_dsR FSQLCallback ]),
  ("gen_query_wcoj_S.c", [ go l_dsS FSQLCallback ]),
  ("gen_query_wcoj_T.c", [ go l_dsT FSQLCallback ])
  -- ("", [go ])
]

abbrev i := (0, ℕ)
abbrev j := (1, ℕ)
abbrev k := (2, ℕ)
abbrev l := (3, ℕ)

def ssA      : i ↠ₛ j ↠ₛ E R      := taco_mat "ssA"
def dsA      : i ↠ₐ j ↠ₛ E R      := taco_dsMat "dsA"
def ssB_ij   : i ↠ₛ j ↠ₛ E R     := taco_mat "ssB"
def ssB      : j ↠ₛ k ↠ₛ E R      := taco_mat "ssB"
def ssB_skip : j ↠ₛ k ↠ₛ E R := skip_mat "ssB"
def dsB      : j ↠ₐ k ↠ₛ E R      := taco_dsMat "dsB"
def sssC     : i ↠ₛ j ↠ₛ k ↠ₛ E R   := taco_mat3 "ssC"

def dsR : i ↠ₛ j ↠ₛ E R:= mat "dsR"
def dsS : j ↠ₛ k ↠ₛ E R:= mat "dsS"
def dsT : i ↠ₛ k ↠ₛ E R:= mat "dsT"


abbrev cause := (0, ℕ)
abbrev year  := (1, ℕ)
abbrev objid := (2, ℕ)

/- Benchmark Queries -/
def spmv      := ∑ i, j: (ssA' : i ↠ₛ j ↠ₛ E R) * (dV : j ↠ₐ E R)
def mul       := ∑ i, j, k: (ssA' : i ↠ₛ j ↠ₛ E R) * (dsB' : j ↠ₐ k ↠ₛ E R)
def mul_ss    := ∑ i, j, k: ssA * ssB_skip
def mttkrp    := ∑ i, j, k, l: sssC * (dsA' : j ↠ₐ l ↠ₛ E R) * (dsB' : k ↠ₐ l ↠ₛ E R)
def mul_inner := ∑ i, j, k: (ssA' : i ↠ₛ k ↠ₛ E R) * (ssB' : j ↠ₛ k ↠ₛ E R)
def udf       := ((λ _ : E R => 1) <$$> dsR) * (S.udf : i ↠ₛ j ↠ₛ E RMax)
def add_ss    := ∑ i, j: ((ssA' + ssB') : i ↠ₛ j ↠ₛ E R)
def inner     := ∑ i, j: ssA * ssB_ij

def threshold : E R := "threshold"
def filter_v    : i ↠ₛ E R := S.valFilter (λ e => threshold << (e : E R)) sV
def filter_spmv := ∑ i, j: filter_v * ssA

def fires : year ↠ₛ objid ↠ₛ E R := mat "ssF"
def range_06_08 : year ↠ₛ E R := (S.predRange (2006 : E ℕ) 2008 : ℕ →ₛ E R)
def count_range := ∑ year, objid: range_06_08 * fires

def E.succ {α} [Tagged α] [Add α] [OfNat α (nat_lit 1)] (e : E α) : E α :=
  E.call .add ![e, (1 : E α)]

namespace String

instance instLEString : LE String := ⟨fun s₁ s₂ ↦ s₁ < s₂ || s₁ = s₂⟩

instance decLe : @DecidableRel String (· ≤ ·)
  | s₁, s₂ => if h₁ : s₁ < s₂ then isTrue (by simp [instLEString, h₁])
              else if h₂ : s₁ = s₂ then isTrue (by simp [instLEString, h₂])
              else isFalse (by simp [instLEString, h₁, h₂])

instance zero : Zero String := ⟨""⟩

instance max : Max String := ⟨fun s₁ s₂ ↦ if s₁ < s₂ then s₂ else s₁⟩

end String

-- CSR, but assume pos[i] = i (inherit the position from the previous level)
def csr.inherit
  {ι : Type} [Tagged ι] [TaggedC ι] [LT ι] [@DecidableRel ι LT.lt] [LE ι] [@DecidableRel ι LE.le] [Zero ι]
  (vars : csr ι ℕ) (loc : E ℕ) : ι →ₛ (E ℕ) :=
  S.interval vars.i .step vars.var loc (loc+1)

def Op.index_str_map : Op (ℕ → R) where
  argTypes := ![String → R, String]
  spec := λ _ _ => .mk
  opName := "index_str_map"

namespace SQL

variable
{ι₁ : Type} [Tagged ι₁] [TaggedC ι₁] [LT ι₁] [@DecidableRel ι₁ LT.lt] [LE ι₁] [@DecidableRel ι₁ LE.le] [Zero ι₁]
{ι₂ : Type} [Tagged ι₂] [TaggedC ι₂] [LT ι₂] [@DecidableRel ι₂ LT.lt] [LE ι₂] [@DecidableRel ι₂ LE.le] [Zero ι₂]
{ι₃ : Type} [Tagged ι₃] [TaggedC ι₃] [LT ι₃] [@DecidableRel ι₃ LT.lt] [LE ι₃] [@DecidableRel ι₃ LE.le] [Zero ι₃]
{ι₄ : Type} [Tagged ι₄] [TaggedC ι₄] [LT ι₄] [@DecidableRel ι₄ LT.lt] [LE ι₄] [@DecidableRel ι₄ LE.le] [Zero ι₄]
{ι₅ : Type} [Tagged ι₅] [TaggedC ι₅] [LT ι₅] [@DecidableRel ι₅ LT.lt] [LE ι₅] [@DecidableRel ι₅ LE.le] [Zero ι₅]
{ι₆ : Type} [Tagged ι₆] [TaggedC ι₆] [LT ι₆] [@DecidableRel ι₆ LT.lt] [LE ι₆] [@DecidableRel ι₆ LE.le] [Zero ι₆]
{α  : Type} [Tagged α]  [One α]
(f : String)
(t₁ t₂ t₃ t₄ := IterMethod.step)

def s_   : ι₁ →ₛ ι₂ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).inherit <$> ·) ⊚
  Functor.mapConst 1
def d_   : ℕ →ₐ ι₂ →ₛ E α :=
  range |>
  ((csr.of f 2 ι₂).inherit <$> ·) ⊚
  Functor.mapConst 1
def ss   : ι₁ →ₛ ι₂ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  Functor.mapConst 1
def ds   : ℕ →ₐ ι₂ →ₛ E α :=
  range |>
  ((csr.of f 2 ι₂).level .step <$> ·) ⊚
  Functor.mapConst 1
def dss  : ℕ →ₐ ι₂ →ₛ ι₃ →ₛ E α :=
  range |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).level t₃ <$> ·) ⊚
  Functor.mapConst 1
def ds_  : ℕ →ₐ ι₂ →ₛ ι₃ →ₛ E α :=
  range |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).inherit <$> ·) ⊚
  Functor.mapConst 1
def ss__ : ι₁ →ₛ ι₂ →ₛ ι₃ →ₛ ι₄ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).inherit <$> ·) ⊚
  ((csr.of f 4 ι₄).inherit <$> ·) ⊚
  Functor.mapConst 1
def sss___ : ι₁ →ₛ ι₂ →ₛ ι₃ →ₛ ι₄ →ₛ ι₅ →ₛ ι₆ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).level t₃ <$> ·) ⊚
  ((csr.of f 4 ι₄).inherit <$> ·) ⊚
  ((csr.of f 5 ι₅).inherit <$> ·) ⊚
  ((csr.of f 6 ι₆).inherit <$> ·) ⊚
  Functor.mapConst 1

end SQL

namespace TPCHq5

abbrev orderkey   := (0, ℕ)
abbrev orderdate  := (1, ℕ)
abbrev custkey    := (2, ℕ)
abbrev suppkey    := (3, ℕ)
abbrev nationkey  := (4, ℕ)
abbrev regionkey  := (5, ℕ)
abbrev nationname := (6, String)
abbrev regionname := (7, String)
abbrev extendedprice := (8, R)
abbrev discount   := (9, R)

def lineitem : orderkey ↠ₛ suppkey ↠ₛ extendedprice ↠ₛ discount ↠ₛ E R :=
  (SQL.ss__ "tpch_lineitem" .search : ℕ →ₛ ℕ →ₛ R →ₛ R →ₛ E R)

def revenue_calc' : R →ₐ R →ₐ E R := fun p d => p * (1 - d)
def revenue_calc : extendedprice ↠ₐ discount ↠ₐ E R := revenue_calc'
def lineitem_revenue : orderkey ↠ₛ suppkey ↠ₛ extendedprice ↠ₛ discount ↠ₛ E R := lineitem * revenue_calc

def orders   : orderkey  ↠ₐ orderdate ↠ₛ custkey ↠ₛ E R :=
  (SQL.dss "tpch_orders"   .search : ℕ →ₐ ℕ →ₛ ℕ →ₛ E R)
def customer : custkey   ↠ₐ nationkey ↠ₛ E R :=
  (SQL.ds  "tpch_customer"         : ℕ →ₐ ℕ →ₛ E R)
def supplier : suppkey   ↠ₐ nationkey ↠ₛ E R :=
  (SQL.ds  "tpch_supplier"         : ℕ →ₐ ℕ →ₛ E R)
def nation   : nationkey ↠ₐ regionkey ↠ₛ nationname ↠ₛ E R :=
  (SQL.ds_ "tpch_nation"   .search : ℕ →ₐ ℕ →ₛ String →ₛ E R)
def region   : regionkey ↠ₐ regionname ↠ₛ E R :=
  (SQL.ds  "tpch_region"           : ℕ →ₐ String →ₛ E R)

def asia : regionname ↠ₛ E R := (S.predRangeIncl "ASIA" "ASIA" : String →ₛ E R)

def year1994unix := 757411200
def year1995unix := 788947200
def orders1994 : orderdate ↠ₛ E R := (S.predRange year1994unix year1995unix : ℕ →ₛ E R)

def q5 := ∑ orderkey, orderdate, custkey: ∑ suppkey, nationkey, regionkey: ∑ regionname, extendedprice, discount:
          lineitem_revenue * orders * orders1994 * customer * supplier * (nation * region * asia)

def compile_fun (name : String) (body : List String) : String :=
s!"std::unordered_map<const char*, double> {name}()\{\n
     std::unordered_map<const char*, double> out;\n
     double* out_loc;
     {String.join body}
     return out;\n
   }"

def outVal : lvl String (MemLoc R) where
  push (s : E String) : P × MemLoc R :=
    let out : Var (String → R) := "out";
    let out_loc : Var (ℕ → R) := "out_loc";
    (out_loc.store_var (.call Op.index_str_map ![out.expr, s]), ⟨out_loc, 0⟩)

end TPCHq5

namespace TPCHq9

abbrev partkey       := (0, ℕ)
abbrev partname      := (1, String)
abbrev suppkey       := (2, ℕ)
abbrev orderkey      := (3, ℕ)
abbrev nationkey     := (4, ℕ)
abbrev orderdate     := (5, ℤ)
abbrev orderyear     := (6, ℤ)
abbrev nationname    := (7, String)
abbrev supplycost    := (8, R)
abbrev extendedprice := (9, R)
abbrev discount      := (10, R)
abbrev quantity      := (11, R)

def lineitem : partkey ↠ₛ suppkey ↠ₛ orderkey ↠ₛ extendedprice ↠ₛ discount ↠ₛ quantity ↠ₛ E R :=
  (SQL.sss___ "tpch9_lineitem" .search : ℕ →ₛ ℕ →ₛ ℕ →ₛ R →ₛ R →ₛ R →ₛ E R)

def profit_calc' : R →ₐ R →ₐ R →ₐ R →ₐ E R := fun c p d q => p * (1 - d) - c * q
def profit_calc : supplycost ↠ₐ extendedprice ↠ₐ discount ↠ₐ quantity ↠ₐ E R := profit_calc'

def part     : partkey   ↠ₐ partname  ↠ₛ E R := (SQL.d_ "tpch9_part" : ℕ →ₐ String →ₛ E R)
def orders   : orderkey  ↠ₐ orderdate ↠ₛ E R := (SQL.d_ "tpch9_orders" : ℕ →ₐ ℤ →ₛ E R)
def supplier : suppkey   ↠ₐ nationkey ↠ₛ E R := (SQL.d_ "tpch9_supplier" : ℕ →ₐ ℕ →ₛ E R)
def partsupp : partkey   ↠ₐ suppkey ↠ₛ supplycost ↠ₛ E R := (SQL.ds_ "tpch9_partsupp" .search : ℕ →ₐ ℕ →ₛ R →ₛ E R)
def nation   : nationkey ↠ₐ nationname ↠ₛ E R := (SQL.d_ "tpch9_nation" : ℕ →ₐ String →ₛ E R)

-- compute ι₂ from ι₁
def derive_idx [Tagged ι₁] [TaggedC ι₁] [Zero ι₁] [Tagged ι₂] [LT ι₂] [@DecidableRel ι₂ LT.lt] [Tagged α] [One α]
               (f : E ι₁ → E ι₂) : ι₁ →ₛ ι₂ →ₛ E α where
  σ := Var ι₁
  skip pos := pos.store_var
  succ _ _ := .skip
  ready _  := 1
  valid _  := 1
  index pos := pos.expr
  value pos := {
    σ     := Var Bool
    skip  := fun v i => .if1 (f pos.expr << i) (v.store_var 1)
    succ  := fun v _ => v.store_var 1
    ready := fun v => E.call Op.neg ![v.expr]
    valid := fun v => E.call Op.neg ![v.expr]
    index := fun _ => f pos.expr
    value := fun _ => 1
    init  := fun n => let v := Var.fresh "visited" n; ⟨v.decl 0, v⟩
  }
  init n := let v := Var.fresh "date" n; ⟨v.decl 0, v⟩

def op_date_to_year : Op ℤ where
  argTypes := ![ℤ]
  spec := fun a => 1970 + (a 0) / (365 * 24 * 60 * 60) -- not exactly
  opName := "date_to_year"

def orderdate_to_year : orderdate ↠ₛ orderyear ↠ₛ E R := (derive_idx (fun d => E.call op_date_to_year ![d]) : ℤ →ₛ ℤ →ₛ E R)

def hasGreen : String →ₐ E Bool := fun v => E.call Op.findStr ![v, .strLit "green"] >= (0 : E ℤ)
def partGreen : partname ↠ₐ E Bool := hasGreen

def q9 := ∑ partkey, partname, suppkey: ∑ orderkey, nationkey, orderdate: ∑ supplycost, extendedprice, discount, quantity:
          lineitem * part * partGreen * partsupp * supplier * nation * profit_calc * (orders * orderdate_to_year)

def compile_fun (name : String) (body : List String) : String :=
s!"std::unordered_map<std::tuple<const char*, int>, double, hash_tuple::hash<std::tuple<const char*, int>>> {name}()\{\n
     std::unordered_map<std::tuple<const char*, int>, double, hash_tuple::hash<std::tuple<const char*, int>>> out;\n
     double* out_loc;
     {String.join body}
     return out;\n
   }"

def index_map2 {α β γ : Type} [Inhabited γ] : Op (ℕ → γ) where
  argTypes := ![α × β → γ, α, β]
  spec := fun a => fun | 0 => (a 0) (a 1, a 2)
                       | _ => default
  opName := "index_map"

def outVal : lvl ℤ (lvl String (MemLoc R)) where
  push (n : E ℤ) : P × lvl String (MemLoc R) :=
    let out : Var (String × ℤ → R) := "out"
    let out_loc : Var (ℕ → R) := "out_loc"
    (.skip, ⟨fun (s : E String) =>
      (out_loc.store_var (E.call index_map2 ![out.expr, s, n]),
       ⟨out_loc, 0⟩)⟩)

end TPCHq9
/- end examples -/

#check (mat "f" : i ↠ₛ j ↠ₛ E R)
#check (ssA * ssB) * (S.lt : i ↠ₛ k ↠ₛ E R)
#check (ssA * ssB) * (E.ofNat <$$> S.attr i)
#check (S.attr i) * (S.attr j)
#check fires

abbrev TacoKernel := String

structure TacoTest where
  name : String
  kernel : TacoKernel
  command : String -- go l r

def taco_ops : List (String × String × String) :=
[
-- let fn := "inner2ss";     (fn, fn, compile_fun fn [go outVal inner]),
-- let fn := "sum_add2";     (fn, fn, compile_fun fn [go outVal add_ss]),
-- let fn := "sum_mul2_csr"; (fn, fn, compile_fun fn [go outVal mul]),
-- let fn := "sum_mul2";     (fn, fn, compile_fun fn [go outVal mul_ss]),
-- let fn := "mttkrp";       (fn, fn, compile_fun fn [go outVal mttkrp ]),
-- let fn := "spmv";         (fn, fn, compile_fun fn [go outVal spmv]),
-- let fn := "filter_spmv";  (fn, fn, compile_fun fn [go outVal filter_spmv])
]
--("sum_mul2_inner_ss", compile_fun "sum_mul2_inner_ss" $ [go outVal mul_inner]),
--("sum_add2", compile_fun "sum_add2" $ [go outVal $ sum2 $ ssA, go outVal $ sum2 $ ssB]),

def sql_ops : List (String × String) :=
[
let fn := "q5"; (fn, TPCHq5.compile_fun fn [go TPCHq5.outVal TPCHq5.q5])
--  ("count_range", compile_fun "count_range" $ [go outVal count_range]),
--  ("triangle", compile_fun "triangle" $ [go outVal $ ∑ i, j, k : dsR * dsS * dsT ]),
--  ("udf", compile_fun "udf" $ [go outVal_max $ ∑ i, j: udf])
  --("triangle", compile_fun "triangle" $ [go outVal $ ∑ i, j, k : dsR * dsS * dsT  ])
]

def files : List (String × List (String × String)) :=
[
("tpch_q5", [let fn := "q5"; (fn, TPCHq5.compile_fun fn [go TPCHq5.outVal TPCHq5.q5])]),
("tpch_q9", [let fn := "q9"; (fn, TPCHq9.compile_fun fn [go TPCHq9.outVal TPCHq9.q9])])
]

def main : IO Unit := do
  let mut funs := ""
  let mut main := ""
  let mut reps := 5
  let mut main_taco := s!"printf(\"RUNNING {reps} iterations per test\\n\");"
  for (taco_name, etch_name, etch_body) in taco_ops do
    funs := funs.append (etch_body ++ "\n")
    main_taco := main_taco.append $ s!"printf(\"{taco_name}\\n\");time(&taco_{taco_name}_, \"taco\", {reps}); time({etch_name}, \"etch\", {reps});\nprintf(\"\\n\");"
  reps := 10
  for x in sql_ops do
    funs := funs.append (x.2 ++ "\n")
    main := main.append $ s!"printf(\"{x.1}\\n\"); time({x.1}, \"etch\", {reps});\nprintf(\"\\n\");"
    --main := main.append $ s!"printf(\"{x.1}\\n\");time(&sql_{x.1}_, \"sql \", {reps}); time({x.1}, \"etch\", {reps});\nprintf(\"\\n\");"
  IO.FS.writeFile "gen_funs.c" funs
  IO.FS.writeFile "gen_out.c" main
  IO.FS.writeFile "gen_out_taco.c" main_taco
  for (f, ops) in files do
    let mut file := ""
    for x in ops do
      file := file.append (x.2 ++ "\n")
    IO.FS.writeFile s!"gen_{f}.c" file

#eval main
