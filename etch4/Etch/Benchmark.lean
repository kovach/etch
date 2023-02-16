import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul
import Etch.Compile
import Etch.ShapeInference

/- TODO:

https://docs.google.com/document/d/1kQFwU0STbcasz0ZPLxK6S4F-RDIvZLUuAg6UF6ga_TI/edit#heading=h.y6ikm63g5ns

especially
https://github.com/TimoKersten/db-engine-paradigms/blob/master/src/benchmarks/tpch/queries/q5.cpp

Note: If we have column A(a, b), convert it to A : a → b → Bool
If b is the key and a is the value, then actually rewrite it as A : b → a

for each table we want, make callback (SQLite)
  0, 1, 2, ... are column names  

VSQLCallback is basically ℕ →ₛ E R
The last one is the value type

orders(o_custkey, o_orderkey, o_orderdate)
customer(c_custkey, c_nationkey)
lineitem(l_orderkey, l_suppkey, (l_extendedprice, l_discount))
supplier(s_suppkey, s_nationkey)
nation(n_nationkey, n_regionkey, n_name)
region(r_regionkey, r_name)

∑(suppkey) lineitem * supplier

// select
//  n_name,
//  sum(l_extendedprice * (1 - l_discount)) as revenue
// from
//   customer,
//   orders,
//   lineitem,
//   supplier,
//   nation,
//   region
// where
//   c_custkey = o_custkey
//   and l_orderkey = o_orderkey
//   and l_suppkey = s_suppkey
//   and c_nationkey = s_nationkey
//   and s_nationkey = n_nationkey
//   and n_regionkey = r_regionkey
//   and r_name = 'ASIA'
//   and o_orderdate >= date '1994-01-01'
//   and o_orderdate < date '1995-01-01'
// group by
//  n_name

select
 sum(l_extendedprice * (1 - l_discount)) as revenue
from
  customer,
  orders,
  lineitem,
  supplier,
  nation,
  region
where
  c_custkey = o_custkey
  and l_orderkey = o_orderkey
  and l_suppkey = s_suppkey
  and c_nationkey = s_nationkey
  and s_nationkey = n_nationkey
  and n_regionkey = r_regionkey
  and r_name = 'ASIA'

-/

def E.toMin (e : E R) : E RMin := E.call Op.toMin ![e]
def E.toMax (e : E R) : E RMax := E.call Op.toMax ![e]
def E.ofNat (e : E ℕ) : E R    := E.call Op.toNum ![e]

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
def sum1 : S ι α → Contraction α := S.contract
def sum2 : S ι (S ι' α) → Contraction (Contraction α) := S.contract ⊚ sum1
def sum3 : S ι (S ι' (S ι'' α)) → Contraction (Contraction (Contraction α)) := S.contract ⊚ sum2
def exp0 (ι : Type _) : α → ι →ₐ α := λ (v : α) => λ _ => v
def exp1 (ι'' : Type _) : (ι' →ₛ α) → (ι' →ₛ (ι'' →ₐ α)) := Functor.map $ exp0 ι''
def exp2 (ι'' : Type _) : S ι (S ι' α) → S ι (S ι' (Fun ι'' α)) := Functor.map $ exp1 ι''


--def S.snd [Tagged α] [Zero α] [Tagged β] [Zero β] : β →ₛ α →ₛ (E α) := S.function "f1_" ⊚ S.function "f2_" $ λ _ x => x
--def S.fst [Tagged α] [Zero α] [Tagged β] [Zero β] : α →ₛ β →ₛ (E α) := S.function "f1_" ⊚ S.function "f2_" $ λ x _ => x
--def S.attr [Tagged α] [Zero α] : α →ₛ (E α) := S.function "f1_" id
def S.attr (i : ℕ × Type _) : i ↠ (E i.2) := Str.fun id

section funs
variable
{ι : Type} [Tagged ι] [DecidableEq ι] [LE ι] [DecidableRel (LE.le : ι → ι → _)] [LT ι] [DecidableRel (LT.lt : ι → ι → _)] [OfNat ι 0] [OfNat ι 1] [Add ι]
{ι' : Type} [Tagged ι'] [DecidableEq ι'] [LE ι'] [DecidableRel (LE.le : ι' → ι' → _)] [LT ι'] [DecidableRel (LT.lt : ι' → ι' → _)] [OfNat ι' 0] [OfNat ι' 1] [Add ι']

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

def ssA      : i ↠ j ↠ E R      := taco_mat "ssA"
def dsA      : i ↠ j ↠ E R      := taco_dsMat "dsA"
def ssB_ij   : i ↠ j ↠ E R     := taco_mat "ssB"
def ssB      : j ↠ k ↠ E R      := taco_mat "ssB"
def ssB_skip : j ↠ k ↠ E R := skip_mat "ssB"
def dsB      : j ↠ k ↠ E R      := taco_dsMat "dsB"
def sssC     : i ↠ j ↠ k ↠ E R   := taco_mat3 "ssC"

def dsR : i ↠ j ↠ E R:= mat "dsR"
def dsS : j ↠ k ↠ E R:= mat "dsS"
def dsT : i ↠ k ↠ E R:= mat "dsT"


abbrev cause := (0, ℕ)
abbrev year  := (1, ℕ)
abbrev objid := (2, ℕ)

/- Benchmark Queries -/
def spmv      := ∑ i, j: (ssA' : i ↠ j ↠ E R) * (dV : j ↠ E R)
def mul       := ∑ i, j, k: (ssA' : i ↠ j ↠ E R) * (dsB' : j ↠ k ↠ E R)
def mul_ss    := ∑ i, j, k: ssA * ssB_skip
def mttkrp    := ∑ i, j, k, l: sssC * (dsA' : j ↠ l ↠ E R) * (dsB' : k ↠ l ↠ E R)
def mul_inner := ∑ i, j, k: (ssA' : i ↠ k ↠ E R) * (ssB' : j ↠ k ↠ E R)
def udf       := ((λ _ : E R => 1) <$$> dsR) * (S.udf : i ↠ j ↠ E RMax)
def add_ss    := ∑ i, j: ((ssA' + ssB') : i ↠ j ↠ E R)
def inner     := ∑ i, j: ssA * ssB_ij

def threshold : E R := "threshold"
def filter_v    : i ↠ E R := S.valFilter (λ e => threshold << (e : E R)) sV
def filter_spmv := ∑ i, j: filter_v * ssA

def fires : year ↠ objid ↠ E R := mat "ssF"
def range_06_08 : year ↠ E R := (S.predRange (2006 : E ℕ) 2008 : ℕ →ₛ E R)
def count_range := ∑ year, objid: range_06_08 * fires

def E.succ {α} [Tagged α] [Add α] [OfNat α (nat_lit 1)] (e : E α) : E α :=
  E.call .add ![e, (1 : E α)]

namespace TPCH

abbrev custkey   := (0, ℕ)
abbrev orderkey  := (1, ℕ)
abbrev nationkey := (2, ℕ)
abbrev suppkey   := (3, ℕ)
abbrev regionkey := (4, ℕ)

def S.always0 {f} [Functor f] [Zero (E α)] : f (E ℕ) → f (E α) := Functor.map (λ _ => 0)
def S.always1 {f} [Functor f] [One (E α)] : f (E ℕ) → f (E α) := Functor.map (λ _ => 1)

def ssMat (f : String) : ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level .step 0 & S.level .step (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def tbl1 (f : String) : ℕ →ₛ E R := (csr.of f 1).level .step 0 |> S.always1
def ssTbl2 (f : String) : ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level .step 0 |> S.level .step (csr.of f 2) ⊚ S.always1
def dsTbl2 (f : String) : ℕ →ₐ ℕ →ₛ E R := range & S.level .step (csr.of f 2) ⊚ S.always1

def orders   : custkey   ↠ orderkey  ↠ E R := ssTbl2 "tpch_orders"
def customer : custkey   ↠ nationkey ↠ E R := dsTbl2 "tpch_customer"
def lineitem : orderkey  ↠ suppkey   ↠ E R := ssMat "tpch_lineitem"  -- R = l_extendedprice * (1 - l_discount)
def supplier : nationkey ↠ suppkey   ↠ E R := ssTbl2 "tpch_supplier"
def nation   : nationkey ↠ regionkey ↠ E R := dsTbl2 "tpch_nation"

def us_const : E ℕ := .var (.mk "US")
def us : nationkey ↠ E R := (S.predRange us_const us_const.succ : ℕ →ₛ E R)

def asia_const : E ℕ := .var (.mk "ASIA")
def asia : regionkey ↠ E R := (S.predRange asia_const asia_const.succ : ℕ →ₛ E R)

def q5 := ∑ custkey, orderkey, nationkey, suppkey, regionkey: lineitem * asia * orders * customer * supplier * nation
#check q5

end TPCH
/- end examples -/

#check (mat "f" : i ↠ j ↠ E R)
#check (ssA * ssB) * (S.lt : i ↠ k ↠ E R)
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
let fn := "q5"; (fn, compile_fun fn [go outVal TPCH.q5])
--  ("count_range", compile_fun "count_range" $ [go outVal count_range]),
--  ("triangle", compile_fun "triangle" $ [go outVal $ ∑ i, j, k : dsR * dsS * dsT ]),
--  ("udf", compile_fun "udf" $ [go outVal_max $ ∑ i, j: udf])
  --("triangle", compile_fun "triangle" $ [go outVal $ ∑ i, j, k : dsR * dsS * dsT  ])
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

#eval main
