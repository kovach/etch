import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul
import Etch.ShapeInference
import Etch.Compile


def IO.compile' (f : String) (body : List String) : IO Unit := IO.FS.writeFile f $ String.join body
def compile_fun (name : String) (body : List String) : String :=
let b := String.join body; s!"double {name}()\{ double val = 0;\n {b} return val; }"

def FSQLCallback : (E ℕ × E ℕ × E R) :=
(.call O.atoi ![.access "argv" 0],
 .call O.atoi ![.access "argv" 1],
 1)

def VSQLCallback : (E ℕ × E R) :=
(.call O.atoi ![.access "argv" 0],
 .call O.atof ![.access "argv" 1])

def SQLCallback : (E ℕ × E ℕ × E R) :=
(.call O.atoi ![.access "argv" 0],
 .call O.atoi ![.access "argv" 1],
 .call O.atof ![.access "argv" 2])

def SQLCallback3 : (E ℕ × E ℕ × E ℕ × E R) :=
(.call O.atoi ![.access "argv" 0],
 .call O.atoi ![.access "argv" 1],
 .call O.atoi ![.access "argv" 2],
 .call O.atof ![.access "argv" 3])

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
def exp1 (ι'' : Type _) : (S ι' α) → (S ι' (Fun ι'' α)) := Functor.map $ exp0 ι''
def exp2 (ι'' : Type _) : S ι (S ι' α) → S ι (S ι' (Fun ι'' α)) := Functor.map $ exp1 ι''

--def S.snd [Tagged α] [Zero α] [Tagged β] [Zero β] : β →ₛ α →ₛ (E α) := S.function "f1_" ⊚ S.function "f2_" $ λ _ x => x
--def S.fst [Tagged α] [Zero α] [Tagged β] [Zero β] : α →ₛ β →ₛ (E α) := S.function "f1_" ⊚ S.function "f2_" $ λ x _ => x
--def S.attr [Tagged α] [Zero α] : α →ₛ (E α) := S.function "f1_" id
def S.attr (i : ℕ × Type _) : i ↠ (E i.2) := .fun id

section funs
variable
{ι : Type} [Tagged ι] [DecidableEq ι] [LE ι] [DecidableRel (LE.le : ι → ι → _)] [LT ι] [DecidableRel (LT.lt : ι → ι → _)] [OfNat ι 0] [OfNat ι 1] [Add ι]
{ι' : Type} [Tagged ι'] [DecidableEq ι'] [LE ι'] [DecidableRel (LE.le : ι' → ι' → _)] [LT ι'] [DecidableRel (LT.lt : ι' → ι' → _)] [OfNat ι' 0] [OfNat ι' 1] [Add ι']

def toGuard {α β} [OfNat β (nat_lit 1)] : α → β := λ _ => 1
def binOp (f : E ι → E ι' → E α) : ι →ₛ ι' →ₛ E α := S.function "f1_" ⊚ S.function "f2_" $ f
def S.lt  : ℕ →ₛ ℕ →ₛ E R := binOp (. <ᵣ .)
def S.udf : ℕ →ₛ ℕ →ₛ E RMax := binOp λ a b => E.call .udf_max ![a,b]
end funs

def sVec   (f : String) : ℕ →ₛ E R := (csr.of f 1).level .step 0 & S.leaf (f ++ "_vals")
def dVec   (f : String) : ℕ →ₐ E R := range & S.leaf (f ++ "_vals")
def mat   (f : String) : ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level .step 0 & S.level .step (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def skip_mat   (f : String) : ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level .search 0 & S.level .step (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def mat3  (f : String) : ℕ →ₛ ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level .step 0 & S.level .step (csr.of f 2) ⊚ S.level .step (csr.of f 3) ⊚ S.leaf (f ++ "_vals")
def dsMat (f : String) : ℕ →ₐ ℕ →ₛ E R := range & S.level .step (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def ssA' := mat "ssA"
def dsA' := dsMat "dsA"
def ssB' := mat "ssB"
def dsB' := dsMat "dsB"
def dV   := dVec "V"
def sV   := sVec "sV"
example : HMul (ℕ →ₛ ℕ →ₐ E R) (ℕ →ₛ ℕ →ₛ E R) (ℕ →ₛ ℕ →ₛ E R) := inferInstance
--def mulAB := ((exp0 ℕ <$> .) <$> ssA) * (exp0 ℕ ssB)
--def mulAB_csr := ((exp0 ℕ <$> .) <$> ssA) * (exp0 ℕ dsB)
--def mulAB_inner := (exp0 ℕ <$> ssA) * (exp0 ℕ ssB)
--def mulAB_ij := mulAB * (exp0 ℕ <$> S.lt)

#eval IO.compile' "gen_query_dV.c" [go l_dV VSQLCallback]
#eval IO.compile' "gen_query_sV.c" [go l_sV VSQLCallback]
#eval IO.compile' "gen_query_dsA.c" [go l_dsA SQLCallback]
#eval IO.compile' "gen_query_dsB.c" [go l_dsB SQLCallback]
#eval IO.compile' "gen_query_ssA.c" [go l_ssA SQLCallback]
#eval IO.compile' "gen_query_ssB.c" [go l_ssB SQLCallback]
#eval IO.compile' "gen_query_sssC.c" [go l_sssC SQLCallback3]
#eval IO.compile' "gen_query_fires.c" [go l_ssF FSQLCallback]
#eval IO.compile' "gen_query_wcoj_R.c" [ go l_dsR FSQLCallback ]
#eval IO.compile' "gen_query_wcoj_S.c" [ go l_dsS FSQLCallback ]
#eval IO.compile' "gen_query_wcoj_T.c" [ go l_dsT FSQLCallback ]

--#eval IO.compile' "gen_main.c"  [go outVar $ sum3 $ mulAB]

-- todo
def names := [
  "add2",
  "inner2ss",
  "mul2_inner",
  "sum_add2",
  "sum_B_csr",
  "sum_inner3",
  "sum_mttkrp",
  "sum_mul2",
  "sum_mul2_csr",
  "sum_mul2_inner",
  "sum_ttm"
]

def ssA   : i ↠ j ↠ E R := mat "ssA"
def dsA   : i ↠ j ↠ E R := dsMat "dsA"
def ssB_ij : i ↠ j ↠ E R := mat "ssB"
def ssB   : j ↠ k ↠ E R := mat "ssB"
def ssB_skip   : j ↠ k ↠ E R := skip_mat "ssB"
def dsB   : j ↠ k ↠ E R := dsMat "dsB"
def sssC : i ↠ j ↠ k ↠ E R := mat3 "ssC"

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
def inner     :=  ∑ i, j: ssA * ssB_ij

def threshold : E R := "threshold"
def filter_v    : i ↠ E R := S.valFilter (λ e => threshold << (e : E R)) sV
def filter_spmv := ∑ i, j: filter_v * ssA

def fires : year ↠ objid ↠ E R := mat "ssF"
def range_06_08 : year ↠ E R := (S.predRange (2006 : E ℕ) 2008 : ℕ →ₛ E R)
def count_range := ∑ year, objid: range_06_08 * fires
/- end examples -/

--#check f1 * fires

#check (mat "f" : i ↠ j ↠ E R)
#check (ssA * ssB) * (S.lt : i ↠ k ↠ E R)
#check (ssA * ssB) * (E.ofNat <$$> S.attr i)
#check (S.attr i) * (S.attr j)
#check fires

def taco_ops : List (String × String) :=
[
-- ("inner2ss", compile_fun "inner2ss" $ [go outVal inner])
-- ("sum_add2", compile_fun "sum_add2" $ [go outVal $ sum2 $ ssA' + ssB']),
-- ("sum_mul2_csr", compile_fun "sum_mul2_csr" $ [go outVal mul])
-- ("sum_mul2", compile_fun "sum_mul2" $ [go outVal mul_ss])
-- ("mttkrp", compile_fun "mttkrp" [go outVal $ mttkrp ]),
-- ("spmv", compile_fun "spmv" $ [go outVal spmv])
-- ("sum_add2", compile_fun "sum_add2" $ [go outVal add_ss])
-- ("filter_spmv", compile_fun "filter_spmv" $ [go outVal filter_spmv])
]
--("sum_mul2_inner_ss", compile_fun "sum_mul2_inner_ss" $ [go outVal mul_inner]),
--("sum_add2", compile_fun "sum_add2" $ [go outVal $ sum2 $ ssA, go outVal $ sum2 $ ssB]),

def sql_ops : List (String × String) :=
[
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
  for x in taco_ops do
    funs := funs.append (x.2 ++ "\n")
    main_taco := main_taco.append $ s!"printf(\"{x.1}\\n\");time(&taco_{x.1}_, \"taco\", {reps}); time({x.1}, \"etch\", {reps});\nprintf(\"\\n\");"
  reps := 10
  for x in sql_ops do
    funs := funs.append (x.2 ++ "\n")
    main := main.append $ s!"printf(\"{x.1}\\n\"); time({x.1}, \"etch\", {reps});\nprintf(\"\\n\");"
    --main := main.append $ s!"printf(\"{x.1}\\n\");time(&sql_{x.1}_, \"sql \", {reps}); time({x.1}, \"etch\", {reps});\nprintf(\"\\n\");"
  IO.FS.writeFile "gen_funs.c" funs
  IO.FS.writeFile "gen_out.c" main
  IO.FS.writeFile "gen_out_taco.c" main_taco

#eval main
