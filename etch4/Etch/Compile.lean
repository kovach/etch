import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul
import Etch.ShapeInference

class Compile (α β : Type _) where compile : α → β → P

instance Comp.base_var [Tagged α] [Add α] : Compile (Var α) (E α) := ⟨λ l v => .store_var l $ E.var l + v ⟩
instance Comp.base_mem [Tagged α] [Add α] : Compile (MemLoc α) (E α) := ⟨λ l v => .store_mem l.arr l.ind (l.access + v) ⟩

instance Comp.step [Compile α β] : Compile (lvl ι α) (S ι β) :=
{ compile := λ storage v =>
    let (init, s) := v.init [];
    let (push, position) := storage.push $ v.index s
    init ;; P.while (v.valid s)
      (.branch (v.ready s)
        (push;; Compile.compile position (v.value s);; (v.succ s))
        (v.skip s (v.index s))) }

instance Comp.contract [Compile α β] : Compile α (Contraction β) where
  compile := λ storage ⟨_, v⟩ =>
    let (init, s) := v.init [];
    init ;; P.while (v.valid s)
      (.branch (v.ready s)
        (Compile.compile storage (v.value s);; v.succ s)
        (v.skip s (v.index s)))

-- Used only to generate callback for data loading
instance [Compile α β] : Compile (lvl ι α) (E ι × β) :=
{ compile := λ storage v =>
    let (push, position) := storage.push v.1
    push;; Compile.compile position v.2 }

-- fix typed initialization
def go [Compile α β] (l : α) (r : β) : String := (Compile.compile l r).compile.emit.run

def IO.compile' (f : String) (body : List String) : IO Unit := IO.FS.writeFile f $ String.join body
def compile_fun (name : String) (body : List String) : String :=
let b := String.join body; s!"double {name}()\{ double val = 0;\n {b} return val; }"

def FSQLCallback : (E ℕ × E ℕ × E R) :=
(.call O.atoi ![.access "argv" 0],
 .call O.atoi ![.access "argv" 1],
 1)

def SQLCallback : (E ℕ × E ℕ × E R) :=
(.call O.atoi ![.access "argv" 0],
 .call O.atoi ![.access "argv" 1],
 .call O.atof ![.access "argv" 2])

def l_ssA : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssA"
def l_dsA : lvl ℕ (lvl ℕ (MemLoc R)) := csr_mat "dsA" "dim" "i1"
def l_ssB : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssB"
def l_dsB : lvl ℕ (lvl ℕ (MemLoc R)) := csr_mat "dsB" "dim" "i1" -- todo "i2"
def l_ssF : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssF"

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

def S.lt : ℕ →ₛ ℕ →ₛ (E R) := S.function "f1_" ⊚ S.function "f2_" $ (. <ᵣ .)
def S.snd [Tagged α] [Zero α] [Tagged β] [Zero β] : β →ₛ α →ₛ (E α) := S.function "f1_" ⊚ S.function "f2_" $ λ _ x => x
def S.fst [Tagged α] [Zero α] [Tagged β] [Zero β] : α →ₛ β →ₛ (E α) := S.function "f1_" ⊚ S.function "f2_" $ λ x _ => x
--def S.attr [Tagged α] [Zero α] : α →ₛ (E α) := S.function "f1_" id
def S.attr (i : ℕ × Type _) : i ↠ (E i.2) := .fun id

section csr
variable {ι : Type} [Tagged ι] [DecidableEq ι]
[LE ι] [DecidableRel (LE.le : ι → ι → _)]
[LT ι] [DecidableRel (LT.lt : ι → ι → _)]

end csr

def mat   (f : String) : ℕ →ₛ ℕ →ₛ E R := (csr.of f 1).level .step 0 & S.level .step (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def dsMat (f : String) : ℕ →ₐ ℕ →ₛ E R := range & S.level .step (csr.of f 2) ⊚ S.leaf (f ++ "_vals")
def ssA := mat "ssA"
def dsA := dsMat "dsA"
def ssB := mat "ssB"
def dsB := dsMat "dsB"

--@[reducible] def ijk := ℕ →ₛ ℕ →ₛ ℕ →ₛ E R
example : HMul (ℕ →ₛ ℕ →ₐ E R) (ℕ →ₛ ℕ →ₛ E R) (ℕ →ₛ ℕ →ₛ E R) := inferInstance
def mulAB := ((exp0 ℕ <$> .) <$> ssA) * (exp0 ℕ ssB)
def mulAB_csr := ((exp0 ℕ <$> .) <$> ssA) * (exp0 ℕ dsB)
def mulAB_inner := (exp0 ℕ <$> ssA) * (exp0 ℕ ssB)

def mulAB_ij := mulAB * (exp0 ℕ <$> S.lt)

#eval IO.compile' "gen_query_dsA.c" [go l_dsA SQLCallback]
#eval IO.compile' "gen_query_dsB.c" [go l_dsB SQLCallback]
#eval IO.compile' "gen_query_ssA.c" [go l_ssA SQLCallback]
#eval IO.compile' "gen_query_ssB.c" [go l_ssB SQLCallback]
#eval IO.compile' "gen_query_fires.c" [go l_ssF FSQLCallback]

#eval IO.compile' "gen_main.c"  [go outVar $ sum3 $ mulAB]

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

def ssA'   : i ↠ j ↠ E R := mat "ssA"
def dsA'   : i ↠ j ↠ E R := dsMat "dsA"
def ssB_ij : i ↠ j ↠ E R := mat "ssB"
def ssB'   : j ↠ k ↠ E R := mat "ssB"
def dsB'   : j ↠ k ↠ E R := dsMat "dsB"

abbrev cause := (0, ℕ)
abbrev year  := (1, ℕ)

def fires : cause ↠ year ↠ E R := mat "ssF"

#check (mat "f" : i ↠ j ↠ E R)
#check (ssA' * ssB') * (S.lt : i ↠ k ↠ E R)
#check (ssA' * ssB') * (E.ofNat <$$> S.attr i)

def taco_ops : List (String × String) :=
[
  ("inner2ss", compile_fun "inner2ss" $ [go outVal $ ∑ i, j: ssA' * ssB_ij]),
  ("sum_add2", compile_fun "sum_add2" $ [go outVal $ sum2 $ ssA + ssB]),
  --("sum_add2", compile_fun "sum_add2" $ [go outVal $ ∑ i, j: ssA' + ssB_ij]),
  --("sum_add2", compile_fun "sum_add2" $ [go outVal $ sum2 $ ssA, go outVal $ sum2 $ ssB]),
  ("sum_mul2_csr", compile_fun "sum_mul2_csr" $ [go outVal $ ∑ i, j, k: ssA' * dsB'])
]

def minyear_ish := ∑ cause, year: (E.toMin <$$> fires) * (E.toMin ∘ E.ofNat <$$> S.attr year)
def minyear_ish' := ∑ cause, year: (E.toMax <$$> fires)
def sql_ops : List (String × String) :=
[
  ("count_fires", compile_fun "count_fires" $ [go outVal_max $ minyear_ish'])
]

def main : IO Unit := do
  let mut funs := ""
  let mut main := ""
  let mut reps := 50
  for x in taco_ops do
    funs := funs.append (x.2 ++ "\n")
    main := main.append $ s!"printf(\"{x.1}\\n\");time(&taco_{x.1}_, \"taco\", {reps}); time({x.1}, \"etch\", {reps});\nprintf(\"\\n\");"
  reps := 2
  for x in sql_ops do
    funs := funs.append (x.2 ++ "\n")
    main := main.append $ s!"printf(\"{x.1}\\n\");time({x.1}, \"etch\", {reps});\nprintf(\"\\n\");"
  IO.FS.writeFile "gen_funs.c" funs
  IO.FS.writeFile "gen_out.c" main

#eval main
