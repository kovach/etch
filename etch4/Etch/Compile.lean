import Etch.Basic
import Etch.ExtStream
import Etch.LVal
import Etch.Add
import Etch.ShapeInference

class Compile (α β : Type _) where compile : α → β → P

instance Comp.base_var [Tagged α] [Add α] : Compile (Var α) (E α) := ⟨λ l v => .store_var l $ E.var l + v ⟩
instance Comp.base_mem [Tagged α] [Add α] : Compile (MemLoc α) (E α) := ⟨λ l v => .store_mem l.arr l.ind (l.access + v) ⟩

instance Comp.step [Compile α β] : Compile (lvl ι α) (S ι β) :=
{ compile := λ storage v => let (push, position) := storage.push v.bound
    v.init ;; P.while v.valid
      (.branch v.ready
        (push;; Compile.compile position v.value;; v.succ)
        (v.skip v.bound)) }

instance Comp.contract [Compile α β] : Compile α (Contraction β) where
  compile := λ storage ⟨_, v⟩ =>
    v.init ;; P.while v.valid
      (.branch v.ready
        (Compile.compile storage v.value;; v.succ)
        (v.skip v.bound))

-- Used only to generate callback for data loading
instance [Compile α β] : Compile (lvl ι α) (E ι × β) :=
{ compile := λ storage v =>
    let (push, position) := storage.push v.1
    push;; Compile.compile position v.2 }

def go [Compile α β] (l : α) (r : β) : String := (Compile.compile l r).compile.emit.run

def IO.compile' (f : String) (body : List String) : IO Unit := IO.FS.writeFile f $ String.join body
def compile_fun (name : String) (body : List String) : String :=
let b := String.join body; s!"double {name}()\{ double val = 0;\n {b} return val; }"

def SQLCallback : (E ℕ × E ℕ × E R) :=
(.call O.atoi ![.access "argv" 0],
 .call O.atoi ![.access "argv" 1],
 .call O.atof ![.access "argv" 2])

def l_ssA : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssA"
def l_dsA : lvl ℕ (lvl ℕ (MemLoc R)) := csr_mat "dsA" "dim" "i1"
def l_ssB : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssB"
def l_dsB : lvl ℕ (lvl ℕ (MemLoc R)) := csr_mat "dsB" "dim" "i1" -- todo "i2"

def outVar : Var R := "fout"
def outVal : Var R := "val"
def sum1 : S ι α → Contraction α := S.contract
def sum2 : S ι (S ι' α) → Contraction (Contraction α) := S.contract ⊚ sum1
def sum3 : S ι (S ι' (S ι'' α)) → Contraction (Contraction (Contraction α)) := S.contract ⊚ sum2
def exp0 (ι : Type _) : α → ι →ₐ α := λ (v : α) => λ _ => v
def exp1 (ι'' : Type _) : (S ι' α) → (S ι' (Fun ι'' α)) := Functor.map $ exp0 ι''
def exp2 (ι'' : Type _) : S ι (S ι' α) → S ι (S ι' (Fun ι'' α)) := Functor.map $ exp1 ι''

def S.lt : ℕ →ₛ ℕ →ₛ (E R) := S.function "f1_" ⊚ S.function "f2_" $ (. <ᵣ .)

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
#eval IO.compile' "gen_main.c" [go outVar $ sum3 $ mulAB]

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

def etch_ops : List (String × String) :=
[
  ("inner2ss", compile_fun "inner2ss" $ [go outVal $ ∑ i, j: ssA' * ssB_ij]),
  ("sum_add2", compile_fun "sum_add2" $ [go outVal $ sum2 $ ssA + ssB]),
  --("sum_add2", compile_fun "sum_add2" $ [go outVal $ ∑ i, j: ssA' + ssB_ij]),
  --("sum_add2", compile_fun "sum_add2" $ [go outVal $ sum2 $ ssA, go outVal $ sum2 $ ssB]),
  ("sum_mul2_csr", compile_fun "sum_mul2_csr" $ [go outVal $ ∑ i, j, k: ssA' * dsB'])
]

def main : IO Unit := do
  let mut funs := ""
  let mut main := ""
  for x in etch_ops do
    funs := funs.append (x.2 ++ "\n")
    let reps := 50
    main := main.append $ s!"printf(\"{x.1}\\n\");time(&taco_{x.1}_, \"taco\", {reps}); time({x.1}, \"etch\", {reps});\nprintf(\"\\n\");"
  IO.FS.writeFile "gen_funs.c" funs
  IO.FS.writeFile "gen_out.c" main

#eval main
