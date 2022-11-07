import Etch.Basic
import Etch.ExtStream
import Etch.LVal

class Compile (α β : Type _) where compile : α → β → P

instance Comp.base_var [Tagged α] [Add α] : Compile (Var α) (E α) :=
⟨λ l v => .store_var l $ E.var l + v ⟩
instance Comp.base_mem [Tagged α] [Add α] : Compile (MemLoc α) (E α) :=
⟨λ l v => .store_mem l.arr l.ind (l.access + v) ⟩

instance Comp.step [Compile α β] : Compile (lvl ι α) (S ι β) :=
{ compile := λ storage v =>
    let (push, position) := storage.push v.bound
    v.init ;;
    P.while v.valid
      (.branch v.ready
        (push;; Compile.compile position v.value;; v.succ)
        (v.skip v.bound)) }

instance [Compile α β] : Compile α (Contraction β) where
  compile := λ storage ⟨_, v⟩ =>
    v.init ;;
    P.while v.valid
      (.branch v.ready
        (Compile.compile storage v.value;; v.succ)
        (v.skip v.bound))

-- Used only to generate callback for data loading
instance [Compile α β] : Compile (lvl ι α) (E ι × β) :=
{ compile := λ storage v =>
    let (push, position) := storage.push v.1
    push;; Compile.compile position v.2 }

def v1  : S ℕ (E ℕ) := S.sparse "p1" "s1" "is1" "vs1"
def v1' : S ℕ (E ℕ) := S.sparseSearch "p1" "s1" "is1" "vs1"
def v2  : S ℕ (E ℕ) := S.sparse "p2" "s2" "is2" "vs2"
def v2' : S ℕ (E ℕ) := S.sparseSearch "p2" "s2" "is2" "vs2"

def m1  : S ℕ (E ℕ) := v1 * v2'

def incPrelude : String := "#include \"prelude.c\"\n"
def epilogue   : String := "#include \"epilogue.c\"\n"

def go [Compile α β] (l : α) (r : β) : String := (Compile.compile l r).compile.emit.run

def IO.compile' (f : String) (body : List String) : IO Unit := IO.FS.writeFile f $ String.join body

--set_option trace.Meta.synthInstance.instances true
--set_option pp.all true

--def n : E ℕ := "n"
--def is' : S ℕ (E ℕ) := S.interval "is" "i" 0 "n"
--def js' : S ℕ (E ℕ) := S.interval "js" "j" (.access "i_pos" "i") (.access "i_pos" "i" + 1)

def is (i : Var ℕ) : E ℕ → S ℕ (E ℕ) := λ n => S.interval_step "is" i 0 n
def is_skip (i : Var ℕ) : E ℕ → S ℕ (E ℕ) := λ n => S.interval_search "is" i 0 n
def js (j : Var ℕ) : E ℕ → S ℕ (E ℕ) := λ i => S.interval_step "js" j (.access "i_pos" i) (.access "i_pos" (i + 1))
def js_skip (j : Var ℕ) : E ℕ → S ℕ (E ℕ) := λ i => S.interval_search "js" j (.access "i_pos" i) (.access "i_pos" (i + 1))
def vals : E ℕ → E R := λ i => .access "vals" i
--def dcsr1' := n & is "i1" ⊚ (js "j1" ⊚ vals) ⊚ S.repl "k1" "dim"
--def dcsr2 := n & is_skip "j2" ⊚ js "k2" ⊚ vals
--def dcsr2' := S.repl "i2" "dim" dcsr2
--#eval IO.compile $ dcsr1'.mul dcsr2'
--#eval IO.compile' $ dcsr1'.mul dcsr2'

def SQLCallback : (E ℕ × E ℕ × E R) :=
(.call O.atoi ![.access "argv" 0],
 .call O.atoi ![.access "argv" 1],
 .call O.atof ![.access "argv" 2])

def lA : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "A"
def lB : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "B"
def lC : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "C"

def outVar : Var R := "fout"
def sum1 : S ι α → Contraction α := S.contract
def sum2 : S ι (S ι' α) → Contraction (Contraction α) := S.contract ⊚ S.contract
def sum3 : S ι (S ι' (S ι'' α)) → Contraction (Contraction (Contraction α)) :=
S.contract ⊚ S.contract ⊚ S.contract
def exp0 {ι : Type _} [Zero ι] [Tagged ι] (n : Var ι) : α → S ι α := S.repl' n
def exp1 {ι'' : Type _} [Zero ι''] [Tagged ι''] (n : String) : (S ι' α) → (S ι' (S ι'' α)) :=
Functor.map $ S.repl' n
def exp2 {ι'' : Type _} [Zero ι''] [Tagged ι''] (n : String) : S ι (S ι' α) → S ι (S ι' (S ι'' α)) :=
Functor.map (Functor.map $ S.repl' n)

def A : S ℕ (S ℕ (E R)) := (csr.of "A" 1).level 0 & S.level (csr.of "A" 2) ⊚ S.leaf "A_vals"
def B : S ℕ (S ℕ (E R)) := (csr.of "B" 1).level 0 & S.level (csr.of "B" 2) ⊚ S.leaf "B_vals"

def k1 : Var ℕ := "k1"
def mulAB := ((exp0 k1 <$> .) <$> A) * exp0 "i2" B

def A' := S.contract $ S.contract <$> A

#eval IO.compile' "gen_query_1.c" [go lA SQLCallback]
-- go lC (S.contract <$> mulAB),
#eval IO.compile' "gen_main.c" [go lB A, go outVar $ sum3 $ mulAB]

