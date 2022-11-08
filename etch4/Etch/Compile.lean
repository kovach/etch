import Etch.Basic
import Etch.ExtStream
import Etch.LVal

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

--instance [Compile α β] : Compile α ((β → P) → P) where
--  compile := λ l cc => cc (Compile.compile l)

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
def lB : lvl ℕ (lvl ℕ (MemLoc R)) := csr_mat "B" "dim" "i2"
--def lB : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "B"
def lC : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "C"

--variable {α : Type 1}

def outVar : Var R := "fout"
def sum1 : S ι α → Contraction α := S.contract
def sum2 : S ι (S ι' α) → Contraction (Contraction α) := S.contract ⊚ S.contract
def sum3 : S ι (S ι' (S ι'' α)) → Contraction (Contraction (Contraction α)) :=
S.contract ⊚ S.contract ⊚ S.contract
def exp0 (ι : Type _) : α → ι →ₐ α := λ (v : α) => λ _ => v
--def exp0 {ι : Type _} [Zero ι] [Tagged ι] (n : Var ι) : α → S ι α := S.repl n
def exp1 (ι'' : Type _) : (S ι' α) → (S ι' (Fun ι'' α)) := Functor.map $ exp0 ι''
--def exp1 {ι'' : Type _} [Zero ι''] [Tagged ι''] (n : String) : (S ι' α) → (S ι' (S ι'' α)) := Functor.map $ S.repl n
def exp2 (ι'' : Type _) : S ι (S ι' α) → S ι (S ι' (Fun ι'' α)) := Functor.map $ exp1 ι''
--def exp2 {ι'' : Type _} [Zero ι''] [Tagged ι''] (n : String) : S ι (S ι' α) → S ι (S ι' (S ι'' α)) := Functor.map (Functor.map $ S.repl n)

instance {ι α β γ} [HMul α β γ] : HMul (ι →ₛ α) (ι →ₐ β) (ι →ₛ γ) where hMul a b := {a with value := a.value * b a.bound}
instance {ι α β γ} [HMul β α γ] : HMul (ι →ₐ β) (ι →ₛ α) (ι →ₛ γ) where hMul b a := {a with value := b a.bound * a.value}
instance {ι α β γ} [HMul α β γ] : HMul (ι →ₐ α) (ι →ₐ β) (ι →ₐ γ) where hMul a b := λ v => a v * b v

variable (f : ι →ₛ α) (g : ι →ₐ α ) [Mul α]
#check exp0 ι f
example : ι→ₐι→ₛα := (exp0 ι f * exp0 ι g)

--def lt : E ℕ → E ℕ → E Bool := (. << .)
--def f1 := S.function ("f1_" : Var ℕ) (show E ℕ → E ℕ → E Bool from (. << .))
--#check (S.function ("f2_" : Var ℕ) <$> f1)
def S.lt : ℕ →ₛ ℕ →ₛ (E R) := S.function "f1_" ⊚ S.function "f2_" $ (. <ᵣ .)

section csr
variable {ι : Type} [Tagged ι] [DecidableEq ι]
[LE ι] [DecidableRel (LE.le : ι → ι → _)]
[LT ι] [DecidableRel (LT.lt : ι → ι → _)]

-- todo: move back into ExtStream
def csr.level : csr ι ℕ → E ℕ → S ι (E ℕ) := λ csr loc => S.interval_step csr.i csr.var (.access csr.v loc) (csr.v.access (loc+1))
--def csr.level : csr ι ℕ → E ℕ → S ι (E ℕ) := λ csr loc => S.interval_search csr.i csr.var (.access csr.v loc) (csr.v.access (loc+1))
def S.level {f} [Functor f] : csr ι ℕ → f (E ℕ) → f (S ι (E ℕ)) := Functor.map ∘ csr.level
def S.leaf  {f} [Functor f] : Var α → f (E ℕ) → f (E α) := Functor.map ∘ E.access
--def S.leaf' : Var α → E ℕ → E α := E.access
end csr

def A : ℕ →ₛ ℕ →ₛ E R := (csr.of "A" 1).level 0 & S.level (csr.of "A" 2) ⊚ S.leaf "A_vals"
def B : ℕ →ₛ ℕ →ₛ E R := (csr.of "B" 1).level 0 & S.level (csr.of "B" 2) ⊚ S.leaf "B_vals"
def B_csr : ℕ →ₐ ℕ →ₛ E R := range & S.level (csr.of "B" 2) ⊚ S.leaf "B_vals"
--def B_csr : ℕ →ₛ ℕ →ₛ E R := S.range "j2" 10000 & S.level (csr.of "B" 2) ⊚ S.leaf "B_vals"

@[reducible] def ijk := ℕ →ₛ ℕ →ₛ ℕ →ₛ E R
example : HMul (ℕ →ₛ ℕ →ₐ E R) (ℕ →ₛ ℕ →ₛ E R) (ℕ →ₛ ℕ →ₛ E R) := inferInstance
def mulAB := (((exp0 ℕ <$> .) <$> A)) * ((exp0 ℕ B_csr))
def mulAB_ij := mulAB * (exp0 ℕ <$> S.lt)
--def mulAB := ((exp0 "k1" <$> .) <$> A) * exp0 "i2" B_csr
--def mulAB_ij := mulAB * (exp0 "j3" <$> S.lt)

#eval IO.compile' "gen_query_1.c" [go lA SQLCallback]
#eval IO.compile' "gen_query_2.c" [go lB SQLCallback]
-- go lC (S.contract <$> mulAB), go lB A,
#eval IO.compile' "gen_main.c" [go outVar $ sum3 $ mulAB]
--#eval IO.compile' "gen_main.c" [go outVar $ sum3 $ mulAB]
