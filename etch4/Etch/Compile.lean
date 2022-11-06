import Etch.Basic
import Etch.ExtStream
import Etch.LVal

-- todo: remove Comp
class Comp (α β : Type _) where compile : α → β

def S.compile [Comp α P] (s : S ι α) : P :=
s.init;;
.while s.valid
  (.branch (s.ready)
    (Comp.compile s.value;; s.succ)
    (s.skip s.bound))


instance (ι) [Comp α P] : Comp (S ι α) P :=
⟨ S.compile ⟩

instance [Tagged α] [Add α] : Comp (E α) P :=
⟨λ v : E α => .store_var "fout" (E.var "fout" + v) ⟩

---
class Comp' (α β : Type _) where compile : α → β → P

instance [Comp' α β] : Comp' (lvl ι α) (S ι β) :=
{ compile := λ storage v =>
    let (push, position) := storage.push v.bound
    v.init ;;
    P.while v.valid
      (.branch v.ready
        (push;; Comp'.compile position v.value;; v.succ)
        (v.skip v.bound)) }

instance [Tagged α] [Add α] : Comp' (MemLoc α) (E α) :=
⟨λ l v => .store_mem l.arr l.ind (l.access + v) ⟩

inductive SQL (α : Type _) | mk (v : α)

instance [Comp' α β] : Comp' (lvl ι α) (E ι × β) :=
{ compile := λ storage v =>
    let (push, position) := storage.push v.1
    push;; Comp'.compile position v.2 }

def v1  : S ℕ (E ℕ) := S.sparse "p1" "s1" "is1" "vs1"
def v1' : S ℕ (E ℕ) := S.sparseSearch "p1" "s1" "is1" "vs1"
def v2  : S ℕ (E ℕ) := S.sparse "p2" "s2" "is2" "vs2"
def v2' : S ℕ (E ℕ) := S.sparseSearch "p2" "s2" "is2" "vs2"

def m1  : S ℕ (E ℕ) := v1 * v2'

def incPrelude : String := "#include \"prelude.c\"\n"
def epilogue   : String := "#include \"epilogue.c\"\n"

def IO.compile [Comp α P] (m : α) : IO Unit := do
  let out : String := (Comp.compile m : P).compile.emit.run
  IO.FS.writeFile "out.cpp"  (incPrelude ++ out ++ epilogue)

def go' [Comp α P] (m : α) : String := (Comp.compile m : P).compile.emit.run

def go [Comp' α β] (l : α) (r : β) : String := (Comp'.compile l r).compile.emit.run

#check String.join
def IO.compile' (f : String) (body : List String) (wrapper := false) : IO Unit := do
  let out := (String.join body)
  let result := if wrapper then incPrelude ++ out ++ epilogue else out
  IO.FS.writeFile f result

--set_option trace.Meta.synthInstance.instances true
--set_option pp.all true

def n : E ℕ := "n"
--def is' : S ℕ (E ℕ) := S.interval "is" "i" 0 "n"
--def js' : S ℕ (E ℕ) := S.interval "js" "j" (.access "i_pos" "i") (.access "i_pos" "i" + 1)

def is (i : Var ℕ) : E ℕ → S ℕ (E ℕ) := λ n => S.interval "is" i 0 n
def is_skip (i : Var ℕ) : E ℕ → S ℕ (E ℕ) := λ n => S.interval_search "is" i 0 n
def js (j : Var ℕ) : E ℕ → S ℕ (E ℕ) := λ i => S.interval "js" j (.access "i_pos" i) (.access "i_pos" (i + 1))
def js_skip (j : Var ℕ) : E ℕ → S ℕ (E ℕ) := λ i => S.interval_search "js" j (.access "i_pos" i) (.access "i_pos" (i + 1))
def vals : E ℕ → E R := λ i => .access "vals" i
def dcsr1' := n & is "i1" ⊚ (js "j1" ⊚ vals) ⊚ S.repl "k1" "dim"

def dcsr2 := n & is_skip "j2" ⊚ js "k2" ⊚ vals
def dcsr2' := S.repl "i2" "dim" dcsr2

def A : S ℕ (S ℕ (E R)) := (csr.of "A" 1).level 0 & S.level (csr.of "A" 2) ⊚ S.leaf "A_vals"
def B : S ℕ (S ℕ (E R)) := (csr.of "B" 1).level 0 & S.level (csr.of "B" 2) ⊚ S.leaf "B_vals"

--#eval IO.compile $ dcsr1'.mul dcsr2'
--#eval IO.compile' $ dcsr1'.mul dcsr2'

def SQLCallback : (E ℕ × E ℕ × E R) :=
(.call O.atoi ![.access "argv" 0],
 .call O.atoi ![.access "argv" 1],
 .call O.atof ![.access "argv" 2])

def lA : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "A"
def lB : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "B"
def lC : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "C"

#check go lA SQLCallback

#eval IO.compile' "out_query_1.c" [go lA SQLCallback]
#eval IO.compile' "out.cpp" [go lB A, go' B] (wrapper := true)
