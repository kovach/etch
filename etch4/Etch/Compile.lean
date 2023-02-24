import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul
--import Etch.ShapeInference

inductive NameProc α
| new : Name → NameProc α
| old : Name →  α → NameProc α

--def Stateful.init [Stateful α] (v : α) : NameProc (Stateful.σ v) → Name × P × Stateful.σ v
--| .new n => (n.freshen, Stateful.init' n v)
--| .old n s => (n, .skip, s)

class Compile (lval rval : Type _) [Stateful rval] where
  compileWithState : (v : rval) → Name → lval → P × (Stateful.σ v)
  compile : (v : rval) → Name → lval → P := fun v n l ↦ compileWithState v n l |>.fst

class Compile' (lval rval : Type _) [Stateful rval] where compile : (v : rval) → Stateful.σ v → lval → P

--instance : Init (ι →ₛ α) where
--  σ s := s.σ
--  init name s := s.init name
--
--structure WithInit (α : Type _) [Init α] where
--  val : α
--  init : Name → P × Init.σ val

--instance [Init α] : Init (WithInit α) where
--  σ s := Init.σ s.val
--  init n v := v.init n

--def SeqExec (τ : Type _) [StreamLike τ τ'] := (s : S.sequence τ) × (P × StreamLike.σ s.a)

--instance [StreamLike τ τ'] : StreamLike (S.sequence τ) (SeqExec τ) where
--  σ v := StreamLike.σ v.a
--  name n seq := ⟨ seq, StreamLike.name n seq.a ⟩

section Compile
open Compile

instance base_var [Tagged α] [Add α] : Compile (Var α) (E α) where
  compileWithState v _ l := (.store_var l (E.var l + v), ())

instance base_mem [Tagged α] [Add α] : Compile (MemLoc α) (E α) where
  compileWithState v _ l := (.store_mem l.arr l.ind (l.access + v), ())

instance base_mem_mem [Tagged α] [Add α] : Compile (MemLoc α) (MemLoc α) where
  compileWithState v _ l := (.store_mem l.arr l.ind (l.access + v.access), ())

def Stateful.init [Init α] : (v : α) → Name → P × σ v := fun v n ↦ Init.init' n v
def new : Name → Name := Name.freshen

variable {ι : Type} [Tagged ι]

instance S.step (R) [Stateful R] [Compile L R] : Compile (lvl ι L) (ι →ₛ R) where
  compileWithState r n l :=
    let (init, s) := Stateful.init r n
    let (push, position) := l.push (r.index s)
    let temp := ("index_lower_bound" : Var ι).fresh n
    (init;; .while (r.valid s)
      (.decl temp (r.index s);;
       .branch (r.ready s)
         (push;; compile (r.value s) (new n) position;; (r.succ s temp))
         (r.skip s temp)), s)

instance contract [Init β] [Compile α β] : Compile α (Contraction ι β) where
  compileWithState ct n l :=
    let ⟨r⟩ := ct
    let (init, s) := Stateful.init r n
    let temp := ("index_lower_bound" : Var ι).fresh n
    (init ;; .while (r.valid s)
      (.decl temp (r.index s);;
       .branch (r.ready s)
        (Compile.compile (r.value s) (new n) l;; r.succ s temp)
        (r.skip s temp)), s)

section Sequence
variable (α β : Type _) [Init α] [Stateful β]

instance sequence [Compile L α] [Compile' L β] : Compile L (Sequence α β) where
  compileWithState seq n lval :=
    --let (init, s₀) := Stateful.init seq.a n
    --Compile'.compile seq.b (.old n $ seq.f s₀) lval
    let (p₁, s₁) := compileWithState seq.a n lval
    (p₁;; Compile'.compile seq.b (seq.f s₁) lval, s₁)

instance sequence' [Compile' L α] [Compile' L β] : Compile' L (Sequence α β) where
  compile seq s₁ lval := Compile'.compile seq.a s₁ lval;; Compile'.compile seq.b (seq.f s₁) lval

end Sequence

instance [Init β] : Init (E ι × β) where
  σ v := Stateful.σ v.2
  init' n v := Init.init' n v.2

-- Used only to generate callback for sql data loading
instance [Init β] [Compile α β] : Compile (lvl ι α) (E ι × β) where
  compileWithState v n storage :=
    let (init, s) := Stateful.init v n
    let (push, position) := storage.push v.1
    (init;; push;; Compile.compile v.2 (new n) position, s)

end Compile

def go [Init β] [Compile α β] (l : α) (r : β) : String := (Compile.compile r emptyName l).compile.emit.run

