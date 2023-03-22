import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul
import Etch.ShapeInference

class Compile (location value : Type _) where compile : Name → location → value → P

section Compile
open Compile

instance base_var [Tagged α] [Add α] : Compile (Var α) (E α) where
  compile _ l v := .store_var l (E.var l + v)

instance base_mem [Tagged α] [Add α] : Compile (MemLoc α) (E α) where
  compile _ l v := .store_mem l.arr l.ind (l.access + v)

instance S.step [Compile L R] [TaggedC ι] : Compile (lvl ι L) (ι →ₛ R) where
  compile n l r :=
    let (init, s) := r.init n
    let (push, position) := l.push (r.index s)
    let index := ("index_lower_bound" : Var ι).fresh n
    init;; .while (r.valid s)
      (.decl index (r.index s);;
       .branch (r.ready s)
         (push;; compile (n.fresh 0) position (r.value s);; (r.succ s index))
         (r.skip s index))

instance contract [Compile α β] : Compile α (Contraction β) where
  compile n := λ storage ⟨ι, _, v⟩ =>
    let (init, s) := v.init n
    let temp := ("index_lower_bound" : Var ι).fresh n
    init;;
    .while (v.valid s)
      (.decl temp (v.index s);;
       .branch (v.ready s)
        (Compile.compile (n.fresh 0) storage (v.value s);; v.succ s temp)
        (v.skip s temp))

section new
instance S'.step [Compile L R] [TaggedC ι] : Compile (lvl ι L) (S' ι R) where
  compile n l r :=
    let (push, position) := l.push r.index
    let index : Var ι    := .fresh "index" n
    let ready : Var Bool := .fresh "ready" n
    .while r.valid
      (.decl index r.index;;
       .decl ready r.ready;;
       .if1 ready (push;; compile (n.fresh 0) position r.value);;
       r.skip index ready)

instance Compile.Then [Compile L R] [Compile L R'] : Compile L (R <;;> R') where
  compile n l r := compile (n.fresh 0) l r.1 ;; compile (n.fresh 1) l r.2

instance Compile.Fun [Compile L R] : Compile L (Name → R) where
  compile n l r := compile (n.fresh 1) l (r $ n.fresh 0)

end new

-- Used only to generate callback for data loading
instance [Compile α β] : Compile (lvl ι α) (E ι × β) where
  compile n := λ storage v =>
    let (push, position) := storage.push v.1
    push;; Compile.compile n.freshen position v.2

end Compile

def go [Compile α β] (l : α) (r : β) : String := (Compile.compile emptyName l r).compile.emit.run
