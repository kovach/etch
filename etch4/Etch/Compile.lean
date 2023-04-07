import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul
import Etch.ShapeInference

class Compile (location value : Type _) where compile : Name → location → value → P

section Compile
open Compile

variable {L R}

instance base_var [Tagged α] [Add α] : Compile (Var α) (E α) where
  compile _ l v := .store_var l (E.var l + v)

instance base_mem [Tagged α] [Add α] : Compile (MemLoc α) (E α) where
  compile _ l v := .store_mem l.arr l.ind (l.access + v)

instance base_dump [Tagged α] : Compile (Dump α) (E α) where
  compile _ _ _ := .skip

instance S.step [Compile L R] [TaggedC ι] : Compile (lvl ι L) (ι →ₛ R) where
  compile n l r :=
    let (init, s) := r.init (n.fresh 0)
    let (push, position) := l.push (r.index s)
    let temp := ("index_lower_bound" : Var ι).fresh (n.fresh 1)
    init;; .while (r.valid s)
      (.decl temp (r.index s);;
       .branch (r.ready s)
         (push;; compile (n.fresh 2) position (r.value s);; r.succ s temp)
         (r.skip s temp))

instance S.step' {n} [Compile L R] [TaggedC ι] : Compile (lvl ι L) (n × ι ⟶ₛ R) where
  compile := fun n l (.str s) => S.step.compile n l s

instance contract [Compile α β] : Compile α (Contraction β) where
  compile n := λ storage ⟨ι, _, v⟩ =>
    let (init, s) := v.init (n.fresh 0)
    let temp := ("index_lower_bound" : Var ι).fresh (n.fresh 1)
    init ;; .while (v.valid s)
      (.decl temp (v.index s);;
       .branch (v.ready s)
        (compile (n.fresh 2) storage (v.value s);; v.succ s temp)
        (v.skip s temp))

-- Used only to generate callback for data loading
instance [Compile α β] : Compile (lvl ι α) (E ι × β) where
  compile n := λ storage v =>
    let (push, position) := storage.push v.1
    push;; Compile.compile n.freshen position v.2

end Compile

def go [Compile α β] (l : α) (r : β) : String := (Compile.compile emptyName l r).compile.emit.run
