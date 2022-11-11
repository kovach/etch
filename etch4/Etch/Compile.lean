import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul
import Etch.ShapeInference

class Compile (α β : Type _) where compile : α → β → P

section Compile
open Compile

instance Comp.base_mem [Tagged α] [Add α] : Compile (MemLoc α) (E α) := ⟨λ l v => .store_mem l.arr l.ind (l.access + v) ⟩

instance base_var [Tagged α] [Add α] :
  Compile (Var α) (E α) where
  compile l v := .store_var l (E.var l + v)

instance step [Compile α β] : Compile (lvl ι α) (S ι β) where
  compile := λ storage v =>
    let (init, s) := v.init []
    let (push, position) :=
    storage.push (v.index s)
    init ;; P.while (v.valid s)
      (.branch (v.ready s)
        (push;; compile position (v.value s);; (v.succ s))
        (v.skip s (v.index s)))

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

end Compile
def go [Compile α β] (l : α) (r : β) : String := (Compile.compile l r).compile.emit.run
