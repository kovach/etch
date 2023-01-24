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

instance S.step [Compile L R] : Compile (lvl ι L) (ι →ₛ R) where
  compile n l r :=
    let (init, s) := r.init emptyName
    let (push, position) := l.push (r.index s)
    init;; .while (r.valid s)
      (.branch (r.ready s)
        (push;; compile n.freshen position (r.value s);; (r.succ s))
        (r.skip s (r.index s)))

-- inv: ∃ v, addr ↦ v ∧ₕ ⟦v⟧ + ⟦r⟧ = v₀
-- r.ready -> ⟦r⟧ = ⟦r.value⟧ + ⟦r.succ⟧
-- r.ready, lawful l.position r.value -> _ {{compile l.pos r.val}} λ h => l.position.addr h = ⟦r.val⟧
-- l.position.addr h = ⟦r.val⟧ → l.addr ↦ ⟦v_⟧ + ⟦r.value⟧
-- inv {{ l.push r.index;; compile (l.position r.index) r.value;; r.succ }} inv

instance contract [Compile α β] : Compile α (Contraction β) where
  compile n := λ storage ⟨_, v⟩ =>
    let (init, s) := v.init emptyName
    init ;; .while (v.valid s)
      (.branch (v.ready s)
        (Compile.compile n.freshen storage (v.value s);; v.succ s)
        (v.skip s (v.index s)))

-- Used only to generate callback for data loading
instance [Compile α β] : Compile (lvl ι α) (E ι × β) where
  compile n := λ storage v =>
    let (push, position) := storage.push v.1
    push;; Compile.compile n.freshen position v.2

end Compile

def go [Compile α β] (l : α) (r : β) : String := (Compile.compile emptyName l r).compile.emit.run
