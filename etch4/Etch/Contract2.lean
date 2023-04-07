import Etch.Compile
import Etch.ShapeInference
import Etch.Stream

def Op.unit : Op Unit where
  argTypes := ![]
  spec := λ _ => ()
  opName := "unit"

def E.unit := E.call Op.unit ![]

def S.contract' (s : ι →ₛ α) : Unit →ₛ α :=
{ s with
  skip := fun p _ => s.skip p (s.index p)
  succ := fun p _ => s.succ p (s.index p)
  index := fun _ => .unit }

structure Storage (α : Type _) where
  σ       : Type
  init    : Name → P × σ
  reset   : σ → P 
  compile : Name → σ → α → P
  restore : σ → α

def Var.storage [Tagged α] [TaggedC α] [Zero α] [Add α] (orig : Var α) : Storage (E α) where
  σ       := Var α
  init  n := let v := orig.fresh n; ⟨v.decl 0, v⟩
  reset v := v.store_var 0
  compile := base_var.compile
  restore := E.var

def Storage.outVar [Tagged α] [TaggedC α] [Zero α] [Add α] : Storage (E α) :=
  Var.storage ("out" : Var α)

/- If `a` is strictly monotonic, then this is strictly monotonic.
   If `a` is only monotonic, then this could be not monotonic. -/
def S.buffer [Tagged ι] [TaggedC ι] [DecidableEq ι] (storage : Storage α) (a : ι →ₛ Unit →ₛ α) : ι →ₛ α where
  σ := a.σ × storage.σ × Var Bool × Var ι × Name
  skip := fun ⟨p, out, done, _, n⟩ i =>
    .branch (a.ready p * (a.index p == i) * -done.expr)
      (let v := a.value p
       let (init, s) := v.init (n.fresh 0)
       init;;
       storage.reset out;;
       .while (v.valid s)
         (.branch (v.ready s)
            (storage.compile (n.fresh 1) out (v.value s);; v.succ s .unit)
            (v.skip s .unit));;
       done.store_var 1)
      (a.skip p i)
  succ := fun ⟨p, _, done, prev, _⟩ i =>
    prev.store_var (a.index p);; a.succ p i;;
    .if1 (a.index p != prev) (done.store_var 0)
  value := fun ⟨_, out, _⟩ => storage.restore out
  ready := fun ⟨p, _, done, _⟩ => a.ready p * done.expr
  index := fun ⟨p, _⟩ => a.index p
  valid := fun ⟨p, _⟩ => a.valid p
  init n := let sub := a.init (n.fresh 0)
            let out := storage.init (n.fresh 1)
            let done := ("done" : Var Bool).fresh (n.fresh 2)
            let prev := ("prev" : Var ι).fresh (n.fresh 2)
            ⟨sub.1;; out.1;; done.decl 0, sub.2, out.2, done, prev, n.fresh 3⟩

def StrS.contract' [Tagged ι] [TaggedC ι] [DecidableEq ι] (storage : Storage α) : (n × ι ⟶ₛ m × ι' ⟶ₛ α) → (n × ι ⟶ₛ α)
| .str s => .str (S.buffer storage ((S.contract' ∘ StrS.inner) <$> s))

def S.singleton (i : E ι) (v : E α) : ι →ₛ E α where
  σ        := Var Bool
  skip _ _ := .skip
  succ p _ := p.store_var 1
  value _  := v
  ready _  := 1
  index _  := i
  valid p  := -p
  init  n  := let v := Var.fresh "visited" n; ⟨v.decl 0, v⟩

def S.reflect [Tagged α] [Zero α] [DecidableEq α] (a : ι →ₛ E α) : ι →ₛ α →ₛ E α :=
{ a with
  value := fun p => S.singleton (a.value p) (a.value p) }

def StrS.reflect [Tagged α] [Zero α] [DecidableEq α] {m} : (n × ι ⟶ₛ E α) → (n × ι ⟶ₛ m × α ⟶ₛ E α)
| .str s => .str (.str <$> S.reflect s)
