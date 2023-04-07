import Etch.Benchmark.Basic
import Etch.Benchmark.SQL
import Etch.Contract2
import Etch.LVal
import Etch.Mul
import Etch.ShapeInference
import Etch.Stream


def Op.access1 {α β : Type _} [Inhabited α] : Op (ℕ → α) where
  argTypes := ![ℕ → α × β]
  spec := fun a n => match n with | 0 => (a 0 0).1
                                  | _ => default
  opName := "tuple_access1"

def Op.access2 {α β : Type _} [Inhabited β] : Op (ℕ → β) where
  argTypes := ![ℕ → α × β]
  spec := fun a n => match n with | 0 => (a 0 0).2
                                  | _ => default
  opName := "tuple_access2"

def Op.get1 {α β : Type _} : Op α where
  argTypes := ![α × β]
  spec := fun a => (a 0).1
  opName := "tuple_get1"

def Op.get2 {α β : Type _} : Op β where
  argTypes := ![α × β]
  spec := fun a => (a 0).2
  opName := "tuple_get2"

namespace Etch.Benchmark.TPCHq18

-- Schema

abbrev orderkey    := (0, ℕ)
abbrev linenumber  := (1, ℕ)
abbrev sumquantity := (2, ℕ)
abbrev custkey     := (3, ℕ)
abbrev custname    := (4, String)
abbrev quantity    := (5, ℕ)
abbrev orderdate   := (6, ℕ)
abbrev totalprice  := (7, R)

def lineitem : orderkey ↠ₛ linenumber ↠ₛ quantity ↠ₛ E ℕ :=
  (SQL.ss_ "tpch_q18_lineitem" : ℕ →ₛ ℕ →ₛ ℕ →ₛ E ℕ)
def customer : custkey ↠ₐ custname ↠ₛ E ℕ :=
  (SQL.ds  "tpch_q18_customer" : ℕ →ₐ String →ₛ E ℕ)
def order : orderkey ↠ₐ custkey ↠ₛ orderdate ↠ₛ totalprice ↠ₛ E ℕ :=
  (SQL.ds__ "tpch_q18_order" : ℕ →ₐ ℕ →ₛ ℕ →ₛ R →ₛ E ℕ)

-- Query

def quantity_id : quantity ↠ₐ E ℕ := f
  where f : ℕ →ₐ E ℕ := id

def lineitem_with_sumquantity' : orderkey ↠ₛ E ℕ :=
  (lineitem * quantity_id)
  |> (StrS.contract' .outVar <$> ·)
  |> StrS.contract' .outVar
def lineitem_with_sumquantity : orderkey ↠ₛ sumquantity ↠ₛ E ℕ :=
  (lineitem * quantity_id)
  |> (StrS.contract' .outVar <$> ·)
  |> StrS.contract' .outVar
  |> StrS.reflect

def filter : sumquantity ↠ₐ E Bool := f
  where f : ℕ →ₐ E Bool := fun q => q >> (300 : E ℕ)

def q18 := ∑ sumquantity : lineitem_with_sumquantity * filter * customer * order

-- Compile... a bit unfortunate

local instance (α) : ToString (Var α) := ⟨Var.toString⟩
local instance : ToString DeclType := ⟨fun | .mk s => s⟩
def compile [Compile (lvl ℕ (lvl ℕ (lvl String (lvl ℕ (lvl R (MemLoc ℕ)))))) Z] (name : String) (exp : Z) : String :=
  let tpl1 := "std::tuple<int, int>"
  let tpl2 := "std::tuple<const char*, std::tuple<int, std::tuple<double, int>>>"
  let T := s!"std::unordered_map<{tpl1}, {tpl2}, hash_tuple::hash<{tpl1}>>"
  let out : Var (ℕ × ℕ → String × ℕ × R × ℕ) := "out";
  let outLoc  : Var (ℕ → String × ℕ × R × ℕ) := "out_loc";
  let outLoc1 : Var (ℕ → String) := "custname";
  let outLoc2 : Var (ℕ → ℕ × R × ℕ) := "out_loc2";
  let outLoc3 : Var (ℕ → ℕ) := "orderdate";
  let outLoc4 : Var (ℕ → R × ℕ) := "out_loc4";
  let outLoc5 : Var (ℕ → R) := "totalprice";
  let outLoc6 : Var (ℕ → ℕ) := "sumquantity";
  let outVal : lvl ℕ (lvl ℕ (lvl String (lvl ℕ (lvl R (MemLoc ℕ))))) := {
    push := fun i =>
      (.skip, ⟨fun j =>
        (outLoc.store_var (E.call Op.indexMap2 ![out.expr, i, j]);;
         outLoc1.store_var (E.call Op.access1 ![outLoc.expr]);;
         outLoc2.store_var (E.call Op.access2 ![outLoc.expr]);;
         outLoc3.store_var (E.call Op.access1 ![outLoc2.expr]);;
         outLoc4.store_var (E.call Op.access2 ![outLoc2.expr]);;
         outLoc5.store_var (E.call Op.access1 ![outLoc4.expr]);;
         outLoc6.store_var (E.call Op.access2 ![outLoc4.expr]),
         ⟨fun k => (outLoc1.store_mem 0 k,
          ⟨fun l => (outLoc3.store_mem 0 l,
           ⟨fun m => (outLoc5.store_mem 0 m, ⟨outLoc6, 0⟩)⟩)⟩) ⟩)⟩) }
  s!"{T} {name}() \{\n {T} {out};\n {tpl2}* {outLoc};
 const char** {outLoc1};
 std::tuple<int, std::tuple<double, int>>* {outLoc2};
 int* {outLoc3};
 std::tuple<double, int>* {outLoc4};
 double* {outLoc5};
 int* {outLoc6};
 {go outVal exp}\n return out;\n}"

def funcs : List (String × String) := [
  let fn := "test"; (fn, compileFunMap ℕ ℕ fn lineitem_with_sumquantity'),
  let fn := "test2"; (fn, compileFunMap2 ℕ ℕ ℕ fn lineitem_with_sumquantity),
  let fn := "q18"; (fn, compile fn q18)
]

end Etch.Benchmark.TPCHq18

namespace Etch.Benchmark.Transpose

def Op.mkPair : Op (α × β) where
  argTypes := ![α, β]
  spec := fun a => (a 0, a 1)
  opName := "mk_pair"


structure Map (ι α : Type _) where
  (l : List ι)
  (f : ι → α)
instance [Inhabited α] : Inhabited (Map ι α) := ⟨⟨[], fun _ => default⟩⟩ 
instance [Zero α] : Zero (Map ι α) := ⟨⟨[], fun _ => 0⟩⟩ 

def Op.mkMap {ι : Type} {α : Type _} [Zero α] : Op (Map ι α) where
  argTypes := ![]
  spec := fun _ => 0
  opName := "mk_map"

def Op.indexMap' {α γ : Type} [Inhabited γ] : Op (ℕ → γ) where
  argTypes := ![Map α γ, α]
  spec := fun a => fun | 0 => (a 0).f (a 1)
                       | _ => default
  opName := "index_map"

def Op.mkNullPtr {α : Type _} [Zero α] : Op (ℕ → α) where
  argTypes := ![]
  spec := fun _ _ => 0
  opName := "mk_nullptr"

structure Iterator (α : Type _) where
  (l : List α)
def Iterator.value : Iterator α → Option α
| ⟨List.cons h _⟩ => some h
| _ => none
def Iterator.next : Iterator α → Option (Iterator α)
| ⟨List.cons _ t⟩ => some ⟨t⟩
| _ => none

instance : Tagged (Iterator α) := ⟨"iterator"⟩
instance : TaggedC (Iterator α) := ⟨⟨"auto"⟩⟩

def Op.mapBegin {ι α : Type _} : Op (Iterator (ι × α)) where
  argTypes := ![Map ι α]
  spec := fun a => ⟨(a 0).l.map (fun i => (i, (a 0).f i))⟩ 
  opName := "map_begin"

def Op.mapEnd {ι α : Type _} : Op (Iterator (ι × α)) where
  argTypes := ![Map ι α]
  spec := fun _ => ⟨[]⟩
  opName := "map_end"

def Op.iteratorNext {ι α : Type _} : Op (Iterator (ι × α)) where
  argTypes := ![Iterator (ι × α)]
  spec := fun a => match (a 0).next with | some x => x | none => ⟨[]⟩
  opName := "iterator_next"

def Op.iteratorKey {ι α : Type _} [Inhabited ι] : Op ι where
  argTypes := ![Iterator (ι × α)]
  spec := fun a => match a 0 with | ⟨h::_⟩ => h.1
                                  | ⟨[]⟩ => panic! "should never happen"
  opName := "iterator_key"

def Op.iteratorKey2 {ι₁ ι₂ α : Type _} [Inhabited (ι₁ × ι₂)] : Op (ι₁ × ι₂) where
  argTypes := ![Iterator ((ι₁ × ι₂) × α)]
  spec := fun a => match a 0 with | ⟨h::_⟩ => h.1
                                  | ⟨[]⟩ => panic! "should never happen"
  opName := "iterator_key"

def Op.iteratorValue {ι α : Type _} [Inhabited α] : Op α where
  argTypes := ![Iterator (ι × α)]
  spec := fun a => match a 0 with | ⟨h::_⟩ => h.2
                                  | ⟨[]⟩ => panic! "should never happen"
  opName := "iterator_value"

instance [DecidableEq α] : DecidableEq (Iterator α) :=
  fun ⟨a⟩ ⟨b⟩ => if h : a = b
                 then .isTrue (by simpa using h)
                 else .isFalse (by simpa using h)

section

open TaggedC (tag)

-- local instance (α) : ToString (Var α) := ⟨Var.toString⟩
local instance : ToString DeclType := ⟨fun | .mk s => s⟩

def Storage.map [TaggedC ι] [DecidableEq ι] [Inhabited ι] [Tagged α] [TaggedC α] [Zero α] [Add α] [Inhabited α] [DecidableEq α] : Storage (ι →ₛ E α) where
  σ       := Var (Map ι α) × Var (ℕ → α)
  init  n := let out := ("out" : Var (Map ι α)).fresh n
             let _ : TaggedC (Map ι α) := ⟨⟨s!"std::map<{tag ι}, {tag α}, {tag ι}_comp>"⟩⟩
             let outLoc := ("out_loc" : Var (ℕ → α)).fresh n
             ⟨out.decl (.call Op.mkMap ![]), out, outLoc⟩
  reset   := fun ⟨m, p⟩ => m.store_var (E.call Op.mkMap ![]);;
                           p.store_var (E.call Op.mkNullPtr ![])
  compile := fun n ⟨m, p⟩ =>
               S.step.compile n
                 { push := fun i => (p.store_var (E.call Op.indexMap' ![m.expr, i]),
                                     MemLoc.mk p 0) }
  restore := fun ⟨m, _⟩ => {
               σ := Var (Iterator (ι × α))
               init := fun n => let it := ("it" : Var (Iterator (ι × α))).fresh n
                                ⟨it.decl (.call Op.mapBegin ![m.expr]), it⟩
               succ := fun p _ => p.store_var (.call Op.iteratorNext ![p.expr])
               skip := fun _ _ => .skip
               valid := fun p => p.expr != .call Op.mapEnd ![m.expr]
               ready := fun _ => 1
               index := fun p => .call Op.iteratorKey ![p.expr]
               value := fun p => .call Op.iteratorValue ![p.expr]
             }

def Storage.map2 [TaggedC ι₁] [DecidableEq ι₁] [Inhabited ι₁]
                 [TaggedC ι₂] [DecidableEq ι₂] [Inhabited ι₂]
                 [Tagged α] [TaggedC α] [Zero α] [Add α] [Inhabited α] [DecidableEq α]
                 : Storage (ι₁ →ₛ ι₂ →ₛ E α) where
  σ       := Var (Map (ι₁ × ι₂) α) × Var (ℕ → α)
  init  n := let out := ("out" : Var (Map (ι₁ × ι₂) α)).fresh n
             let _ : TaggedC (Map (ι₁ × ι₂) α) := ⟨⟨s!"std::map<std::tuple<{tag ι₁}, {tag ι₂}>, {tag α}>"⟩⟩
             let outLoc := ("out_loc" : Var (ℕ → α)).fresh n
             ⟨out.decl (.call Op.mkMap ![]), out, outLoc⟩
  reset   := fun ⟨m, p⟩ => m.store_var (E.call Op.mkMap ![]);;
                           p.store_var (E.call Op.mkNullPtr ![])
  compile := fun n ⟨m, p⟩ =>
               S.step.compile n
                 { push := fun i => (.skip,
                    { push := fun j => (p.store_var (E.call Op.indexMap' ![m.expr, .call Op.mkPair ![i, j]]),
                        MemLoc.mk p 0) : lvl ι₂ (MemLoc α) }) }
  restore := fun ⟨m, _⟩ => {
               σ := Var (Iterator ((ι₁ × ι₂) × α))
               init := fun n => let it := ("it" : Var (Iterator ((ι₁ × ι₂) × α))).fresh n
                                ⟨it.decl (.call Op.mapBegin ![m.expr]), it⟩
               succ := fun p _ => p.store_var (.call Op.iteratorNext ![p.expr])
               skip := fun _ _ => .skip
               valid := fun p => p.expr != .call Op.mapEnd ![m.expr]
               ready := fun _ => 1
               index := fun p => E.call Op.get1 ![.call Op.iteratorKey2 ![p.expr]]
               value := fun p => S.singleton (E.call Op.get2 ![.call Op.iteratorKey2 ![p.expr]])
                                             (E.call Op.iteratorValue ![p.expr])
             }
end

abbrev x  := (0, String)
abbrev j  := (1, ℕ)
abbrev i  := (2, ℕ)
abbrev j' := (3, ℕ)

-- x → j  → i → E R
def orig : x ↠ₛ j ↠ₛ i ↠ₛ E R :=
  (SQL.sss "matrix" : String →ₛ ℕ →ₛ ℕ →ₛ E R)

def rep : j ↠ₐ j' ↠ₛ E R := f
  where f : ℕ →ₐ ℕ →ₛ E R := fun i => S.singleton i 1

-- x → j  → i → j' → E R
def interm := orig * rep
#check interm

def interm2 := (StrS.inner <$> ·) <$> ((StrS.inner <$> ·) <$> ·) <$> interm
#check interm2

def cont := interm2.contract' (Storage.map2)
#check cont

-- x → () → i → j' → E R
-- x →      i → j' → E R

end Etch.Benchmark.Transpose

