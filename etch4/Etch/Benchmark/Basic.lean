import Etch.C
import Etch.Op
import Etch.Compile

instance : TaggedC R := ⟨⟨"double"⟩⟩

-- For C++ maps.
def Op.indexMap {α γ : Type} [Inhabited γ] : Op (ℕ → γ) where
  argTypes := ![α → γ, α]
  spec := fun a => fun | 0 => (a 0) (a 1)
                       | _ => default
  opName := "index_map"
def Op.indexMap2 {α β γ : Type} [Inhabited γ] : Op (ℕ → γ) where
  argTypes := ![α × β → γ, α, β]
  spec := fun a => fun | 0 => (a 0) (a 1, a 2)
                       | _ => default
  opName := "index_map"

namespace Etch.Benchmark

section

variable (I : Type _) [TaggedC I]
         (J : Type _) [TaggedC J]
         (X : Type _) [TaggedC X] [Inhabited X] [Tagged X] [Zero X]
         {Z : Type _}

local instance (α) : ToString (Var α) := ⟨Var.toString⟩
local instance : ToString (DeclType) := ⟨fun | .mk s => s⟩
open TaggedC (tag)

def Arg := (a : Type) × TaggedC a × Var a
def Arg.mk {a} [inst : TaggedC a] (v : Var a) : Arg := ⟨a, ⟨inst, v⟩⟩
def Arg.toC : Arg → String
  | ⟨a, ⟨_, v⟩⟩ => s!"{tag a} {v}"

def compileFun [Compile (Var X) Z] (name : String) (exp : Z) (args : List Arg := []) : String :=
  let val : Var X := "val"
  let decl := (val.decl 0).compile.emit.run
  let argStr := args.map Arg.toC |> String.intercalate ", "
  s!"{tag X} {name}({argStr}) \{\n {decl}\n {go val exp}\n return {val};\n}"

def compileFunMap [Compile (lvl I (MemLoc X)) Z] (name : String) (exp : Z) : String :=
  let T := s!"std::unordered_map<{tag I}, {tag X}>"
  let out : Var (I → X) := "out";
  let out_loc : Var (ℕ → X) := "out_loc";
  let outVal : lvl I (MemLoc X) := {
    push := fun i =>
      (out_loc.store_var (E.call Op.indexMap ![out.expr, i]), ⟨out_loc, 0⟩)
  }
  s!"{T} {name}() \{\n {T} {out};\n {tag X}* {out_loc};\n {go outVal exp}\n return out;\n}"

def compileFunMap2 [Compile (lvl I (lvl J (MemLoc X))) Z] (name : String) (exp : Z) : String :=
  let tpl := s!"std::tuple<{tag I}, {tag J}>"
  let T := s!"std::unordered_map<{tpl}, {tag X}, hash_tuple::hash<{tpl}>>"
  let out : Var (I × J → X) := "out";
  let out_loc : Var (ℕ → X) := "out_loc";
  let outVal : lvl I (lvl J (MemLoc X)) := {
    push := fun i =>
      (.skip, ⟨fun j =>
        (out_loc.store_var (E.call Op.indexMap2 ![out.expr, i, j]),
         ⟨out_loc, 0⟩)⟩) }
  s!"{T} {name}() \{\n {T} {out};\n {tag X}* {out_loc};\n {go outVal exp}\n return out;\n}"
end

section

def compileSqliteCb (name : String) (body : List String) : String :=
  s!"int {name}(void *data, int argc, char **argv, char **azColName) \{\n  {String.join body}\n  return 0;\n}"

end

end Etch.Benchmark
