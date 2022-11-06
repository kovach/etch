namespace C
abbrev Var := String
abbrev M := ReaderT String (StateM String)
abbrev Op := ReaderT String (StateM String) Unit
def Op.run (p : Op) : String := StateT.run (ReaderT.run p "") "" |>.snd
end C

open C

def emitString [ToString α] (a : α) : M Unit := modify λ s => s ++ toString a

namespace String
def emit (a : String) : M Unit := _root_.modify $ λ s => s ++ a
def emitStart (a : String) : M Unit := λ indent => _root_.modify $ λ s => s ++ indent ++ a
end String

def emitStart (a : String) : M Unit := λ indent => _root_.modify $ λ s => s ++ indent ++ a

def emitLine [ToString α] (a : α) : M Unit :=
  emitString a *> emitString "\n"

def emitLines [ToString α] (a : Array α) : Op :=
  a.forM emitLine

inductive Expr
| lit (n : Int)
| litf (f : Float)
| var (v : Var)
| index (base : Expr) (indices : List Expr)
| star (addr : Expr)
| mul (exprs : List Expr)
| binOp : String → Expr → Expr → Expr
| ternary : Expr → Expr → Expr → Expr
| extern : String → Expr
| call : String → List Expr → Expr
| true
| false
deriving Repr
-- todo? inductive LHS | var (v : Var) | index (base : LHS) (indices : List Expr) deriving Repr
inductive DeclType | Int | Float deriving Repr
inductive Stmt
| forIn : (n : Nat) → Var → Stmt → Stmt
| while : Expr → Stmt → Stmt
| cond  : Expr → Stmt → Stmt
| conde : Expr → Stmt → Stmt → Stmt
| accum : Expr → Expr → Stmt
| store : Expr → Expr → Stmt
| decl : DeclType → Var → Expr → Stmt
| seq : Stmt → Stmt → Stmt
| noop : Stmt
| extern : String → Stmt
| block : Stmt → Stmt
| break_
deriving Repr

instance : OfNat Expr n where
  ofNat := Expr.lit n

def Stmt.sequence : List Stmt → Stmt
| [] => Stmt.noop
| x :: xs => Stmt.seq x $ sequence xs

def String.wrap (s : String) : String := "(" ++ s ++ ")"

namespace Expr

def wrap (s : String) : String := String.wrap s
partial def toString : Expr → String
  | lit n => ToString.toString n
  | litf n => ToString.toString n
  | var v => v
  | index n indices => toString n ++ (indices.map λ i => "[" ++ toString i ++ "]").foldl String.append ""
  | star addr => "*" ++ addr.toString
  | mul es => wrap $ String.join (List.intersperse "*" (es.map toString))
  | binOp op a b => wrap $ a.toString ++ op ++ b.toString
  | ternary cond a b => wrap $ cond.toString.wrap ++ "?" ++ a.toString.wrap ++ ":" ++ b.toString.wrap
  | extern s => s
  | call f args => let as := String.join (List.intersperse "," (args.map toString)); s!"{f}({as})"
  | true => "true"
  | false => "false"

instance : ToString Expr where
  toString := Expr.toString

def emit : Expr → Op := String.emit ∘ toString

end Expr

def DeclType.emit
| Int => "int".emit
| Float => "float".emit

namespace Stmt

def semicolon := emitLine ";"

def lf := "".emitStart
def indentUnit : String := "  "
def indent : M a → M a := ReaderT.adapt (. ++ indentUnit)
def emit : Stmt → Op
| extern s => emitString s
| accum lhs value => do lf; lhs.emit; " += ".emit; value.emit; emitLine ";"
| store lhs value => do lf; lhs.emit; " = ".emit; value.emit; emitLine ";"
| forIn bound var body => do
  lf; emitString s!"for (int {var} = 0; {var} < {bound}; {var}++) \{\n"
  indent body.emit
  lf; emitLine "}"
| Stmt.while condition body => do lf; "while (".emit ; condition.emit; ") {\n".emit; indent body.emit; lf; emitLine "}"
| cond condition a => do lf; "if (".emit; condition.emit; ") {\n".emit; indent a.emit; lf; emitLine "}"
| conde condition thenb elseb => do lf; "if (".emit; condition.emit; ") {\n".emit; indent thenb.emit; lf; "} else {\n".emit; indent elseb.emit; lf; emitLine "}"
| decl type name value => do lf; type.emit; " ".emit; name.emit; emitString " = "; value.emit; semicolon
| seq p1 p2 => do emit p1; emit p2
| block s => do lf; emitLine "{"; s.emit; lf; emitLine "}"
| break_ => do lf; emitLine "break;"
| noop => pure ()


def emitIncludes : Op := do
  "#include <stdio.h>\n".emit
  "#include <stdint.h>\n".emit

def emitPrintf : Op := emitLine ""

def emitProgram (body : Stmt) : Op := do
  emitIncludes
  emitLine "int main() {"
  body.emit
  emitPrintf
  emitLine "return 0;"
  emitLine "}"

def compile (p : Stmt) : String := p.emit |>.run
def compileWithWrapper (p : Stmt) : String := p.emitProgram |>.run
end Stmt
