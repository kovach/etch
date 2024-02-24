import Std.Data.RBMap

open Std (RBMap RBNode RBColor)

-- for reference, RBNode: | node (c : RBColor) (l : RBNode α) (v : α) (r : RBNode α)
inductive Visitor (α : Type)
| done
| r (c : RBColor) (right : RBNode α) (value : α) (k : Visitor α)
| l (c : RBColor) (left : RBNode α)  (value : α) (k : Visitor α)

inductive Direction | up | down
  deriving Inhabited

variable (f : α → α) [Ord ι]

abbrev Tree ι [Ord ι] α := RBNode (ι × α)

-- stackless traversal algorithm from section 2.6: https://www.microsoft.com/en-us/research/uploads/prod/2020/11/perceus-tr-v4.pdf
-- Lean doesn't re-use constructors of different type (?) so this allocates
-- todo: could reuse Std.RBNode.Path, also see zoom
@[inline] partial def tmap (t : Tree ι α) : Tree ι α :=
  let rec @[specialize] go (t : Tree ι α) (k : Visitor (ι × α)) (d : Direction) : Tree ι α :=
  match d with
  | .down =>
    match t with
    | .node c l x r => go l (.r c r x k) .down
    | .nil => go .nil k .up
  | .up =>
    match k with
    | .done => t
    | .r c r (i, x) k => go r (.l c t (i, f x) k) .down
    | .l c l x k => go (.node c l x t) k .up
  go t .done .down

-- hacked a bit so that there is no allocation
inductive Side | r | l | no
  deriving Inhabited
abbrev Tree' ι [Ord ι] (α : Type u) := RBNode (ι × Side × α)
instance : Inhabited (Tree' ι α) := ⟨.nil⟩

@[inline] partial def tmap' (t : Tree' ι α) : Tree' ι α :=
  let rec @[specialize] go (t : Tree' ι α) (k : Tree' ι α) (d : Direction) : Tree' ι α :=
  match d with
  | .down =>
    match t with
    | .node c l (i, _, x) r => go l (.node c r (i, .r, x) k) .down
    | .nil => go .nil k .up
  | .up =>
    match k with
    | .nil => t
    | .node c r (i, .r, x) k => go r (.node c t (i, .l, f x) k) .down
    | .node c l (i, .l, x) k => go (.node c l (i, .no, x) t) k .up
    | .node .. => panic! "no"
  go t .nil .down

def Std.RBNode.look [Inhabited α] (t : RBNode α) : α :=
  match t with
  | .nil => default
  | .node _ _ v _ => v

/-- `upperBound? cut` retrieves the smallest entry greater than or equal to `cut`, if it exists. -/
@[specialize] def Std.RBNode.upperBoundP? (cut : α → Ordering) : RBNode α → Option α → Option α
  | .nil,          lb => lb
  | .node _ a y b, lb =>
    match cut y with
    | .lt => upperBoundP? cut a (some y)
    | .gt => upperBoundP? cut b lb
    | .eq => some y
