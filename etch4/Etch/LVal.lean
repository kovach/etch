import Etch.Basic
import Etch.ExtStream

variable
(ι : Type _) [Tagged ι] [DecidableEq ι]
[LE ι] [DecidableRel (LE.le : ι → ι → _)]
[LT ι] [DecidableRel (LT.lt : ι → ι → _)]
{α : Type _} [Tagged α] [OfNat α (nat_lit 0)]

abbrev loc := E ℕ
structure il (ι : Type _) := (push' : (loc → P) → E ι → P × loc)
structure vl  (α : Type _) := (value  : loc → α) (init : loc → P)
structure lvl (ι α : Type _) := (push : E ι → P × α)

instance : Functor (lvl ι) := { map := λ f l => { push := Prod.map id f ∘ l.push } }

def lvl.of {ι α} (i : il ι) (v : vl α) : lvl ι α := v.value <$> ⟨i.push' v.init⟩
--⟨λ e => let (p, l) := i.push' e v.init; (p, v.value l)⟩

variable {ι}

infixl:20 "||" => Add.add

structure MemLoc (α : Type) where (arr : Var α) (ind : E ℕ)

def MemLoc.access (m : MemLoc α) : E α := m.arr.access m.ind

def sparse_index (indices : Var ι) (bounds : MemLoc ℕ) : il ι :=
let array := bounds.arr
let ind   := bounds.ind
let lower := array.access bounds.2
let upper := array.access $ bounds.2 + 1
let loc := upper-1
let current := indices.access loc
{ push' := λ init i =>
    let prog := P.if1 (lower == upper || i != current)
                      (array.incr_array (ind+1);; init loc);;
                P.store_mem indices loc i
    (prog, loc) }

def dense_index (dim : E ℕ) (counter : Var ℕ) (base : E ℕ) : il ℕ :=
{ push' := λ init i =>
    let l i  : loc := base * dim + i
    let prog : P := P.while (counter.expr <= i) (init (l counter);; counter.incr)
    (prog, l i) }

def interval_vl (array : Var ℕ) : vl (MemLoc ℕ) :=
{ value  := λ loc =>  ⟨array, loc⟩,
  init := λ loc =>  .store_mem array (loc + 1) (.access array loc) }
def dense_vl  (array : Var α) : vl (MemLoc α) :=
{ value := λ loc => ⟨array, loc⟩,
  init := λ loc => .store_mem array loc 0 }
def implicit_vl : vl (E ℕ) := { value := id, init := λ _ => P.skip }

-- this combinator combines an il with a vl to form a lvl.
-- the extra parameter α is used to thread the primary argument to a level through ⊚.
--   see dcsr/csr_mat/dense below
--def with_values : (α → il ι) → vl β → α → lvl ι β := λ i v e => { __ := v, __ := i e }
def with_values : (α → il ι) → vl β → α → lvl ι β := λ i v e => lvl.of (i e) v

def dense_mat (d₁ d₂ : E ℕ) : lvl ℕ (lvl ℕ (MemLoc ℕ)) := (0 : E ℕ) &
  (with_values (dense_index d₁ "i1") implicit_vl) ⊚
  (with_values (dense_index d₂ "i2") $ dense_vl "values")
def cube_lvl (d₁ d₂ d₃ : E ℕ):= 0 &
  (with_values (dense_index d₁ "i1") implicit_vl) ⊚
  (with_values (dense_index d₂ "i2") implicit_vl) ⊚
  (with_values (dense_index d₃ "i3") $ dense_vl "values")
def sparse_vec : lvl ℕ (MemLoc α) := ⟨("size" : Var ℕ), (0 : E ℕ)⟩ &
  (with_values (sparse_index ("A1_crd" : Var ℕ)) (dense_vl "A_vals"))

def dcsr (l : String) : lvl ℕ (lvl ℕ (MemLoc α)) :=
  (interval_vl $ l ++ "1_pos").value 0 &
  (with_values (sparse_index (l ++ "1_crd" : Var ℕ)) (interval_vl $ l ++ "2_pos")) ⊚
  (with_values (sparse_index (l ++ "2_crd" : Var ℕ)) (dense_vl $ l ++ "_vals"))

def csr_mat (l dim i : String) : lvl ℕ (lvl ℕ (MemLoc α)) := 0 &
  (with_values (dense_index dim i) (interval_vl $ l ++ "2_pos")) ⊚
  (with_values (sparse_index $ l ++ "2_crd") (dense_vl $ l ++ "_vals"))

--todo
def trieType : ℕ → Type _
| 0 => lvl ℕ (MemLoc α)
| n+1 => lvl ℕ (trieType n)
