import Etch.Basic
import Etch.Stream

section LVal

class Rep (σ : Type _) (α : Type _)
class HasReset (σ : Type _) where reset : P
open HasReset

--structure StreamLVal (ι : Type) (σ α : Type _) extends HasReset σ where
structure StreamLVal (ι : Type) (α : Type _) where
  reset : P -- before compile
  take : E ι → α
  commit : E ι → P

infixr:25 " ←ₛ " => StreamLVal

abbrev Interval := MemLoc ℕ
abbrev Ptr := MemLoc
instance : HAdd (Ptr α) (E ℕ) (Ptr α) := ⟨ fun ⟨arr, ind⟩ x ↦ ⟨arr, ind + x⟩ ⟩
def Interval.upper (x : Interval) : MemLoc ℕ := ⟨x.arr, x.ind + 1⟩
def Interval.lower (x : Interval) : MemLoc ℕ := x

variable
  {α : Type _} [Tagged α] [Zero α] [Add α] [HasReset α]
  {ι : Type _} [Tagged ι] [DecidableEq ι]
  [LE ι] [DecidableRel (LE.le : ι → ι → _)] [LT ι] [DecidableRel (LT.lt : ι → ι → _)]

def sparse [Rep (Ptr σ) β] (entry : Ptr σ → β) (size : E ℕ) (indices : Ptr ι) (values : Ptr σ) (x : Interval)
    : StreamLVal ι β where
  reset := x.lower.store size;; x.upper.store size
  -- assumes input is greater than any previous index
  take _ := entry $ values + x.upper.access
  commit ind := (indices + x.upper.access).store ind;; x.upper.incr

-- use cpp vector instead of pre-allocated array
def sparse_vec [Rep (Ptr σ) β] (entry : Ptr σ → β)
  (size : E ℕ)
  (push_is : P × E ι)
  (push_vs : P × E σ)
  (indices : Ptr ι) (values : Ptr σ) (x : Interval)
    : StreamLVal ι β where
  reset := x.lower.store size;; x.upper.store size
  -- assumes input is greater than any previous index
  take _ := entry $ values + x.upper.access
  commit ind := (indices + x.upper.access).store ind;; x.upper.incr

def dense [Add ι] [Mul ι] [Sized ι]
    -- (max_ctr : Var ℕ)
    (entry : Ptr σ → β) (values : Ptr σ)
    : StreamLVal ι β where
  reset := .skip -- .store_var max_ctr 0
  take i := entry $ values + Sized.toNat i
  commit _ := .skip

instance : Rep (Ptr ℕ) (E ℕ) where
#check dense
#check ⟨Var.mk "l1", 0⟩ |> dense "i" (sparse (fun p ↦ p.access) "i_size" ⟨Var.mk "i", 0⟩ ⟨("v" : ArrayVar ℕ), 0 ⟩)

--def sparse [Rep (Ptr σ) β] (indices : ArrayVar ι) (values : ArrayVar σ) (entry : Ptr σ → β) (x : Interval)
--    : StreamLVal ι Interval β where
--  reset := .store_mem x.arr (x.ind + 1) x.access
--  accumulator _ := entry ⟨values, x.upper.access⟩
--  commit ind := .store_mem indices x.upper.access ind;; x.upper.incr
--
----instance : Rep Interval (StreamLVal ι Interval α)
--def dense [Add ι] [Mul ι] [Sized ι] (max_ctr : Var ℕ) (entry : E ℕ → β) (values : Ptr σ)
--    : StreamLVal ι (Var ℕ) β where
--  reset := .store_var max_ctr 0
--  accumulator i := ⟨ values, Sized.toNat i ⟩ --entry (MemLoc.access ⟨values.arr, values.ind * Sized.dimension ι + max⟩)
--  commit ind := .while (max_ctr.expr << Sized.toNat ind) (reset (values + max_ctr.expr);; max_ctr.incr)

#exit

structure ScalarLVal (α : Type _) extends HasReset α where
  --reset : P -- before compile
  accumulator : α
  commit : P

--def dense [Add ι] [Mul ι] [Sized ι] (max_ctr : Var ℕ) (values : Ptr α) : StreamLVal ι (Ptr α) where
--  reset max_ctr := .store_var max_ctr 0
--  accumulator := ⟨values.arr, values.ind * Sized.dimension ι + max⟩
--  commit ind := .while (max_ctr.expr << Sized.toNat ind) (reset (values + max_ctr.expr);; max_ctr.incr)

def value (acc : Var α) : ScalarLVal (E α) where
  reset := .store_var acc 0
  accumulator := acc
  commit := .skip

end LVal

#exit

variable
(ι : Type _) [Tagged ι] [DecidableEq ι]
[LE ι] [DecidableRel (LE.le : ι → ι → _)] [LT ι] [DecidableRel (LT.lt : ι → ι → _)]
{α : Type _} [Tagged α] [Zero α]

abbrev loc := E ℕ
structure il (ι : Type _) := (push' : (loc → P) → E ι → P × loc)
structure vl  (α : Type _) := (value  : loc → α) (init : loc → P)
structure lvl (ι α : Type _) := (push : E ι → P × α) -- (declare : P) (σ : Type)

instance : Functor (lvl ι) := { map := λ f l => { push := Prod.map id f ∘ l.push } }

def lvl.of {ι α} (i : il ι) (v : vl α) : lvl ι α := v.value <$> ⟨i.push' v.init⟩

variable {ι}

infixl:20 "||" => Add.add

def sparse_il' (ind_array : Var (ℕ → ι)) (lower upper : MemLoc ℕ) : il ι :=
  let loc   := upper.deref - 1
  let current := ind_array.access loc
  { push' := λ init i =>
      let prog := P.if1 (lower.deref == upper.deref || i != current)
                    (upper.incr_array;; init loc);;
                    P.store_mem ind_array loc i
      (prog, loc) }

def sparse_il (ind_array : Var (ℕ → ι)) (bounds : MemLoc ℕ) : il ι :=
  let array := bounds.arr
  let ind   := bounds.ind
  let lower := array.access ind
  let upper := array.access (ind + 1)
  let loc   := upper - 1
  let current := ind_array.access loc
  { push' := λ init i =>
      let prog := P.if1 (lower == upper || i != current)
                    (array.incr_array (ind + 1);; init loc);;
                    P.store_mem ind_array loc i
      (prog, loc) }

def dense_il [Add ι] [Mul ι] [Sized ι] (counter : Var ℕ) (base : E ℕ) : il ι :=
  { push' := λ init i =>
      let l (i : E ℕ)  : loc := base * Sized.dimension ι + i
      let prog : P := P.while (counter.expr <= Sized.toNat i) (init (l counter);; counter.incr)
      (prog, l (Sized.toNat i)) }

def interval_vl (array : ArrayVar ℕ) : vl (MemLoc ℕ) :=
  { value := λ loc =>  ⟨array, loc⟩,
    init  := λ loc =>  .store_mem array (loc + 1) (.access array loc) }
def dense_vl  (array : ArrayVar α) : vl (MemLoc α) :=
  { value := λ loc => ⟨array, loc⟩,
    init  := λ loc => .store_mem array loc 0 }
def implicit_vl : vl (E ℕ) := { value := id, init := λ _ => P.skip }

-- a function of type α → lvl ι β is essentially a level format
-- this combinator combines an il with a vl to form a lvl.
-- the extra parameter α is used to thread the primary argument to a level through ⊚.
--   see dcsr/csr_mat/dense below
def with_values : (α → il ι) → vl β → (α → lvl ι β) := λ i v e => lvl.of (i e) v
