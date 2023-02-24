import Etch.Basic
import Etch.Stream

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
