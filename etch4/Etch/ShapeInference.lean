import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul

class NatLt (m n : ℕ) where proof : m < n
instance NatLt.zero (n : ℕ) : NatLt 0 n.succ := ⟨Nat.succ_pos _⟩
instance NatLt.succ (m n : ℕ) [h : NatLt m n] : NatLt (m+1) (n+1) :=
⟨Nat.succ_lt_succ h.proof⟩

--instance i1 : NatLt 3 2 := inferInstance -- no
instance i2 : NatLt 1 3 := inferInstance

universe u v

class Atomic (α : Type u)

class Rectangle (f : ℕ → Type _ → Type _) :=
  (map {α β : Type _} (i : ℕ) : (α → β) → f i α → f i β)
  (repl {α : Type _}  (i : ℕ) : α → f i α)
open Rectangle

class Merge (α β : Type _) (γ : outParam $ Type _) :=
  (merge1 : α → γ)
  (merge2 : β → γ)

open Merge

section Instances
variable
{Gen  : ℕ → Type u → Type v}
{Gen' : ℕ → Type u → Type v}
[Rectangle Gen]
[Rectangle Gen']
{α β γ : Type u}

instance Gen.Merge.one {ρ} [Atomic ρ] : Merge ρ ρ ρ := ⟨id, id⟩
instance Gen.Merge.succ {i : ℕ} [Merge α β γ] : Merge (Gen i α) (Gen i β) (Gen i γ) :=
⟨map i (merge1 β), map i (merge2 α)⟩
instance Gen.Merge.scalar_r {i : ℕ} {ρ} [Atomic ρ] [Merge α ρ α] : Merge (Gen i α) ρ (Gen i α) :=
⟨id, repl i ∘ merge2 α⟩
instance Gen.Merge.lt {i j : ℕ} [NatLt i j] [Merge α (Gen' j β) γ] : Merge (Gen i α) (Gen' j β) (Gen i γ) :=
⟨map i (merge1 (Gen' j β)), repl i ∘ merge2 α⟩
instance Gen.Merge.scalar_l {j : ℕ} {ρ} [Atomic ρ] [Merge ρ β β] : Merge ρ (Gen j β) (Gen j β) :=
⟨repl j ∘ merge1 β, id⟩
instance Gen.merge.gt {i j : ℕ} [NatLt j i] [Merge (Gen' i α) β γ] : Merge (Gen' i α) (Gen j β) (Gen j γ) :=
⟨repl j ∘ merge1 β, map j (merge2 (Gen' i α))⟩

def merge {α β γ} [Merge α β γ] : α → β → (γ × γ) := λ a b => (merge1 β a, merge2 α b)

end Instances

instance {α β γ : Type _} [Merge α β γ] [Mul γ] : HMul α β γ := ⟨λ a b => merge1 β a * merge2 α b⟩
instance {α β γ : Type _} [Merge α β γ] [Add γ] : HAdd α β γ := ⟨λ a b => merge1 β a + merge2 α b⟩
--instance {α β γ : Type _} [Merge α β γ] [HAdd' γ γ γ] : HAdd' α β γ := ⟨λ a b => HAdd'.add (merge1 β a) (merge2 α b)⟩

@[reducible] def Ind (_ : ℕ) (ι : Type _) := ι

inductive Str (ι : Type _) (n : ℕ) (α : Type _)
| fun (v : Ind n ι →ₐ α) : Str ι n α
| str (s : Ind n ι →ₛ α) : Str ι n α

instance {n} : Functor (Str n ι) where
  map f
  | .fun v => Str.fun $ f ∘ v
  | .str g => Str.str { g with value := f ∘ g.value }

instance {ι : Type _} : Rectangle (Str ι) where
  map  _ := Functor.map
  repl _ := fun v => .fun $ λ _ => v

instance : Atomic (E α) := ⟨⟩

notation:37 a:36 " × " b:36 " ⟶ " c:36  => Str b a c
infixr:25 " ↠ " => λ (p : ℕ×Type) c => Str (Prod.snd p) (Prod.fst p) c

instance [Guard α] : Guard (n × ι ⟶ α) where guard n b := λ
| .str s => .str {s with valid := λ l => b * s.valid l}
| .fun f => .fun λ x => Guard.guard n b $ f x

variable
{α β γ : Type _}
(n : ℕ)
{ι : Type _} [Tagged ι] [DecidableEq ι]
[LT ι] [DecidableRel (LT.lt : ι → ι → _)] [Zero ι]
[LE ι] [DecidableRel (LE.le : ι → ι → _)]
[Max ι]

-- todo: make local
abbrev i := (0, ℕ)
abbrev j := (1, ℕ)
abbrev k := (2, ℕ)
abbrev l := (3, ℕ)

--example : Merge (Str ℕ 0 (E R)) (Str ℕ 0 (E R)) (Str ℕ 0 $ E R)   := inferInstance
--example : Merge (0×ι ⟶ E R) (1×ℕ ⟶ E R) (Str ι 0 (Str ℕ 1 $ E R)) := inferInstance
--example : Merge (0×ι ⟶ E R) (j ↠ E R)   (Str ι 0 (Str ℕ 1 $ E R)) := inferInstance
--example : Merge (i ↠ E R) (j ↠ E R) (Str ℕ 0 (Str ℕ 1 $ E R))     := inferInstance

--instance G.Ind.hmul {i : ℕ} [has_hmul α β γ] : has_hmul (G (Ind i) α) (G (Ind i) β) (G (Ind i) γ) := ⟨G.mul⟩
--instance [Inhabited α] : Inhabited (Stream n α) := ⟨Stream.view ⟨λ _ => default⟩⟩
--instance [Inhabited ι] [Inhabited α] : Inhabited (G ι α) := ⟨G.empty⟩

-- instance Stream.has_mul {α} {i} [has_mul α] : has_mul (StreamGen' i α) := ⟨StreamGen.mul⟩

instance Str.Mul {γ} {i} [Mul γ] : Mul (i × ι ⟶ γ) := ⟨λ a b =>
match a, b with
| .fun a, .fun b => Str.fun $ a*b
| .str a, .fun b => Str.str $ a*b
| .fun a, .str b => Str.str $ a*b
| .str a, .str b => Str.str $ a*b
⟩

--instance : Inhabited (E R)
--instance : Coe (ι →ₛ α) (n×ι ⟶ α) := ⟨.str⟩
example : Mul (E R) := inferInstance

variable (f : i ↠ E R)
variable
(ν μ : Type _)
(a : i ↠ E R) (b : j ↠ E R)
(q : i ↠ j ↠ E R)
[NatLt i.1 j.1]
[Tagged i.2] [DecidableEq i.2] [LT i.2] [DecidableRel (LT.lt : i.2 → i.2 → _)]
[Tagged j.2] [DecidableEq j.2] [LT j.2] [DecidableRel (LT.lt : j.2 → j.2 → _)]
[Tagged ν] [DecidableEq ν] [LT ν] [DecidableRel (LT.lt : ν → ν → _)]

--#check f * f #check a * b example [HMul α α α] : Mul α := inferInstance example : Mul (i ↠ j ↠ E R) := inferInstance

instance : Coe (ι →ₛ E α) (n × ι ⟶ E α) := ⟨.str⟩
instance : Coe (ι →ₐ E α) (n × ι ⟶ E α) := ⟨.fun⟩
instance [Coe α β] : Coe (ι →ₛ α) (n × ι ⟶ β) := ⟨.str ∘ Functor.map Coe.coe⟩
instance [Coe α β] : Coe (ι →ₐ α) (n × ι ⟶ β) := ⟨.fun ∘ Functor.map Coe.coe⟩

class of_stream (α β : Type _) := (coe : α → β)
instance base.of_stream : of_stream α α := ⟨id⟩

-- TODO!
variable [Add ι] [OfNat ι 1]

def Str.to_g {n} : (n × ι ⟶ α) → (ι →ₛ α) := λ s => match s with
| .fun f => f <$> S.univ "dim" "u_" -- ??
| .str a => a

instance [of_stream α β] : of_stream (n × ι ⟶ α) (ι →ₛ β) := ⟨
λ | .fun f => (of_stream.coe ∘ f) <$> S.univ dim "no"
  | .str a => of_stream.coe <$> a
⟩

def Stream.of [of_stream α β] : α → β := of_stream.coe

class SumIndex (n : ℕ) (α : Type _) (β : outParam $ Type _) := (sum : α → β)
instance sum_eq (n : ℕ) : SumIndex n (n × ι ⟶ α) (Contraction α) := ⟨S.contract ∘ Str.to_g⟩
example : Inhabited $ E R := inferInstance
instance sum_lt (m n : ℕ) [NatLt n m] [SumIndex m α β] : SumIndex m (n × ι ⟶ α) (n × ι ⟶ β) := ⟨Functor.map $ SumIndex.sum m⟩

notation:35 "∑" i:34 ":" v:34 => SumIndex.sum i.1 v
notation:35 "∑" i:34 "," j:34 ":" v:34 => SumIndex.sum i.1 (SumIndex.sum j.1 v)
notation:35 "∑" i:34 "," j:34 "," k:34 ":" v:34 => SumIndex.sum i.1 (SumIndex.sum j.1 (SumIndex.sum k.1 v))
notation:35 "∑" i:34 "," j:34 "," k:34 "," l:34 ":" v:34 => SumIndex.sum i.1 (SumIndex.sum j.1 (SumIndex.sum k.1 (SumIndex.sum l.1 v)))
--macro "∑" i:term ws j:term "," v:term : term => `(SumIndex.sum $i.1 (SumIndex.sum $j.1 $v))
--macro "∑" i:term "," v:term : term => `(SumIndex.sum $i.1 $v)
--macro "∑" i:term+ "," v:term : term => `(SumIndex.sum $(i[0]!).1 $v)

variable (A : ℕ →ₛ ℕ →ₛ E R)
#check SumIndex.sum 0 (a : 0 × ℕ ⟶ E R)
#check ∑ i: (A : i ↠ j ↠ E R)
--#check ∑ i, j: (A : i ↠ j ↠ E R)
--#check ∑ i, j: (A : i ↠ j ↠ E R)
--#check ∑ j, k: (A : i ↠ j ↠ E R) * (B : j ↠ k ↠ E R)

class ApplyScalarFn (α β γ : Type _) (δ : outParam $ Type _) := (map : (E α → E β) → γ → δ)
instance : ApplyScalarFn α β (E α) (E β) := ⟨ (. $ .) ⟩
instance [ApplyScalarFn α β α' β'] : ApplyScalarFn α β (n × ι ⟶ α') (n × ι ⟶ β') := ⟨ λ f x => ApplyScalarFn.map f <$> x ⟩
infixr:10 " <$$> "  => ApplyScalarFn.map

/-
#check Nat.add
inductive St (α : Type) : ℕ → Type
| base : St α 0
| vec (δ) {n} (of : St α n) : St α (n+δ)

-- no
def St.eval {n α} (ctxt : Fin n → Type) : St α n → List Type
| base => []
| vec d x => ctxt ⟨d, Nat.add⟩ :: x.eval _

class Broadcast (α β : Type _) (γ : outParam $ Type _) :=
  broadcast : List ℕ → α → β → γ × γ

instance [Rectangle f] [Broadcast α β γ] : Broadcast (f i α) (f j β) (f

def broadcast (ordering : List ℕ) (a : f i α) (b : g i β)
/- todo
  fix ∑ notation (use ∃ from Heap)
  make broadcast based on a given ordering argument
-/
-/
