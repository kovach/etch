import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul

class NatLt (m n : ℕ) where proof : m < n
instance NatLt.one (n : ℕ) : NatLt 0 n.succ := ⟨Nat.succ_pos _⟩
instance NatLt.trans (m n : ℕ) [h : NatLt m n] : NatLt (m+1) (n+1) :=
⟨Nat.succ_lt_succ h.proof⟩

-- example : NatLt 3 2 := inferInstance -- no
example : NatLt 1 3 := inferInstance

universe u v

class Atomic (α : Type u)

@[reducible] def Ind (_ : ℕ) (ι : Type _) := ι

class IndexedFunctor (f : ℕ → Type u → Type v) : Type (max (u+1) v) where
  imap : {i : ℕ} → {α β : Type u} → (α → β) → f i α → f i β
  imapConst : {i : ℕ} → {α β : Type u} → α → f i β → f i α := imap ∘ (Function.const _)

instance [IndexedFunctor F] : Functor (F n) where
  map := IndexedFunctor.imap
  mapConst := IndexedFunctor.imapConst

inductive StrF (ι : Type _) (n : ℕ) (α : Type _)
| fun (v : Ind n ι →ₐ α) : StrF ι n α

instance : IndexedFunctor (StrF ι) where
  imap | f, .fun v => .fun (f ∘ v)

inductive StrS (ι : Type _) (n : ℕ) (α : Type _)
| str (s : Ind n ι →ₛ α) : StrS ι n α

instance : IndexedFunctor (StrS ι) where
  imap | f, .str g => .str { g with value := f ∘ g.value }

section HMul
variable {ι : Type} [Tagged ι] [DecidableEq ι] [Max ι]
variable [IndexedFunctor F] [IndexedFunctor F'] [Atomic ρ]

instance instHMul.Merge.succ_ss [HMul α β γ] : HMul (StrS ι i α) (StrS ι i β) (StrS ι i γ) :=
⟨fun | .str s₁, .str s₂ => .str (s₁ * s₂)⟩
instance instHMul.Merge.succ_sf [HMul α β γ] : HMul (StrS ι i α) (StrF ι i β) (StrS ι i γ) :=
⟨fun | .str s₁, .fun s₂ => .str (s₁ * s₂)⟩
instance instHMul.Merge.succ_fs [HMul α β γ] : HMul (StrF ι i α) (StrS ι i β) (StrS ι i γ) :=
⟨fun | .fun s₁, .str s₂ => .str (s₁ * s₂)⟩
instance instHMul.Merge.succ_ff [HMul α β γ] : HMul (StrF ι i α) (StrF ι i β) (StrF ι i γ) :=
⟨fun | .fun s₁, .fun s₂ => .fun (s₁ * s₂)⟩

instance instHMul.Merge.scalar_r [HMul α ρ α] : HMul (F i α) ρ (F i α) :=
⟨fun s₁ k => (· * k) <$> s₁⟩
instance instHMul.Merge.lt [NatLt i j] [HMul α (F' j β) γ] : HMul (F i α) (F' j β) (F i γ) :=
⟨fun s₁ k => (· * k) <$> s₁⟩
instance instHMul.Merge.scalar_l [HMul ρ α α] : HMul ρ (F i α) (F i α) :=
⟨fun k s₂ => (k * ·) <$> s₂⟩
instance instHMul.Merge.gt [NatLt j i] [HMul (F' i α) β γ] : HMul (F' i α) (F j β) (F j γ) :=
⟨fun k s₂ => (k * ·) <$> s₂⟩

instance [Mul α] : Mul (StrS ι i α) := ⟨HMul.hMul⟩ 
instance [Mul α] : Mul (StrF ι i α) := ⟨HMul.hMul⟩ 

-- Special: bool * S
instance instHMul.Merge.scalar_r_bool : HMul (StrS ι i α) (E Bool) (StrS ι i α) :=
⟨fun | .str s₁, k => .str (Guard.guard k s₁)⟩
instance instHMul.Merge.scalar_l_bool : HMul (E Bool) (StrS ι i α) (StrS ι i α) :=
⟨fun | k, .str s₂ => .str (Guard.guard k s₂)⟩
instance instHMul.Merge.succ_sf_bool : HMul (StrS ι i α) (StrF ι i (E Bool)) (StrS ι i α) :=
⟨fun | .str s₁, .fun s₂ => .str (s₁ * s₂)⟩
instance instHMul.Merge.succ_fs_bool : HMul (StrF ι i (E Bool)) (StrS ι i β) (StrS ι i β) :=
⟨fun | .fun s₁, .str s₂ => .str (s₁ * s₂)⟩
end HMul

section HAdd
variable {α β γ ι : Type}
  [Tagged ι] [TaggedC ι] [DecidableEq ι]
  [LT ι] [LE ι] [DecidableRel (LT.lt : ι → ι → Prop)]
  [DecidableRel (LE.le : ι → ι → _)]
  {i : ℕ}
  [Guard α] [Guard β]
variable [IndexedFunctor F] [IndexedFunctor F'] [Atomic ρ]

instance instHAdd.Merge.succ_ss [HAdd α β γ] : HAdd (StrS ι i α) (StrS ι i β) (StrS ι i γ) :=
⟨fun | .str s₁, .str s₂ => .str (s₁ + s₂)⟩
instance instHAdd.Merge.succ_sf [HAdd α β γ] : HAdd (StrS ι i α) (StrF ι i β) (StrS ι i γ) :=
⟨fun | .str s₁, .fun s₂ => .str (s₁ + s₂)⟩
instance instHAdd.Merge.succ_fs [HAdd α β γ] : HAdd (StrF ι i α) (StrS ι i β) (StrS ι i γ) :=
⟨fun | .fun s₁, .str s₂ => .str (s₁ + s₂)⟩
instance instHAdd.Merge.succ_ff [HAdd α β γ] : HAdd (StrF ι i α) (StrF ι i β) (StrF ι i γ) :=
⟨fun | .fun s₁, .fun s₂ => .fun (s₁ + s₂)⟩

instance instHAdd.Merge.scalar_r [HAdd α ρ α] : HAdd (F i α) ρ (F i α) :=
⟨fun s₁ k => (· + k) <$> s₁⟩
instance instHAdd.Merge.lt [NatLt i j] [HAdd α (F' j β) γ] : HAdd (F i α) (F' j β) (F i γ) :=
⟨fun s₁ k => (· + k) <$> s₁⟩
instance instHAdd.Merge.scalar_l [HAdd ρ α α] : HAdd ρ (F i α) (F i α) :=
⟨fun k s₂ => (k + ·) <$> s₂⟩
instance instHAdd.Merge.gt [NatLt j i] [HAdd (F i α) β γ] : HAdd (F i α) (F' j β) (F' j γ) :=
⟨fun k s₂ => (k + ·) <$> s₂⟩

instance [Add α] : Add (StrS ι i α) := ⟨HAdd.hAdd⟩ 
instance [Add α] : Add (StrF ι i α) := ⟨HAdd.hAdd⟩ 
end HAdd

instance : Atomic (E α) := ⟨⟩

notation:37 a:36 " × " b:36 " ⟶ₐ " c:36  => StrF b a c
infixr:25 " ↠ₐ " => λ (p : ℕ×Type) c => StrF (Prod.snd p) (Prod.fst p) c
notation:37 a:36 " × " b:36 " ⟶ₛ " c:36  => StrS b a c
infixr:25 " ↠ₛ " => λ (p : ℕ×Type) c => StrS (Prod.snd p) (Prod.fst p) c

instance [Guard α] : Guard (n × ι ⟶ₛ α) where
  guard b := fun | .str f => .str (Guard.guard b f)

instance [Tagged α] [Zero α] : Guard (n × ι ⟶ₐ E α) where
  guard b := fun | .fun f => .fun (Guard.guard b f)

variable
{α β γ : Type _}
(n : ℕ)
{ι : Type _} [Tagged ι] [TaggedC ι] [DecidableEq ι]
[LT ι] [DecidableRel (LT.lt : ι → ι → _)] [Zero ι]
[LE ι] [DecidableRel (LE.le : ι → ι → _)]
[Max ι]

instance StrS.Mul [Mul γ] : Mul (i × ι ⟶ₛ γ) := ⟨HMul.hMul⟩
instance StrF.Mul [Mul γ] : Mul (i × ι ⟶ₐ γ) := ⟨HMul.hMul⟩

instance : Coe (ι →ₛ α) (n × ι ⟶ₛ α) := ⟨.str⟩
instance : Coe (ι →ₐ α) (n × ι ⟶ₐ α) := ⟨.fun⟩
instance [Coe α β] : Coe (ι →ₛ α) (n × ι ⟶ₛ β) := ⟨.str ∘ Functor.map Coe.coe⟩
instance [Coe α β] : Coe (ι →ₐ α) (n × ι ⟶ₐ β) := ⟨.fun ∘ Functor.map Coe.coe⟩

class of_stream (α β : Type _) := (coe : α → β)
instance base.of_stream : of_stream α α := ⟨id⟩

def Stream.of [of_stream α β] : α → β := of_stream.coe

class SumIndex (n : ℕ) (α : Type _) (β : outParam $ Type _) := (sum : α → β)
instance sum_eq (n : ℕ) : SumIndex n (n × ι ⟶ₛ α) (Contraction α) := ⟨fun | .str s => S.contract s⟩
instance sum_lt_f [IndexedFunctor F] (m n : ℕ) [NatLt n m] [SumIndex m α β] : SumIndex m (F n α) (F n β) := ⟨IndexedFunctor.imap $ SumIndex.sum m⟩
instance sum_lt_s [IndexedFunctor F] (m n : ℕ) [NatLt n m] [SumIndex m α β] : SumIndex m (F n α) (F n β) := ⟨IndexedFunctor.imap $ SumIndex.sum m⟩

notation:35 "∑" i:34 ":" v:34 => SumIndex.sum i.1 v
notation:35 "∑" i:34 "," j:34 ":" v:34 => SumIndex.sum i.1 (SumIndex.sum j.1 v)
notation:35 "∑" i:34 "," j:34 "," k:34 ":" v:34 => SumIndex.sum i.1 (SumIndex.sum j.1 (SumIndex.sum k.1 v))
notation:35 "∑" i:34 "," j:34 "," k:34 "," l:34 ":" v:34 => SumIndex.sum i.1 (SumIndex.sum j.1 (SumIndex.sum k.1 (SumIndex.sum l.1 v)))
--macro "∑" i:term ws j:term "," v:term : term => `(SumIndex.sum $i.1 (SumIndex.sum $j.1 $v))
--macro "∑" i:term "," v:term : term => `(SumIndex.sum $i.1 $v)
--macro "∑" i:term+ "," v:term : term => `(SumIndex.sum $(i[0]!).1 $v)

class ApplyScalarFn (α β γ : Type _) (δ : outParam $ Type _) := (map : (E α → E β) → γ → δ)
instance : ApplyScalarFn α β (E α) (E β) := ⟨ (. $ .) ⟩
instance [IndexedFunctor F] [ApplyScalarFn α β α' β'] : ApplyScalarFn α β (F n α') (F n β') := ⟨ λ f x => ApplyScalarFn.map f <$> x ⟩
infixr:10 " <$$> "  => ApplyScalarFn.map
