import data.finsupp.pointwise
import verification.semantics.stream
import verification.semantics.stream_props

noncomputable theory
open_locale classical

class Eval (α : Type*) (ι : out_param Type) (β : out_param Type*) [has_zero β] :=
(eval : α → (ι →₀ β))

instance Stream.Eval_base {ι : Type} {α : Type*} [add_zero_class α] : 
  Eval (StreamExec ι α) ι α :=
{ eval := λ s, s.eval }

instance SimpleStream.Eval_base {ι : Type} {α : Type*} [linear_order ι] [add_zero_class α] : 
  Eval (SimpleStream ι α) ι α :=
{ eval := λ s, Eval.eval (↑s : StreamExec ι α) }

instance Stream.Eval_ind {ι α ι' α' : Type*} [add_zero_class α'] [Eval α ι' α'] :
  Eval (StreamExec ι α) ι (ι' →₀ α') :=
{ eval := λ s, (Eval.eval <$₂> s).eval }

instance SimpleStream.Eval_ind {ι α ι' α' : Type*} [linear_order ι] [add_zero_class α'] [Eval α ι' α'] :
  Eval (SimpleStream ι α) ι (ι' →₀ α') :=
{ eval := λ s, Eval.eval (↑s : StreamExec ι α) }

class AddZeroEval (α : Type*) (ι : out_param Type) (β : out_param Type*) [add_zero_class β] 
  extends Eval α ι β, has_add α, has_zero α :=
(hadd : ∀ (x y : α), eval (x + y) = eval x + eval y)
(hzero : eval 0 = 0)

class MulEval (α : Type*) (ι : out_param Type) (β : out_param Type*) [non_unital_non_assoc_semiring β]
  extends Eval α ι β, has_mul α :=
(hmul : ∀ (x y : α), eval (x * y) = eval x * eval y)

attribute [simp] AddZeroEval.hadd AddZeroEval.hzero
  MulEval.hmul

@[simp] lemma Eval.contract {ι ι' : Type} {α α' : Type*} [add_comm_monoid α'] [Eval α ι' α']
  (s : StreamExec ι α) :
  Eval.eval (contract_stream s) () = (Eval.eval s).sum_range :=
by simp [Eval.eval, contract_stream, StreamExec.bimap_bimap, ← contract_stream_spec_apply]

@[simp] lemma Eval.contract' {ι ι' : Type} {α α' : Type*} [linear_order ι] [add_comm_monoid α'] [Eval α ι' α']
  (s : SimpleStream ι α) :
  Eval.eval s.contract () = (Eval.eval s).sum_range :=
Eval.contract _