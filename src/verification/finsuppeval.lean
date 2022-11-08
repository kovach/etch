import verification.stream

noncomputable theory
open_locale classical

class Eval (α : Type*) (ι : out_param Type) (β : out_param Type*) [add_zero_class β] :=
(eval : α → (ι →₀ β))

instance Stream.Eval_base {ι : Type} {α : Type*} [add_zero_class α] : 
  Eval (StreamExec ι α) ι α :=
{ eval := (λ s, s.eval) }

instance Stream.Eval_ind {ι α ι' α' : Type*} [add_zero_class α'] [Eval α ι' α'] :
  Eval (StreamExec ι α) ι (ι' →₀ α') :=
{ eval := λ s, (Eval.eval <$₂> s).eval }

class AddZeroEval (α : Type*) (ι : out_param Type) (β : out_param Type*) [add_zero_class β] 
  extends Eval α ι β, has_add α, has_zero α :=
(hadd : ∀ (x y : α), eval (x + y) = eval x + eval y)
(hzero : eval 0 = 0)

attribute [simp] AddZeroEval.hadd AddZeroEval.hzero
