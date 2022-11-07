import verification.stream

noncomputable theory
open_locale classical

class Eval (α : Type) (ι : out_param Type) (β : out_param Type) [add_comm_monoid β] :=
(eval : α → (ι →₀ β))

instance Stream.FEval_base {σ ι α : Type} [add_comm_monoid α] : 
  Eval (StreamExec σ ι α) ι α :=
{ eval := (λ s, s.eval) }

instance Stream.FEval_ind {σ ι α ι' α' : Type} [add_comm_monoid α'] [Eval α ι' α'] :
  Eval (StreamExec σ ι α) ι (ι' →₀ α') :=
{ eval := λ s, (Eval.eval <$₂> s).eval }

