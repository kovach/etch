import algebra
import algebra.group
import algebra.group.defs
import tactic
import logic.relation
set_option pp.proofs true

universes u v
variables (α β : Type*)

-- todo, already exists as:
#check function.End
#check function.End.smul_def
instance comp_monoid (ν : Type*) : monoid (ν → ν) :=
{ mul := λ a b, a ∘ b , mul_assoc := λ a b c, rfl
, one := λ a, a , one_mul := λ a, rfl , mul_one := λ a, rfl }

instance endo_action : mul_action (α → α) α :=
{ smul := λ f a, f a
, one_smul := λ a, begin unfold has_one.one mul_one_class.one monoid.one, end
, mul_smul := λ f g x , begin unfold has_mul.mul mul_one_class.mul monoid.mul function.comp, end }

instance fish_monoid (m : _) (ν : Type) [monad m] [is_lawful_monad m] : monoid (ν → m ν) :=
{ mul := λ a b, (a >=> b)
, mul_assoc := λ a b c, begin unfold has_mul.mul, rw fish_assoc, end --needed for rev version?
, one := pure
, one_mul := fish_pipe
, mul_one := fish_pure
}
