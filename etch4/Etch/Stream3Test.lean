import Etch.Stream3
import Etch.Stream3Deriving

namespace Etch.Stream.Test

inductive A
| attr1 | attr2 | attr3
deriving Repr, DecidableEq
def A.toTag : A → String
| attr1 => "attr1"
| attr2 => "attr2"
| attr3 => "attr3"
instance A.represented : Represented A := ⟨A.toTag⟩
open A (attr1 attr2 attr3)

set_option trace.Elab.Deriving.attr_order_total true in
deriving instance AttrOrderTotal with { order := [.attr1, .attr2, .attr3] } for A

inductive A'
| attr' : Fin 10 → A'
deriving Repr, DecidableEq,
AttrOrderTotal with { order := [.attr' 0, .attr' 1, .attr' 2, .attr' 3, .attr' 4,
                                .attr' 5, .attr' 6, .attr' 7, .attr' 8, .attr' 9] }
def A'.toTag : A' → String
| attr' _ => "attr1"
instance A'.represented : Represented A' := ⟨A'.toTag⟩
open A' (attr')

variable (i j k : A)
#check (contract' i $ default [i, j])
#check let a  : [j] →ₛ i := (contract' i (default [i, j])); a

variable
(s₁ : [attr1] →ₛ attr3)
(s₂ : [attr2] →ₛ attr3)
(srev : [attr2, attr1] →ₛ attr3)

section v1
def attr1Sublist : [attr1].SublistT A.order.val := .check' (by decide)
def attr2Sublist : [attr2].SublistT A.order.val := .check' (by decide)

#eval (mergeAttr attr1Sublist attr2Sublist).fst.val

#check (s₂.mulMerge attr2Sublist attr1Sublist s₁) -- `: (mergeAttr attr2Sublist attr1Sublist).fst.val →ₛ attr3`
#check (s₂.mulMerge attr2Sublist attr1Sublist s₁ : [attr1, attr2] →ₛ attr3)

#check (s₂.mulMerge (.check' (by decide)) (.check' (by decide)) s₁) -- works
-- Doesn't work ☹
-- #check (s₂.mulMerge (.check' (by decide)) (.check' (by decide)) s₁ : [attr1, attr2] →ₛ attr3)

end v1

section v2
#eval merge [attr1] [attr2]
#check s₂.mul' s₁ -- `: [attr1, attr2] →ₛ attr3`

-- #check srev.mul'' s₁
-- failed to synthesize instance
--   `AttrMerge' A.order.val [attr2, attr1] [attr1] ?m.287939`

#eval decide (attr' 0 < attr' 1)
#eval decide (attr' 9 < attr' 1)
#eval merge [attr' 0, attr' 9] [attr' 8]
variable
(s₁ : [attr' 0, attr' 3, attr' 4, attr' 5, attr' 6, attr' 7, attr' 9] →ₛ attr' 4)
(s₂ : [attr' 0, attr' 1, attr' 2, attr' 3, attr' 8] →ₛ attr' 4)
-- Notice how fast this is.
#check s₂.mul' s₁ -- `: [attr1, attr2] →ₛ attr3`

end v2

end Etch.Stream.Test
