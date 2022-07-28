import tactic.ext
import data.set.basic

section
variable (α : Type)

@[ext]
structure TestStruct :=
(x : α)

end

#check set.preimage_image_eq