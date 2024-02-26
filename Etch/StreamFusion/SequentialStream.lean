import Mathlib.Data.Prod.Lex
import Mathlib.Data.String.Basic
import Init.Data.Array.Basic
import Std.Data.RBMap
import Std.Data.HashMap

import Etch.StreamFusion.Basic

open Std (RBMap HashMap)

namespace Etch.Verification

structure SequentialStream (ι : Type) (α : Type u) where
  σ : Type
  q : σ
  valid : σ → Bool
  index : {x // valid x} → ι
  next  : {x // valid x} → σ
  ready : {x // valid x} → Bool
  value : {x // ready x} → α

infixr:25 " →ₛ! " => SequentialStream

namespace SequentialStream

class ToStream (α : Type u) (β : outParam $ Type v) where
  stream : α → β

--instance instBase [Scalar α] [Add α] : OfStream α α where
--  eval := Add.add

@[inline] partial def fold (f : β → ι → α → β) (s : SequentialStream ι α) (acc : β) : β :=
  let rec @[specialize] go f
      (valid : s.σ → Bool) (ready : (x : s.σ) → valid x → Bool)
      (index : (x : s.σ) → valid x → ι) (value : (x : s.σ) → (h : valid x) → ready x h → α)
      (next : {x // valid x} → s.σ)
      --(next : (x : s.σ) → valid x → Bool → s.σ)
      (acc : β) (q : s.σ) :=
    if hv : valid q then
      let i := index q hv
      let hr := ready q hv
      let acc' := if hr : hr then f acc i (value q hv hr) else acc
      let q' := next ⟨q, hv⟩
      go f valid ready index value next acc' q'
    else acc
  go f s.valid (fun q h => s.ready ⟨q,h⟩) (fun q h => s.index ⟨q,h⟩) (fun q v r => s.value ⟨⟨q,v⟩,r⟩) s.next
     acc s.q

@[macro_inline]
def map (f : α → β) (s : ι →ₛ! α) : ι →ₛ! β := {
  s with value := f ∘ s.value
}

@[simps, macro_inline]
def contract (s : ι →ₛ! α) : Unit →ₛ! α := { s with index := default }

end SequentialStream

end Etch.Verification
