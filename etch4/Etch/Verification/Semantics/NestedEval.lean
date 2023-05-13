import Etch.Verification.Semantics.SkipStream
import Etch.Verification.Semantics.Zero
import Etch.Verification.Semantics.Add
import Etch.Verification.Semantics.Mul
import Etch.Verification.Semantics.Contract
import Etch.Verification.Semantics.Replicate

/-!
# Nested stream evaluation

In this file, we define how nested streams are evaluated.
To do this, we use Lean's typeclass system to infer an evaluation
function depending on the shape of the nested stream.

## Main definitions
  - `BoundedStream`: A stream bundled with an initial state and a proof that the stream is bounded
  - `LawfulStream`: A stream bundled with a proof that the stream is strictly lawful
  - `LawfulEval`: An evaluation function that preserves addition, multiplication, and zero

## Main results 
  - `LawfulEval.ind`: Shows that if `α` lawfully evaluates to `β`,
      then (lawful) streams of type `ι ⟶ₛ α` lawfully evaluate to
      finitely supported functions `ι →₀ β`. In the base case, `α = β`,
      and in the inductive case, `α` is itself another stream type which
      lawfully evaluates to `β`. This, together with `LawfulStream.eval_contract`
      and `LawfulStream.eval_replicate`, corresponds to theorem 6.1 in the paper.
-/

set_option linter.uppercaseLean3 false

namespace Etch.Verification

noncomputable section

open Classical

@[ext]
structure BoundedStream (ι : Type) [LinearOrder ι] (α : Type _) where
  toStream : Stream ι α -- not `extends` to make `@[ext]` not recurse into Stream
  init : toStream.σ
  bdd : IsBounded toStream
#align BoundedStream Etch.Verification.BoundedStream

-- mathport name: «expr ⟶b »
infixr:50 " ⟶b " => BoundedStream

-- mathport name: «expr↟ »
local notation "↟" s => BoundedStream.toStream s

attribute [instance] BoundedStream.bdd

variable {ι : Type} [LinearOrder ι] {α β γ : Type _}

@[simps toStream init]
def BoundedStream.map (f : α → β) (s : BoundedStream ι α) : BoundedStream ι β :=
  ⟨(↟s).map f, s.init, by simp; infer_instance⟩
#align BoundedStream.map Etch.Verification.BoundedStream.map

@[simp]
theorem BoundedStream.map_id (s : BoundedStream ι α) : s.map id = s := rfl
#align BoundedStream.map_id Etch.Verification.BoundedStream.map_id

theorem BoundedStream.map_map (g : α → β) (f : β → γ) (s : BoundedStream ι α) :
    (s.map g).map f = s.map (f ∘ g) := by ext : 1 <;> simp [Stream.map_map]
#align BoundedStream.map_map Etch.Verification.BoundedStream.map_map

class Eval (α : Type _) (β : outParam (Type _)) [AddZeroClass β] where
  eval : α → β
#align Eval Etch.Verification.Eval

open Eval

instance Eval.base {α : Type _} [AddZeroClass α] : Eval α α where eval := id
#align Eval.base Etch.Verification.Eval.base

instance Eval.ind (ι : Type) [LinearOrder ι] (α β : Type _) [AddZeroClass β] [Eval α β] :
    Eval (ι ⟶b α) (ι →₀ β) where eval s := (↟(s.map eval)).eval s.init
#align Eval.ind Etch.Verification.Eval.ind

structure StrictLawfulStream (ι : Type) [LinearOrder ι] (α : Type _) {β : Type _} [AddZeroClass β]
  [Eval α β] extends ι ⟶b α where
  strictLawful : IsStrictLawful (toStream.map eval)
#align StrictLawfulStream Etch.Verification.StrictLawfulStream

-- mathport name: «expr ⟶ₛ »
infixr:50 " ⟶ₛ " => StrictLawfulStream

attribute [instance] StrictLawfulStream.strictLawful

class LawfulEval (α : Type _) (β : outParam (Type _)) [NonUnitalNonAssocSemiring β] extends
  Eval α β, Add α, Mul α, Zero α where
  eval_zero : eval 0 = 0
  eval_add : ∀ x y, eval (x + y) = eval x + eval y
  eval_mul : ∀ x y, eval (x * y) = eval x * eval y
#align LawfulEval Etch.Verification.LawfulEval

instance LawfulEval.base {α : Type _} [NonUnitalNonAssocSemiring α] : LawfulEval α α where
  eval_zero := rfl
  eval_add _ _ := rfl
  eval_mul _ _ := rfl
#align LawfulEval.base Etch.Verification.LawfulEval.base

@[simps toStream init]
def BoundedStream.add [Zero α] [Add α] (q r : ι ⟶b α) : ι ⟶b α :=
  ⟨(↟q).add (↟r), (q.init, r.init), inferInstance⟩
#align BoundedStream.add Etch.Verification.BoundedStream.add

@[simps toStream init]
def BoundedStream.mul [Mul α] (q r : ι ⟶b α) : ι ⟶b α :=
  ⟨(↟q).mul (↟r), (q.init, r.init), inferInstance⟩
#align BoundedStream.mul Etch.Verification.BoundedStream.mul

@[simps toStream init]
def BoundedStream.zero : ι ⟶b α :=
  ⟨Stream.zero ι α, (), inferInstance⟩
#align BoundedStream.zero Etch.Verification.BoundedStream.zero

@[simps toStream init]
def BoundedStream.contract (s : ι ⟶b α) : Unit ⟶b α :=
  ⟨(↟s).contract, s.init, inferInstance⟩
#align BoundedStream.contract Etch.Verification.BoundedStream.contract

@[simps toStream init]
def BoundedStream.replicate (n : ℕ) (v : α) : Fin n ⟶b α :=
  ⟨Stream.replicate n v, 0, inferInstance⟩
#align BoundedStream.replicate Etch.Verification.BoundedStream.replicate

def Stream.eval' [AddZeroClass α] (s : Stream ι α) (q : s.σ) : ι →₀ α :=
  if _ : IsBounded s then s.eval q else Classical.arbitrary _
#align Stream.eval' Etch.Verification.Stream.eval'

theorem Stream.eval'_eq [AddZeroClass α] (s : Stream ι α) [IsBounded s] (q : s.σ) :
    s.eval' q = s.eval q :=
  dif_pos _
#align Stream.eval'_eq Etch.Verification.Stream.eval'_eq

theorem BoundedStream.zero_eval [NonUnitalNonAssocSemiring β] [LawfulEval α β] :
    eval (@BoundedStream.zero ι _ α) = (0 : ι →₀ β) := by
  dsimp [eval]
  rw [← Stream.eval'_eq]
  convert_to (Stream.zero ι β).eval' () = 0
  · congr
    simp [BoundedStream.map, BoundedStream.zero]
  · simp [Stream.eval'_eq]
#align BoundedStream.zero_eval Etch.Verification.BoundedStream.zero_eval

theorem Stream.add_map_eval [NonUnitalNonAssocSemiring β] [LawfulEval α β] :
    ∀ q r : Stream ι α, (q.add r).map Eval.eval = (q.map Eval.eval).add (r.map Eval.eval) :=
  Stream.add_map Eval.eval LawfulEval.eval_add LawfulEval.eval_zero
#align Stream.add_map_eval Etch.Verification.Stream.add_map_eval

theorem Stream.mul_map_eval [NonUnitalNonAssocSemiring β] [LawfulEval α β] :
    ∀ q r : Stream ι α, (q.mul r).map Eval.eval = (q.map Eval.eval).mul (r.map Eval.eval) :=
  Stream.mul_map Eval.eval LawfulEval.eval_mul
#align Stream.mul_map_eval Etch.Verification.Stream.mul_map_eval

theorem BoundedStream.add_map_eval [NonUnitalNonAssocSemiring β] [LawfulEval α β] (q r : ι ⟶b α) :
    (q.add r).map eval = (q.map eval).add (r.map eval) :=
  by
  ext : 1
  · exact Stream.add_map_eval (↟q) (↟r)
  rfl
#align BoundedStream.add_map_eval Etch.Verification.BoundedStream.add_map_eval

theorem BoundedStream.mul_map_eval [NonUnitalNonAssocSemiring β] [LawfulEval α β] (q r : ι ⟶b α) :
    (q.mul r).map eval = (q.map eval).mul (r.map eval) :=
  by
  ext : 1
  · exact Stream.mul_map_eval _ _
  rfl
#align BoundedStream.mul_map_eval Etch.Verification.BoundedStream.mul_map_eval

theorem BoundedStream.eval_add [NonUnitalNonAssocSemiring β] [LawfulEval α β] (q r : ι ⟶b α)
    [IsLawful ((↟q).map eval)] [IsLawful ((↟r).map eval)] : eval (q.add r) = eval q + eval r := by
  dsimp only [eval]; conv_lhs => rw [← Stream.eval'_eq]
  convert_to (↟(q.map eval).add (r.map eval)).eval' (q.add r).init = _
  · congr
    exact BoundedStream.add_map_eval q r
  · rw [Stream.eval'_eq]
    dsimp
    exact add_spec ..
#align BoundedStream.eval_add Etch.Verification.BoundedStream.eval_add

theorem BoundedStream.eval_contract [NonUnitalNonAssocSemiring β] [LawfulEval α β] (q : ι ⟶b α)
    [IsLawful ((↟q).map eval)] : (eval q.contract : Unit →₀ β) () = Finsupp.sumRange (eval q) := by
  dsimp [eval, ← Stream.contract_map]
  exact Stream.contract_eval ..
#align BoundedStream.eval_contract Etch.Verification.BoundedStream.eval_contract

theorem BoundedStream.eval_mul [NonUnitalNonAssocSemiring β] [LawfulEval α β] (q r : ι ⟶b α)
    [IsStrictLawful ((↟q).map eval)] [IsStrictLawful ((↟r).map eval)] :
    eval (q.mul r) = eval q * eval r := by
  dsimp only [eval]; conv_lhs => rw [← Stream.eval'_eq]
  convert_to (↟(q.map eval).mul (r.map eval)).eval' (q.mul r).init = _
  · congr
    exact BoundedStream.mul_map_eval q r
  rw [Stream.eval'_eq]; dsimp; rw [mul_spec]
#align BoundedStream.eval_mul Etch.Verification.BoundedStream.eval_mul

@[simps toBoundedStream]
def LawfulStream.replicate [NonUnitalNonAssocSemiring β] [LawfulEval α β] (n : ℕ) (v : α) :
    Fin n ⟶ₛ α :=
  ⟨BoundedStream.replicate n v, by dsimp; infer_instance⟩
#align LawfulStream.replicate Etch.Verification.LawfulStream.replicate

instance LawfulEval.ind [NonUnitalNonAssocSemiring β] [LawfulEval α β] :
    LawfulEval (ι ⟶ₛ α) (ι →₀ β)
    where
  eval s := eval s.toBoundedStream
  add x y :=
    ⟨x.add y.toBoundedStream, by
      dsimp
      rw [Stream.add_map_eval]
      infer_instance⟩
  mul x y :=
    ⟨x.mul y.toBoundedStream, by
      dsimp
      rw [Stream.mul_map_eval]
      infer_instance⟩
  zero :=
    ⟨BoundedStream.zero, by
      simp
      infer_instance⟩
  eval_zero := BoundedStream.zero_eval
  eval_add _ _ := BoundedStream.eval_add ..
  eval_mul _ _ := BoundedStream.eval_mul ..
#align LawfulEval.ind Etch.Verification.LawfulEval.ind

attribute [simp] LawfulEval.eval_add LawfulEval.eval_zero LawfulEval.eval_mul

@[simp]
theorem LawfulStream.eval_contract [NonUnitalNonAssocSemiring β] [LawfulEval α β] (q : ι ⟶ₛ α) :
    (eval q.contract : Unit →₀ β) () = Finsupp.sumRange (eval q) :=
  BoundedStream.eval_contract _
#align LawfulStream.eval_contract Etch.Verification.LawfulStream.eval_contract

@[simp]
theorem LawfulStream.eval_replicate [NonUnitalNonAssocSemiring β] [LawfulEval α β] (n : ℕ) (v : α)
    (j : Fin n) : (eval (LawfulStream.replicate n v) : Fin n →₀ β) j = eval v := by
  dsimp [eval]
  rw [Stream.replicate_eval]
#align LawfulStream.eval_replicate Etch.Verification.LawfulStream.eval_replicate

end
end Etch.Verification
