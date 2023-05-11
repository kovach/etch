import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange
import Mathlib.Data.Option.Basic
import Mathlib.Data.PFun
import Mathlib.Data.Prod.Lex
import Mathlib.Init.IteSimp

/-!
This is a collection of miscellaneous lemmas. Not all of these are used;
many of them where used in previous versions of the formalization/are used
in the WIP verification of the code-generating compiler.
-/


theorem Bool.coe_iff_eq_true (b : Bool) : b ↔ b = true :=
  Iff.rfl
#align bool.coe_iff_eq_tt Bool.coe_iff_eq_true

@[simp]
theorem Option.bind_const_none {α β} (x : Option α) : (x.bind fun _ => none) = (none : Option β) :=
  by cases x <;> simp
#align option.bind_const_none Option.bind_const_none

@[simp]
theorem Option.isNone_false_iff_isSome {α} (x : Option α) : x.isNone = false ↔ x.isSome = true :=
  by cases x <;> simp
#align option.is_none_ff_iff_is_some Option.isNone_false_iff_isSome

@[simp]
theorem Fin.tuple_eval_one {n : ℕ} {α : Fin (n + 2) → Type _} (x₀ : α 0) (x₁ : α 1)
    (x₂ : ∀ i : Fin n, α i.succ.succ) : Fin.cons x₀ (Fin.cons x₁ x₂) 1 = x₁ :=
  rfl
#align fin.tuple_eval_one Fin.tuple_eval_one

@[simp]
theorem Fin.tuple_eval_two {n : ℕ} {α : Fin (n + 3) → Type _} (x₀ : α 0) (x₁ : α 1) (x₂ : α 2)
    (x₃ : ∀ i : Fin n, α i.succ.succ.succ) : Fin.cons x₀ (Fin.cons x₁ (Fin.cons x₂ x₃)) 2 = x₂ :=
  rfl
#align fin.tuple_eval_two Fin.tuple_eval_two

universe u v

variable {m : Type u → Type v} [Monad m]

-- Technically `m` only needs to be applicative but whatever
def Fin.tupleSequence : ∀ {n : ℕ} {α : Fin n → Type u}, (∀ i, m (α i)) → m (∀ i, α i)
  | 0, _, _ => pure default
  | n + 1, α, x =>
    x 0 >>= fun r => Fin.tupleSequence (Fin.tail x) >>= fun x' => return (Fin.cons r x')
#align fin.tuple_sequence Fin.tupleSequence

@[simp]
theorem Fin.tuple_sequence₁ [LawfulMonad m] {α : Fin 1 → Type u} (x : ∀ i, m (α i)) :
    Fin.tupleSequence x = x 0 >>= fun r₀ => pure (Fin.cons r₀ default) := by
  simp [Fin.tupleSequence, functor_norm]
#align fin.tuple_sequence₁ Fin.tuple_sequence₁

@[simp]
theorem Fin.tuple_sequence₂ [LawfulMonad m] {α : Fin 2 → Type u} (x : ∀ i, m (α i)) :
    Fin.tupleSequence x =
      x 0 >>= fun r₀ => x 1 >>= fun r₁ => pure (Fin.cons r₀ <| Fin.cons r₁ <| default) := by
  simp [Fin.tupleSequence, functor_norm]
  rfl
#align fin.tuple_sequence₂ Fin.tuple_sequence₂

def Fin.tupleSome {n : ℕ} {α : Fin n → Type u} (x : ∀ i, Option (α i)) : Option (∀ i, α i) :=
  Fin.tupleSequence x
#align fin.tuple_some Fin.tupleSome

@[simp]
theorem Option.bind_isSome {α β} (x : Option α) (y : α → Option β) :
    (x.bind y).isSome ↔ ∃ h : x.isSome, (y (x.get h)).isSome := by cases x <;> simp
#align option.bind_is_some Option.bind_isSome

@[simp]
theorem Option.map_isSome {α β} (x : Option α) (y : α → β) : (y <$> x).isSome = x.isSome := by
  cases x <;> simp
#align option.map_is_some Option.map_isSome

@[simp]
theorem Option.not_isSome' {α} (x : Option α) : !x.isSome = x.isNone := by cases x <;> simp
#align option.not_is_some' Option.not_isSome'

def Option.guardProp {α} (p : Prop) [Decidable p] (x : α) : Option α :=
  if p then some x else none
#align option.guard_prop Option.guardProp

@[simp]
theorem Option.guardProp_isSome {α} {p : Prop} [Decidable p] {x : α} :
    (Option.guardProp p x).isSome ↔ p := by
  dsimp only [Option.guardProp]
  split_ifs <;> simpa
#align option.guard_prop_is_some Option.guardProp_isSome

@[simp]
theorem Option.coe_part_dom {α} (x : Option α) : (x : Part α).Dom ↔ x.isSome := by cases x <;> simp
#align option.coe_part_dom Option.coe_part_dom

@[simp]
theorem Option.coe_part_eq_some {α} (x : Option α) (y : α) :
    (x : Part α) = Part.some y ↔ x = some y := by simp [Part.eq_some_iff]
#align option.coe_part_eq_some Option.coe_part_eq_some

@[simp]
theorem List.get?_isSome_iff {α} {x : List α} {n : ℕ} : (x.get? n).isSome ↔ n < x.length := by
  rw [← not_iff_not]
  simp [Option.isNone_iff_eq_none]
#align list.nth_is_some_iff List.get?_isSome_iff

@[simp]
theorem Option.map_is_some' {α β} (x : Option α) (f : α → β) : (x.map f).isSome = x.isSome := by
  cases x <;> simp
#align option.map_is_some' Option.map_is_some'

theorem List.zipWith_fst {α β} {l₁ : List α} {l₂ : List β} (hl : l₁.length ≤ l₂.length) :
    List.zipWith (fun a b => a) l₁ l₂ = l₁ := by
  erw [← List.map_uncurry_zip_eq_zipWith, List.map_fst_zip]
  exact hl
#align list.zip_with_fst List.zipWith_fst

theorem List.zipWith_snd {α β} {l₁ : List α} {l₂ : List β} (hl : l₂.length ≤ l₁.length) :
    List.zipWith (fun a b => b) l₁ l₂ = l₂ := by
  erw [← List.map_uncurry_zip_eq_zipWith, List.map_snd_zip]
  exact hl
#align list.zip_with_snd List.zipWith_snd

@[simp]
theorem Multiset.map_get {α} {l : List α} :
    (Finset.univ.val : Multiset (Fin l.length)).map l.get = l := by
  simp [Finset.univ, Fintype.elems]
#align multiset.map_nth_le Multiset.map_get

@[simp]
theorem le_false_iff : ∀ {b : Bool}, b ≤ false ↔ b = false := by decide
#align le_ff_iff le_false_iff

@[simp]
theorem lt_true_iff : ∀ {b : Bool}, b < true ↔ b = false := by decide
#align lt_tt_iff lt_true_iff

@[simp]
theorem false_lt_iff : ∀ {b : Bool}, false < b ↔ b = true := by decide
#align ff_lt_iff false_lt_iff

theorem Bool.min_eq_and {a b : Bool} : min a b = (a && b) := rfl
#align bool.min_eq_and Bool.min_eq_and

theorem ne_min_of_ne_and_ne {ι : Type _} [LinearOrder ι] {a x y : ι} (hx : a ≠ x) (hy : a ≠ y) :
    a ≠ min x y := by cases' min_choice x y with h h <;> rw [h] <;> assumption
#align ne_min_of_ne_and_ne ne_min_of_ne_and_ne

@[simp]
theorem max_ne_self_iff {ι : Type _} [LinearOrder ι] (a b : ι) : ¬a = max a b ↔ a < b := by
  rw [max_def]
  split_ifs with h
  · simpa using h
  · simpa using le_of_not_ge h
#align max_ne_self_iff max_ne_self_iff

@[simp]
theorem max_ne_self_iff' {ι : Type _} [LinearOrder ι] (a b : ι) : ¬b = max a b ↔ b < a := by
  rw [max_comm]; simp
#align max_ne_self_iff' max_ne_self_iff'

section WithTop

variable {ι : Type} [PartialOrder ι]

@[simp]
theorem WithTop.isSome_iff_lt_top {x : WithTop ι} : x.isSome ↔ x < ⊤ := by
  rw [← not_iff_not, Bool.eq_false_eq_not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none,
    lt_top_iff_ne_top, Ne, Classical.not_not]
  rfl
#align with_top.is_some_iff_lt_top WithTop.isSome_iff_lt_top

@[simp, norm_cast]
theorem Prod.WithTop.coe_inj {α : Type} (x y : α) : (x : WithTop α) = y ↔ x = y :=
  Option.some_inj
#align prod.with_top.coe_inj Prod.WithTop.coe_inj

end WithTop

namespace Prod

variable {α β : Type _} (r₁ : α → α → Prop) (r₂ : β → β → Prop)

def RProdEq (s₁ s₂ : α × β) : Prop :=
  r₁ s₁.1 s₂.1 ∧ (r₂ s₁.2 s₂.2 ∨ s₁.2 = s₂.2) ∨ r₂ s₁.2 s₂.2 ∧ (r₁ s₁.1 s₂.1 ∨ s₁.1 = s₂.1)
#align prod.rprod_eq Prod.RProdEq

variable {r₁ r₂}

def RProdEqSubLex (s₁ s₂ : α × β) (h : RProdEq r₁ r₂ s₁ s₂) : Prod.Lex r₁ r₂ s₁ s₂ := by
  cases' s₁ with a b; cases' s₂ with c d
  rcases h with (⟨h₁, _⟩ | ⟨h₁, h₂ | h₂⟩)
  · exact Prod.Lex.left _ _ h₁
  · exact Prod.Lex.left _ _ h₂
  · dsimp only at h₁ h₂
    rw [h₂]
    exact Prod.Lex.right _ h₁
#align prod.rprod_eq_sub_lex Prod.RProdEqSubLex

def rprodEq (ha : WellFoundedRelation α) (hb : WellFoundedRelation β) : WellFoundedRelation (α × β) where
  rel := RProdEq ha.rel hb.rel
  wf := by
    apply Subrelation.wf (r := Prod.Lex ha.rel hb.rel) (h₂ := (lex ha hb).wf)
    intro a b h
    exact RProdEqSubLex a b h
-- #align prod.rprod_eq_wf Prod.rprodEq

namespace Lex

-- mathport name: «expr <ₗ »
local notation:50 a " <ₗ " b => @LT.lt (α ×ₗ β) _ a b

-- mathport name: «expr ≤ₗ »
local notation:50 a " ≤ₗ " b => @LE.le (α ×ₗ β) _ a b

theorem le_iff' [LT α] [LE β] {x y : α ×ₗ β} : x ≤ y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 ≤ y.2 :=
  Prod.lex_def _ _
#align prod.lex.le_iff' Prod.Lex.le_iff'

theorem le_iff'' [PartialOrder α] [Preorder β] {x y : α ×ₗ β} :
    x ≤ y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 ≤ y.2) := by
  rw [Prod.Lex.le_iff', le_iff_lt_or_eq]
  have := @ne_of_lt _ _ x.1 y.1
  tauto
#align prod.lex.le_iff'' Prod.Lex.le_iff''

theorem lt_iff' [LT α] [LT β] {x y : α ×ₗ β} : x < y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2 :=
  Prod.lex_def _ _
#align prod.lex.lt_iff' Prod.Lex.lt_iff'

theorem lt_iff'' [PartialOrder α] [Preorder β] {x y : α ×ₗ β} :
    x < y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 < y.2) := by
  rw [lt_iff', le_iff_lt_or_eq]
  have : x.1 < y.1 → ¬x.1 = y.1 := ne_of_lt
  tauto
#align prod.lex.lt_iff'' Prod.Lex.lt_iff''

theorem fst_le_of_le [Preorder α] [Preorder β] {x y : α ×ₗ β} (h : x ≤ y) : x.1 ≤ y.1 := by
  rw [Prod.Lex.le_iff'] at h
  cases h with
  | inl h => exact h.le
  | inr h => exact h.1.le
#align prod.lex.fst_le_of_le Prod.Lex.fst_le_of_le

theorem fst_lt_of_lt_of_le [Preorder α] [PartialOrder β] {x y : α ×ₗ β} (h : x < y)
    (h' : y.2 ≤ x.2) : x.1 < y.1 := by
  rw [Prod.Lex.lt_iff'] at h
  cases h with
  | inl h => exact h
  | inr h => cases h.2.not_le h'
#align prod.lex.fst_lt_of_lt_of_le Prod.Lex.fst_lt_of_lt_of_le

theorem fst_mono [Preorder α] [Preorder β] : @Monotone (α ×ₗ β) α _ _ Prod.fst := fun _ _ =>
  fst_le_of_le
#align prod.lex.fst_mono Prod.Lex.fst_mono

theorem min_fst [LinearOrder α] [LinearOrder β] (x y : α ×ₗ β) : (min x y).1 = min x.1 y.1 :=
  Monotone.map_min fst_mono
#align prod.lex.min_fst Prod.Lex.min_fst

@[simp]
theorem mk_fst_mono_iff [Preorder α] [Preorder β] {x : α} {y₁ y₂ : β} :
    ((x, y₁) ≤ₗ (x, y₂)) ↔ y₁ ≤ y₂ := by simp [le_iff']
#align prod.lex.mk_fst_mono_iff Prod.Lex.mk_fst_mono_iff

@[simp]
theorem mk_fst_mono_lt_iff [Preorder α] [Preorder β] {x : α} {y₁ y₂ : β} :
    ((x, y₁) <ₗ (x, y₂)) ↔ y₁ < y₂ := by simp [lt_iff']
#align prod.lex.mk_fst_mono_lt_iff Prod.Lex.mk_fst_mono_lt_iff

@[simp]
theorem mk_snd_mono_le_iff [PartialOrder α] [Preorder β] {x₁ x₂ : α} {y : β} :
    ((x₁, y) ≤ₗ (x₂, y)) ↔ x₁ ≤ x₂ := by simp [le_iff'']
#align prod.lex.mk_snd_mono_le_iff Prod.Lex.mk_snd_mono_le_iff

@[simp]
theorem mk_snd_mono_lt_iff [Preorder α] [Preorder β] {x₁ x₂ : α} {y : β} :
    ((x₁, y) <ₗ (x₂, y)) ↔ x₁ < x₂ := by simp [lt_iff']
#align prod.lex.mk_snd_mono_lt_iff Prod.Lex.mk_snd_mono_lt_iff

@[simp]
theorem mk_false_lt_mk_true_iff [PartialOrder α] {x₁ x₂ : α} :
    @LT.lt (α ×ₗ Bool) _ (x₁, false) (x₂, true) ↔ x₁ ≤ x₂ := by simp [lt_iff', le_iff_lt_or_eq]
#align prod.lex.mk_ff_lt_mk_tt_iff Prod.Lex.mk_false_lt_mk_true_iff

@[simp]
theorem mk_true_le_mk_false_iff_lt [PartialOrder α] (x y : α) :
    @LE.le (α ×ₗ Bool) _ (x, true) (y, false) ↔ x < y := by simp [le_iff']
#align prod.lex.mk_tt_le_mk_ff_iff_lt Prod.Lex.mk_true_le_mk_false_iff_lt

theorem mk_min [LinearOrder α] [LinearOrder β] (x : α) (y₁ y₂ : β) :
    @min (α ×ₗ β) _ (x, y₁) (x, y₂) = (x, min y₁ y₂) :=
  (@Monotone.map_min _ (α ×ₗ β) _ _ (fun y => (x, y)) y₁ y₂ fun y₁ y₂ => by simp).symm
#align prod.lex.mk_min Prod.Lex.mk_min

end Lex

end Prod

@[simp]
theorem max_le_min_iff {α : Type _} [LinearOrder α] {x y : α} : max x y ≤ min x y ↔ x = y := by
  have h : max x y ≤ min x y ↔ y = x := by simpa using le_antisymm_iff.symm
  exact h.trans eq_comm
#align max_le_min_iff max_le_min_iff

@[simp]
theorem max_eq_min_iff {α : Type _} [LinearOrder α] {x y : α} : min x y = max x y ↔ x = y :=
  ⟨fun h => max_le_min_iff.mp h.symm.le, fun h => by simp [h]⟩
#align max_eq_min_iff max_eq_min_iff

@[simp]
theorem Finsupp.mul_single {ι β : Type _} [MulZeroClass β] (i : ι) (x y : β) :
    Finsupp.single i x * Finsupp.single i y = Finsupp.single i (x * y) := by
  ext a
  by_cases i = a <;> simp [h]
#align finsupp.mul_single Finsupp.mul_single

theorem Finsupp.mul_eq_zero_of_disjoint_support {ι β : Type _} [DecidableEq ι] [MulZeroClass β]
    (f g : ι →₀ β) (h : Disjoint f.support g.support) : f * g = 0 := by
  rw [← Finsupp.support_eq_empty, ← Finset.subset_empty]
  refine' _root_.trans Finsupp.support_mul _
  rwa [Finset.subset_empty, ← Finset.disjoint_iff_inter_eq_empty]
#align finsupp.mul_eq_zero_of_disjoint_support Finsupp.mul_eq_zero_of_disjoint_support

theorem Finsupp.mul_single_eq_zero {ι β : Type _} [MulZeroClass β] (i₁ i₂ : ι) (hi : i₁ ≠ i₂)
    (x y : β) : Finsupp.single i₁ x * Finsupp.single i₂ y = 0 := by classical
  rw [Finsupp.mul_eq_zero_of_disjoint_support]
  simp_rw [Finset.disjoint_iff_ne, Finsupp.mem_support_single]
  simp_rw [and_imp, forall_eq]
  intros
  exact hi
#align finsupp.mul_single_eq_zero Finsupp.mul_single_eq_zero

theorem Finsupp.mul_filter {ι β : Type _} [MulZeroClass β] (P Q : ι → Prop) (f g : ι →₀ β) :
    f.filter P * g.filter Q = (f * g).filter fun i => P i ∧ Q i := by
  ext i
  by_cases h₁ : P i <;> by_cases h₂ : Q i <;> simp [h₁, h₂]
#align finsupp.mul_filter Finsupp.mul_filter

theorem Finsupp.mul_filter' {ι β : Type _} [MulZeroClass β] (P : ι → Prop) (f g : ι →₀ β) :
    (f * g).filter P = f.filter P * g.filter P := by simp [Finsupp.mul_filter]
#align finsupp.mul_filter' Finsupp.mul_filter'

theorem Finsupp.filter_ext_iff {ι β : Type _} [AddZeroClass β] (P : ι → Prop) (f g : ι →₀ β) :
    f.filter P = g.filter P ↔ ∀ a, P a → f a = g a := by classical
  simp [FunLike.ext_iff, Finsupp.filter_apply, apply_ite₂ (· = ·), ← imp_iff_not_or]
#align finsupp.filter_ext_iff Finsupp.filter_ext_iff

theorem mul_eq_zero_of {α : Type _} [MulZeroClass α] {x y : α} : x = 0 ∨ y = 0 → x * y = 0
  | Or.inl h => by
    rw [h]
    exact MulZeroClass.zero_mul y
  | Or.inr h => by
    rw [h]
    exact MulZeroClass.mul_zero x
#align mul_eq_zero_of mul_eq_zero_of

