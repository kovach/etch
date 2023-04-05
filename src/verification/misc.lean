import data.fin.tuple.basic
import data.finsupp.basic
import data.finsupp.pointwise
import data.list.basic
import data.list.range
import data.list.fin_range
import data.option.basic
import data.pfun
import data.prod.lex

/-! 
This is a collection of miscellaneous lemmas. Not all of these are used;
many of them where used in previous versions of the formalization/are used 
in the WIP verification of the code-generating compiler.
-/

lemma bool.coe_iff_eq_tt (b : bool) : b ↔ b = tt := iff.rfl
@[simp] lemma option.bind_const_none {α β} (x : option α) :
  x.bind (λ _, none) = (none : option β) :=
by cases x; simp
@[simp] lemma option.is_none_ff_iff_is_some {α} (x : option α) :
  x.is_none = ff ↔ x.is_some = tt :=
by cases x; simp

@[simp] lemma fin.tuple_eval_one {n : ℕ} {α : fin (n + 2) → Type*}
  (x₀ : α 0) (x₁ : α 1) (x₂ : Π i : fin n, α i.succ.succ) :
  fin.cons x₀ (fin.cons x₁ x₂) 1 = x₁ := rfl

@[simp] lemma fin.tuple_eval_two {n : ℕ} {α : fin (n + 3) → Type*}
  (x₀ : α 0) (x₁ : α 1) (x₂ : α 2) (x₃ : Π i : fin n, α i.succ.succ.succ) :
  fin.cons x₀ (fin.cons x₁ (fin.cons x₂ x₃)) 2 = x₂ := rfl

universes u v
variables {m : Type u → Type v} [monad m]

/- Technically `m` only needs to be applicative but whatever -/
def fin.tuple_sequence : ∀ {n : ℕ} {α : fin n → Type u},
  (Π i, m (α i)) → m (Π i, α i)
| 0 _ _ := pure default
| (n+1) α x := (x 0) >>= λ r, (fin.tuple_sequence (fin.tail x)) >>= λ x', return (fin.cons r x')

@[simp] lemma fin.tuple_sequence₁ [is_lawful_monad m] {α : fin 1 → Type u} (x : Π i, m (α i)) :
  fin.tuple_sequence x = (x 0) >>= λ r₀, pure (fin.cons r₀ default) :=
by simp [fin.tuple_sequence] with functor_norm

@[simp] lemma fin.tuple_sequence₂ [is_lawful_monad m] {α : fin 2 → Type u} (x : Π i, m (α i)) :
  fin.tuple_sequence x = (x 0) >>= λ r₀, (x 1) >>= λ r₁, pure (fin.cons r₀ $ fin.cons r₁ $ default) :=
by { simp [fin.tuple_sequence] with functor_norm, refl, }

def fin.tuple_some {n : ℕ} {α : fin n → Type u} (x : Π i, option (α i)) : option (Π i, α i) :=
fin.tuple_sequence x

@[simp] lemma option.bind_is_some {α β} (x : option α) (y : α → option β):
  (x >>= y).is_some ↔ (∃ (h : x.is_some), (y (option.get h)).is_some) :=
by cases x; simp

@[simp] lemma option.map_is_some {α β} (x : option α) (y : α → β) :
  (y <$> x).is_some = x.is_some := by cases x; simp

@[simp] lemma option.not_is_some' {α} (x : option α) : !x.is_some = x.is_none :=
by { cases x; simp, }

def option.guard_prop {α} (p : Prop) [decidable p] (x : α) : option α :=
  if p then some x else none
@[simp] lemma option.guard_prop_is_some {α} {p : Prop} [decidable p] {x : α} :
  (option.guard_prop p x).is_some ↔ p :=
by { dsimp only [option.guard_prop], split_ifs; simpa }

@[simp] lemma option.coe_part_dom {α} (x : option α) :
  (x : part α).dom ↔ x.is_some := by cases x; simp

@[simp] lemma option.coe_part_eq_some {α} (x : option α) (y : α) :
  (x : part α) = part.some y ↔ x = some y :=
by simp [part.eq_some_iff]

@[simp] lemma list.nth_is_some_iff {α} {x : list α} {n : ℕ} :
  (x.nth n).is_some ↔ n < x.length :=
by { rw ← not_iff_not, simp [option.is_none_iff_eq_none], }

@[simp] lemma option.map_is_some' {α β} (x : option α) (f : α → β) :
  (x.map f).is_some = x.is_some := by cases x; simp

lemma list.zip_with_fst {α β} {l₁ : list α} {l₂ : list β} (hl : l₁.length ≤ l₂.length) :
  list.zip_with (λ a b, a) l₁ l₂ = l₁ :=
by { erw [← list.map_uncurry_zip_eq_zip_with, list.map_fst_zip], exact hl, }

lemma list.zip_with_snd {α β} {l₁ : list α} {l₂ : list β} (hl : l₂.length ≤ l₁.length) :
  list.zip_with (λ a b, b) l₁ l₂ = l₂ :=
by { erw [← list.map_uncurry_zip_eq_zip_with, list.map_snd_zip], exact hl, }

@[simp] lemma multiset.map_nth_le {α} {n : ℕ} {l : list α} (hn : l.length = n) :
    (finset.univ.val : multiset (fin n)).map (λ i, l.nth_le i (by rw hn; exact i.prop)) = l :=
by { subst hn, simp [finset.univ, fintype.elems], erw list.map_nth_le, }

@[simp] lemma le_ff_iff : ∀ {b : bool}, b ≤ ff ↔ b = ff := dec_trivial

@[simp] lemma lt_tt_iff : ∀ {b : bool}, b < tt ↔ b = ff := dec_trivial

lemma bool.min_eq_and {a b : bool} : min a b = a && b := rfl

lemma ne_min_of_ne_and_ne {ι : Type*} [linear_order ι] {a x y : ι} (hx : a ≠ x) (hy : a ≠ y) :
  a ≠ min x y := by cases min_choice x y with h; rw h; assumption

@[simp] lemma max_ne_self_iff {ι : Type*} [linear_order ι] (a b : ι) :
  ¬(a = max a b) ↔ a < b :=
by { rw max_def, split_ifs, { simpa using h }, { simpa using le_of_not_ge h } }

@[simp] lemma max_ne_self_iff' {ι : Type*} [linear_order ι] (a b : ι) :
  ¬(b = max a b) ↔ b < a :=
by { rw max_comm, simp, }

section with_top
variables {ι : Type} [partial_order ι]

@[simp] lemma with_top.is_some_iff_lt_top {x : with_top ι} :
  x.is_some ↔ x < ⊤ :=
by { rw [← not_iff_not, eq_ff_eq_not_eq_tt, option.not_is_some, option.is_none_iff_eq_none, lt_top_iff_ne_top, ne, not_not], refl, }

@[simp, norm_cast] lemma prod.with_top.coe_inj {α : Type} (x y : α) : (x : with_top α) = y ↔ x = y :=
option.some_inj

end with_top

namespace prod
variables {α β : Type*} (r₁ : α → α → Prop) (r₂ : β → β → Prop)

def rprod_eq (s₁ s₂ : α × β) : Prop :=
(r₁ s₁.1 s₂.1 ∧ (r₂ s₁.2 s₂.2 ∨ s₁.2 = s₂.2)) ∨
  (r₂ s₁.2 s₂.2 ∧ (r₁ s₁.1 s₂.1 ∨ s₁.1 = s₂.1))

variables {r₁ r₂}

theorem rprod_eq_sub_lex (s₁ s₂ : α × β) (h : rprod_eq r₁ r₂ s₁ s₂) :
  prod.lex r₁ r₂ s₁ s₂ :=
begin
  cases s₁ with a b, cases s₂ with c d,
  rcases h with (⟨h₁, _⟩|⟨h₁, (h₂|h₂)⟩),
  { exact prod.lex.left _ _ h₁, },
  { exact prod.lex.left _ _ h₂, },
  { dsimp only at h₁ h₂, rw h₂, exact prod.lex.right _ h₁, }
end

theorem rprod_eq_wf (h₁ : well_founded r₁) (h₂ : well_founded r₂) :
  well_founded (rprod_eq r₁ r₂) :=
subrelation.wf rprod_eq_sub_lex (lex_wf h₁ h₂)

namespace lex

local notation a ` <ₗ `:50 b := @has_lt.lt (α ×ₗ β) _ a b
local notation a ` ≤ₗ `:50 b := @has_le.le (α ×ₗ β) _ a b

lemma le_iff' [has_lt α] [has_le β] {x y : α ×ₗ β} :
  x ≤ y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2) := prod.lex_def _ _

lemma le_iff'' [partial_order α] [preorder β] {x y : α ×ₗ β} :
  x ≤ y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 ≤ y.2) :=
by { rw [prod.lex.le_iff', le_iff_lt_or_eq], have := @ne_of_lt _ _ x.1 y.1, tauto!, }

lemma lt_iff' [has_lt α] [has_lt β] {x y : α ×ₗ β} :
  x < y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2) := prod.lex_def _ _

lemma lt_iff'' [partial_order α] [preorder β] {x y : α ×ₗ β} :
  x < y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 < y.2) :=
by { rw [lt_iff', le_iff_lt_or_eq], have : x.1 < y.1 → ¬(x.1 = y.1) := ne_of_lt, tauto, }

lemma fst_le_of_le [preorder α] [preorder β] {x y : α ×ₗ β} (h : x ≤ y) : x.1 ≤ y.1 :=
by { rw prod.lex.le_iff' at h, cases h, { exact h.le, }, { exact h.1.le, }, }

lemma fst_lt_of_lt_of_le [preorder α] [partial_order β] {x y : α ×ₗ β}
  (h : x < y) (h' : y.2 ≤ x.2) : x.1 < y.1 :=
by { rw prod.lex.lt_iff' at h, cases h, { exact h, }, cases h.2.not_le h', }

lemma fst_mono [preorder α] [preorder β] :
  @monotone (α ×ₗ β) α _ _ prod.fst := λ x y, fst_le_of_le

lemma min_fst [linear_order α] [linear_order β] (x y : α ×ₗ β) :
  (min x y).1 = min x.1 y.1 := monotone.map_min fst_mono

@[simp] lemma mk_fst_mono_iff [preorder α] [preorder β]
  {x : α} {y₁ y₂ : β} : ((x, y₁) ≤ₗ (x, y₂)) ↔ y₁ ≤ y₂ := by simp [le_iff']

@[simp] lemma mk_fst_mono_lt_iff [preorder α] [preorder β]
  {x : α} {y₁ y₂ : β} : ((x, y₁) <ₗ (x, y₂)) ↔ y₁ < y₂ := by simp [lt_iff']

@[simp] lemma mk_snd_mono_le_iff [partial_order α] [preorder β]
  {x₁ x₂ : α} {y : β} : ((x₁, y) ≤ₗ (x₂, y)) ↔ x₁ ≤ x₂ := by simp [le_iff'']

@[simp] lemma mk_snd_mono_lt_iff [preorder α] [preorder β]
  {x₁ x₂ : α} {y : β} : ((x₁, y) <ₗ (x₂, y)) ↔ x₁ < x₂ := by simp [lt_iff']

@[simp] lemma mk_ff_lt_mk_tt_iff [partial_order α] {x₁ x₂ : α} :
  (@has_lt.lt (α ×ₗ bool) _ (x₁, ff) (x₂, tt)) ↔ x₁ ≤ x₂ := by simp [lt_iff', le_iff_lt_or_eq]

lemma mk_min [linear_order α] [linear_order β] (x : α) (y₁ y₂ : β) :
  @min (α ×ₗ β) _ (x, y₁) (x, y₂) = (x, min y₁ y₂) :=
(@monotone.map_min _ (α ×ₗ β) _ _ (λ y, (x, y)) y₁ y₂ $ λ y₁ y₂, by simp).symm

end lex

end prod

@[simp] lemma max_le_min_iff {α : Type*} [linear_order α] {x y : α} :
  max x y ≤ min x y ↔ x = y := by simpa using le_antisymm_iff.symm

@[simp] lemma max_eq_min_iff {α : Type*} [linear_order α] {x y : α} :
   min x y = max x y ↔ x = y :=
⟨λ h, max_le_min_iff.mp h.symm.le, λ h, by simp [h]⟩ 

@[simp] lemma finsupp.mul_single {ι β : Type*} [mul_zero_class β] (i : ι) (x y : β) :
  (finsupp.single i x) * (finsupp.single i y) = finsupp.single i (x * y) :=
by { ext a, by_cases i = a; simp [h], }

lemma finsupp.mul_eq_zero_of_disjoint_support {ι β : Type*} [decidable_eq ι] [mul_zero_class β] (f g : ι →₀ β) (h : disjoint f.support g.support) :
  f * g = 0 :=
begin
  rw [← finsupp.support_eq_empty, ← finset.subset_empty],
  refine trans finsupp.support_mul _,
  rwa [finset.subset_empty, ← finset.disjoint_iff_inter_eq_empty],
end

lemma finsupp.mul_single_eq_zero {ι β : Type*} [mul_zero_class β] (i₁ i₂ : ι) (hi : i₁ ≠ i₂) (x y : β) :
  (finsupp.single i₁ x) * (finsupp.single i₂ y) = 0 :=
by { classical, rw [finsupp.mul_eq_zero_of_disjoint_support], simp [finset.disjoint_iff_ne, finsupp.mem_support_single], intros, exact hi, }

lemma finsupp.mul_filter {ι β : Type*} [mul_zero_class β] (P Q : ι → Prop) (f g : ι →₀ β) :
  (f.filter P) * (g.filter Q) = (f * g).filter (λ i, P i ∧ Q i) :=
by { ext i, by_cases h₁ : P i; by_cases h₂ : Q i; simp [h₁, h₂], }

lemma finsupp.mul_filter' {ι β : Type*} [mul_zero_class β] (P : ι → Prop) (f g : ι →₀ β) :
  (f * g).filter P = (f.filter P) * (g.filter P) := by simp [finsupp.mul_filter]

lemma finsupp.filter_ext_iff {ι β : Type*} [add_zero_class β] (P : ι → Prop) (f g : ι →₀ β) :
  (f.filter P = g.filter P) ↔ (∀ a, P a → f a = g a) :=
by { classical, simp [fun_like.ext_iff, finsupp.filter_apply, apply_ite2 (=), ← imp_iff_not_or], }

lemma mul_eq_zero_of {α : Type*} [mul_zero_class α] {x y : α} : x = 0 ∨ y = 0 → x * y = 0
| (or.inl h) := by { rw h, exact zero_mul y, }
| (or.inr h) := by { rw h, exact mul_zero x, }

