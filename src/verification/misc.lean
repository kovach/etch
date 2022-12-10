import data.fin.tuple.basic
import data.finsupp.basic
import data.finsupp.pointwise
import data.list.basic
import data.list.range
import data.option.basic
import data.pfun
import data.prod.lex

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

@[simp] lemma le_ff_iff {b : bool} : b ≤ ff ↔ b = ff :=
by cases b; simp

lemma ne_min_of_ne_and_ne {ι : Type*} [linear_order ι] {a x y : ι} (hx : a ≠ x) (hy : a ≠ y) :
  a ≠ min x y := by cases min_choice x y with h; rw h; assumption

@[simp] lemma max_ne_self_iff {ι : Type*} [linear_order ι] (a b : ι) :
  ¬(a = max a b) ↔ a < b :=
by { simp [max_def, ← not_lt], split_ifs, { simp [h, le_of_lt h] }, { simp [h, le_of_not_lt h] } }

@[simp] lemma max_ne_self_iff' {ι : Type*} [linear_order ι] (a b : ι) :
  ¬(b = max a b) ↔ b < a :=
by { rw max_comm, simp, }

section with_top
variables {ι : Type} [partial_order ι]

@[simp] lemma with_top.is_some_iff_lt_top {x : with_top ι} :
  x.is_some ↔ x < ⊤ :=
by { rw [← not_iff_not, eq_ff_eq_not_eq_tt, option.not_is_some, option.is_none_iff_eq_none, lt_top_iff_ne_top, ne, not_not], refl, }

lemma prod.lex.le_iff' {α β : Type} [has_lt α] [has_le β] {x y : α ×ₗ β} :
  x ≤ y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2) := prod.lex_def _ _

lemma prod.lex.le_iff'' {α β : Type} [partial_order α] [preorder β] {x y : α ×ₗ β} :
  x ≤ y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 ≤ y.2) :=
by { rw [prod.lex.le_iff', le_iff_lt_or_eq], have := @ne_of_lt _ _ x.1 y.1, tauto!, }

lemma prod.lex.lt_iff' {α β : Type} [has_lt α] [has_lt β] {x y : α ×ₗ β} :
  x < y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2) := prod.lex_def _ _

lemma prod.lex.fst_le_of_le {α β : Type} [preorder α] [preorder β] {x y : α ×ₗ β} (h : x ≤ y) : x.1 ≤ y.1 :=
by { rw prod.lex.le_iff' at h, cases h, { exact h.le, }, { exact h.1.le, }, }

lemma prod.lex.fst_lt_of_lt_of_le {α β : Type} [preorder α] [partial_order β] {x y : α ×ₗ β}
  (h : x < y) (h' : y.2 ≤ x.2) : x.1 < y.1 :=
by { rw prod.lex.lt_iff' at h, cases h, { exact h, }, cases h.2.not_le h', }

@[simp, norm_cast] lemma prod.with_top.coe_inj {α : Type} (x y : α) : (x : with_top α) = y ↔ x = y :=
option.some_inj

end with_top

/- NOTE: This stuff is already in mathlib (`data.finsupp.pointwise`) -/

-- variables {ι α : Type}

-- noncomputable instance finsupp.has_mul [mul_zero_class α] : has_mul (ι →₀ α) :=
-- ⟨λ a b, finsupp.zip_with (*) (zero_mul _) a b⟩

-- lemma finsupp.mul_apply [mul_zero_class α] (g₁ g₂ : ι →₀ α) (a : ι) : (g₁ * g₂) a = g₁ a * g₂ a := rfl

-- -- #check pi.distrib -- todo, tactic like this?
-- noncomputable instance finsupp.non_unital_semiring [non_unital_semiring α] : non_unital_semiring (ι →₀ α) :=
-- {
--   zero := 0,
--   add_assoc := λ a b c, fun_like.ext _ _ (by simp [finsupp.add_apply, add_assoc]),
--   zero_add  := λ a,     fun_like.ext _ _ (by simp [finsupp.add_apply]),
--   add_zero  := λ a,     fun_like.ext _ _ (by simp [finsupp.add_apply]),
--   add_comm  := λ a b,   fun_like.ext _ _ (by simp [finsupp.add_apply, add_comm] ),
--   zero_mul  := λ a,     fun_like.ext _ _ (by simp [finsupp.mul_apply]),
--   mul_zero  := λ a,     fun_like.ext _ _ (by simp [finsupp.mul_apply]),

--   left_distrib  := λ a b c, by simp [fun_like.ext_iff, finsupp.mul_apply, finsupp.add_apply, left_distrib],
--   right_distrib := λ a b c, by simp [fun_like.ext_iff, finsupp.mul_apply, finsupp.add_apply, right_distrib],

--   mul_assoc     := λ a b c, by simp [fun_like.ext_iff, finsupp.mul_apply, mul_assoc],

--   ..finsupp.has_mul, ..finsupp.has_add, }

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

set_option pp.implicit true


