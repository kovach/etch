import algebra.big_operators.finsupp
import tactic.field_simp
import data.rat.floor

def BoundedStreamGen : Type := sorry

def BoundedStreamGen.eval (x : BoundedStreamGen) : ℕ →₀ ℤ := sorry

def contract (x : BoundedStreamGen) : BoundedStreamGen := sorry

def externSparseVec (x : list ℕ) (y : list ℤ) : BoundedStreamGen := sorry

lemma externSparseVec.spec (x : list ℕ) (y : list ℤ) :
  (externSparseVec x y).eval = (list.zip_with finsupp.single x y).sum := sorry

lemma contract.spec (s : BoundedStreamGen) :
  (contract s).eval = s.eval.map_domain (λ _, 0) := sorry

class HasCorrectEval (x : BoundedStreamGen) (gn : out_param $ ℕ →₀ ℤ) : Prop :=
(iseq [] : x.eval = gn)

open HasCorrectEval (iseq)

instance externSparseVec.correctEval (x : list ℕ) (y : list ℤ) [fact (x.length = y.length)] :
  HasCorrectEval (externSparseVec x y) (list.zip_with finsupp.single x y).sum := ⟨externSparseVec.spec _ _⟩

instance contract.correctEval (s : BoundedStreamGen) {gn : ℕ →₀ ℤ} 
  [HasCorrectEval s gn] : HasCorrectEval (contract s) (finsupp.map_domain.add_monoid_hom (λ _, 0) gn) :=
⟨by { rw [contract.spec, iseq], refl, }⟩

def sum_vec (x : list ℕ) (y : list ℤ) : BoundedStreamGen := contract (externSparseVec x y)

lemma sum_vec.spec (x : list ℕ) (y : list ℤ) (hx : x.length = y.length) :
  (sum_vec x y).eval = finsupp.single 0 y.sum :=
begin
  haveI : fact _ := ⟨hx⟩,
  rw [sum_vec, iseq],-- ← list.sum_hom, list.map_zip_with],
  -- simp,
end



open HasCorrectEval (iseq)



universe u
lemma eq_of_heq' {α : Sort u} {a a' : α} (h : a == a') : a = a' :=
have ∀ (α' : Sort u) (a' : α') (h₁ : @heq α a α' a') (h₂ : α = α'), (eq.rec_on h₂ a : α') = a', from
  λ (α' : Sort u) (a' : α') (h₁ : @heq α a α' a'), heq.rec_on h₁ (λ h₂ : α = α, rfl),
show (eq.rec_on (eq.refl α) a : α) = a', from
  this α a' h (eq.refl α)


def star (f : ℕ → ℕ) (hf : ∀ n : ℕ, f (n + 1) ≤ n) : ℕ → ℕ
| 0 := 0
| (n + 1) := have _ := nat.lt_succ_of_le (hf n), if f (n + 1) = 0 then 0 else 1 + star (f (n + 1))

notation f`＊`:9000 := star f (by assumption)

lemma star_eq {f : ℕ → ℕ} (h₁ : f 0 = 0) (h₂ : ∀ n, f (n + 1) ≤ n) (n : ℕ) : 
  f＊ n = if f n = 0 then 0 else 1 + f＊ (f n) :=
by cases n; simp [star, h₁]

@[simp] lemma star_zero {f : ℕ → ℕ} (h₂ : ∀ n, f (n + 1) ≤ n) : f＊ 0 = 0 := by simp [star]

@[simp] lemma star_one {f : ℕ → ℕ} (h₂ : ∀ n, f (n + 1) ≤ n) : f＊ 1 = 0 :=
by simpa [star, imp_false] using h₂ 0

lemma star_contraction_of_contraction {f : ℕ → ℕ} (H : ∀ n, f (n + 1) ≤ n) (n : ℕ) :
  f＊ 0 = 0 ∧ f＊ (n + 1) ≤ n :=
begin
  split, { simp, },
  induction n using nat.strong_induction_on with n ih,
  rw star,
  split_ifs, { exact zero_le _, },
  specialize H n, refine trans _ H,
  cases (f (n + 1)) with m hm, { contradiction, },
  rw [nat.succ_eq_add_one, add_comm 1 _, add_le_add_iff_right],
  refine ih m _,
  rwa ← nat.succ_le_iff,
end

-- open_locale big_operators


-- lemma egyption_fraction_wf (r : ℚ) (h₁ : 0 < r) (h₂ : r < 1) :
--   (r - (1 : ℚ) / ⌈1/r⌉).num < r.num :=
-- begin
  
-- end

-- def egyptian_fraction : ∀ (r : ℚ) (h₁ : 0 ≤ r) (h₂ : r < 1), finset ℤ | r h₁ h₂ :=
-- if H : r = 0 then 0 else
-- let n : ℤ := ⌈1/r⌉ in
-- have wf : (r - (1 : ℚ) / n).num < r.num := sorry, 
-- insert n (egyptian_fraction (r - (1 : ℚ) / n) _ _)
-- using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf rat.num⟩]}
