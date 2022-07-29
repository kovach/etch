import algebra

def finmap (α β : Type*) := α → option β

namespace finmap
variables (α β : Type*) [decidable_eq α]
def empty {α β} [decidable_eq α] : finmap α β := λ _, none
def extend {α β} [decidable_eq α] (m : finmap α β) (k : α) (v : β) := λ k', if k = k' then some v else m k'
notation `•` := empty
notation m `⟦` k `:` v `⟧` := extend m k v
#eval •⟦1:3⟧ 1
#check ([] : list ℕ)
#check []

def m1 : finmap ℕ ℕ := •⟦1:3⟧⟦2:4⟧
#eval m1 2

lemma sound {α β} [decidable_eq α] (m : finmap α β) (k : α) (v : β) : m⟦k:v⟧ k = some v :=
begin
simp only [extend], split_ifs, all_goals {refl},
end
lemma frame {α β} [decidable_eq α] (m : finmap α β) (k k' : α) (v : β) : k ≠ k' → m⟦k':v⟧ k = m k := λ h,
begin
simp only [extend], split_ifs with h2, exact false.rec _ (h h2.symm), refl,
end
end finmap

universes u v
inductive hlist : list (Type u) → Type (u+1)
| nil : hlist []
| cons {i} {is} : i → hlist is → hlist (i :: is)
infixr ` :: `:67 := hlist.cons --notation `[` `]` := HList.nil
inductive hmem : Type u → list (Type u) → Type (u+1)
| head {a} {as}   : hmem a (a :: as)
| tail {a b} {bs} : hmem a bs → hmem a (b::bs)

namespace hmem
variables {α : Type u} {γ : list (Type u)}
def lift_r : Π {γ γ' : list (Type u)}, hmem α γ' → hmem α (γ ++ γ')
| [] _ m := m
| (_ :: _) _ m := tail m.lift_r
def lift_l : Π {γ γ' : list (Type u)}, hmem α γ → hmem α (γ ++ γ')
| _ _ head := head
| _ _ (tail r) := tail r.lift_l
end hmem

namespace hlist
def get {i} : Π {is}, hlist is → hmem i is → i
| _ (cons a _) (hmem.head) := a
| _ (cons _ as) (hmem.tail h) := as.get h
def update {i} (v : i) : Π {is}, hlist is → hmem i is → hlist is
| _ (cons _ as) (hmem.head) := v :: as
| _ (cons a as) (hmem.tail h) := a :: (as.update h)

theorem get_update {i} (v : i) : Π {is} (s : hlist is) (m : hmem i is), (s.update v m).get m = v
| _ (cons _ _) (hmem.head) := rfl
| _ (cons _ as) (hmem.tail h) := get_update as h
-- todo: the frame rule (het eq?)
--theorem frame {i j} (v : i) : Π {is} (s : hlist is) (m : hmem i is) (n : hmem j is), m ≠ n → (s.update v m).get n = s.get n := sorry

def append : Π {γ γ' : list (Type u)}, hlist γ → hlist γ' → hlist (γ ++ γ')
| _ _ (hlist.nil) y := y
| _ _ (hlist.cons a as) y := hlist.cons a (as.append y)
local infixr ` ++ `:67 := hlist.append
theorem get_update_append_l {i} (v : i) : Π {γ γ' : list (Type u)} (s : hlist γ) (t : hlist γ') (m : hmem i γ),
((s ++ t).update v m.lift_l) = s.update v m ++ t
:= λ γ γ' s t m,
begin
  induction m,
  { cases s,
    refl, },
  { cases s,
    simp only [append, hmem.lift_l, update],
    split,
    refl,
    apply m_ih,
  }
end
theorem get_update_append_r {i} (v : i) : Π {γ γ' : list (Type u)} (s : hlist γ) (t : hlist γ') (m : hmem i γ'),
((s ++ t).update v m.lift_r) = s ++ t.update v m
:= λ γ γ' s t m,
begin
  induction s,
  { refl },
  { simp only [append, hmem.lift_r, update],
    split,
    refl,
    assumption, }
end
end hlist
