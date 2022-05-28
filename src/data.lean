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
inductive hmem : (Type u) → list (Type u) → Type (u+1)
| head {a} {as} : hmem a (a :: as)
| tail {a b} {bs} : hmem a bs → hmem a (b::bs)
namespace hlist
def get {i} : Π {is}, hlist is → hmem i is → i
| _ (cons a as) (hmem.head) := a
| (_ :: is) (cons a as) (hmem.tail h) := as.get h
def update {i} (v : i) : Π {is}, hlist is → hmem i is → hlist is
| _ (cons a as) (hmem.head) := v :: as
| (_ :: is) (cons a as) (hmem.tail h) := a :: (as.update h)
end hlist
