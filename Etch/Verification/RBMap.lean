import Std.Classes.Order
import Std.Data.RBMap
import Std.Data.RBMap.Lemmas

/-!
This file copies the changes from PR #739 (https://github.com/leanprover/std4/pull/739)
by Mario Carneiro. Once that PR is merged, this file should be deleted.
-/

namespace Std
namespace RBNode
open RBColor

attribute [simp] fold foldl foldr Any forM foldlM Ordered

theorem min?_mem {t : RBNode α} (h : t.min? = some a) : a ∈ t := by
  rw [min?_eq_toList_head?] at h
  rw [← mem_toList]
  revert h; cases toList t <;> rintro ⟨⟩; constructor

theorem Ordered.min?_le {t : RBNode α} [TransCmp cmp] (ht : t.Ordered cmp) (h : t.min? = some a)
    (x) (hx : x ∈ t) : cmp a x ≠ .gt := by
  rw [min?_eq_toList_head?] at h
  rw [← mem_toList] at hx
  have := ht.toList_sorted
  revert h hx this; cases toList t <;> rintro ⟨⟩ (_ | ⟨_, hx⟩) (_ | ⟨h1,h2⟩)
  · rw [OrientedCmp.cmp_refl (cmp := cmp)]; decide
  · rw [(h1 _ hx).1]; decide

theorem max?_mem {t : RBNode α} (h : t.max? = some a) : a ∈ t := by
  simpa using min?_mem ((min?_reverse _).trans h)

theorem Ordered.le_max? {t : RBNode α} [TransCmp cmp] (ht : t.Ordered cmp) (h : t.max? = some a)
    (x) (hx : x ∈ t) : cmp x a ≠ .gt :=
  ht.reverse.min?_le ((min?_reverse _).trans h) _ (by simpa using hx)

end RBNode


open RBNode (IsCut IsStrictCut)

namespace RBSet


theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {t : RBSet α cmp} :
    t.forM (m := m) f = t.toList.forM f := RBNode.forM_eq_forM_toList

theorem isEmpty_iff_toList_eq_nil {t : RBSet α cmp} :
    t.isEmpty ↔ t.toList = [] := by obtain ⟨⟨⟩, _⟩ := t <;> simp [toList, isEmpty]

theorem findP?_some_eq_eq {t : RBSet α cmp} : t.findP? cut = some y → cut y = .eq :=
  RBNode.find?_some_eq_eq

theorem findP?_some_mem_toList {t : RBSet α cmp} (h : t.findP? cut = some y) : y ∈ toList t :=
  mem_toList.2 <| RBNode.find?_some_mem h

theorem findP?_some_memP {t : RBSet α cmp} (h : t.findP? cut = some y) : t.MemP cut :=
  RBNode.find?_some_memP h

theorem findP?_some [@TransCmp α cmp] [IsStrictCut cmp cut] {t : RBSet α cmp} :
    t.findP? cut = some y ↔ y ∈ toList t ∧ cut y = .eq :=
  t.2.out.1.find?_some.trans <| by simp [mem_toList]

theorem memP_iff_findP? [@TransCmp α cmp] [IsCut cmp cut] {t : RBSet α cmp} :
    MemP cut t ↔ ∃ y, t.findP? cut = some y := t.2.out.1.memP_iff_find?

theorem findP?_insert_of_eq [@TransCmp α cmp] [IsStrictCut cmp cut]
    (t : RBSet α cmp) (h : cut v = .eq) : (t.insert v).findP? cut = some v :=
  findP?_some.2 ⟨mem_toList_insert_self .., h⟩

theorem findP?_insert_of_ne [@TransCmp α cmp] [IsStrictCut cmp cut]
    (t : RBSet α cmp) (h : cut v ≠ .eq) : (t.insert v).findP? cut = t.findP? cut := by
  refine Option.ext fun u =>
    findP?_some.trans <| .trans (and_congr_left fun h' => ?_) findP?_some.symm
  rw [mem_toList_insert, or_iff_left, and_iff_left]
  · exact mt (fun h => by rwa [IsCut.congr (cut := cut) (find?_some_eq_eq h)]) h
  · rintro rfl; contradiction

theorem findP?_insert [@TransCmp α cmp] (t : RBSet α cmp) (v cut) [IsStrictCut cmp cut] :
    (t.insert v).findP? cut = if cut v = .eq then some v else t.findP? cut := by
  split <;> [exact findP?_insert_of_eq t ‹_›; exact findP?_insert_of_ne t ‹_›]

theorem isEmpty_iff_eq_empty {α : Type _} {cmp : α → α → Ordering} (t : RBSet α cmp) : t.isEmpty ↔ t = ∅ := by
  obtain ⟨⟨⟩, _⟩ := t <;>
  simp [isEmpty]
  · rfl
  · change _ ≠ Subtype.mk _ _
    simp

@[simp] theorem findP?_empty (v : α) (cut : α → Ordering) :
  (∅ : RBSet α cmp).findP? cut = none := rfl

end RBSet

namespace RBMap

-- @[simp] -- FIXME: RBSet.val_toList already triggers here, seems bad?
theorem val_toList {t : RBMap α β cmp} : t.1.toList = t.toList := rfl

@[simp] theorem mkRBSet_eq : mkRBMap α β cmp = ∅ := rfl
@[simp] theorem empty_eq : @RBMap.empty α β cmp = ∅ := rfl
@[simp] theorem default_eq : (default : RBMap α β cmp) = ∅ := rfl
@[simp] theorem empty_toList : toList (∅ : RBMap α β cmp) = [] := rfl
@[simp] theorem single_toList : toList (single a b : RBMap α β cmp) = [(a, b)] := rfl

theorem mem_toList {t : RBMap α β cmp} : x ∈ toList t ↔ x ∈ t.1 := RBNode.mem_toList

theorem foldl_eq_foldl_toList {t : RBMap α β cmp} :
    t.foldl f init = t.toList.foldl (fun r p => f r p.1 p.2) init :=
  RBNode.foldl_eq_foldl_toList

theorem foldr_eq_foldr_toList {t : RBMap α β cmp} :
    t.foldr f init = t.toList.foldr (fun p r => f p.1 p.2 r) init :=
  RBNode.foldr_eq_foldr_toList

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {t : RBMap α β cmp} :
    t.foldlM (m := m) f init = t.toList.foldlM (fun r p => f r p.1 p.2) init :=
  RBNode.foldlM_eq_foldlM_toList

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {t : RBMap α β cmp} :
    t.forM (m := m) f = t.toList.forM (fun p => f p.1 p.2) :=
  RBNode.forM_eq_forM_toList

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m] {t : RBMap α β cmp} :
    forIn (m := m) t init f = forIn t.toList init f := RBNode.forIn_eq_forIn_toList

theorem toStream_eq {t : RBMap α β cmp} : toStream t = t.1.toStream .nil := rfl

@[simp] theorem toStream_toList {t : RBMap α β cmp} : (toStream t).toList = t.toList :=
  RBSet.toStream_toList

theorem toList_sorted {t : RBMap α β cmp} : t.toList.Pairwise (RBNode.cmpLT (cmp ·.1 ·.1)) :=
  RBSet.toList_sorted

theorem findEntry?_some_eq_eq {t : RBMap α β cmp} : t.findEntry? x = some (y, v) → cmp x y = .eq :=
  RBSet.findP?_some_eq_eq

theorem findEntry?_some_mem_toList {t : RBMap α β cmp} (h : t.findEntry? x = some y) :
    y ∈ toList t := RBSet.findP?_some_mem_toList h

theorem find?_some_mem_toList {t : RBMap α β cmp} (h : t.find? x = some v) :
    ∃ y, (y, v) ∈ toList t ∧ cmp x y = .eq := by
  obtain ⟨⟨y, v⟩, h', rfl⟩ := Option.map_eq_some'.1 h
  exact ⟨_, findEntry?_some_mem_toList h', findEntry?_some_eq_eq h'⟩

theorem mem_toList_unique [@TransCmp α cmp] {t : RBMap α β cmp}
    (hx : x ∈ toList t) (hy : y ∈ toList t) (e : cmp x.1 y.1 = .eq) : x = y :=
  RBSet.mem_toList_unique hx hy e

/-- A "representable cut" is one generated by `cmp a` for some `a`. This is always a valid cut. -/
instance (cmp) (a : α) : IsStrictCut cmp (cmp a) where
  le_lt_trans h₁ h₂ := TransCmp.lt_le_trans h₂ h₁
  le_gt_trans h₁ := Decidable.not_imp_not.1 (TransCmp.le_trans · h₁)
  exact h := (TransCmp.cmp_congr_left h).symm

instance (f : α → β) (cmp) [@TransCmp β cmp] (x : β) :
    IsStrictCut (Ordering.byKey f cmp) (fun y => cmp x (f y)) where
  le_lt_trans h₁ h₂ := TransCmp.lt_le_trans h₂ h₁
  le_gt_trans h₁ := Decidable.not_imp_not.1 (TransCmp.le_trans · h₁)
  exact h := (TransCmp.cmp_congr_left h).symm

theorem findEntry?_some [@TransCmp α cmp] {t : RBMap α β cmp} :
    t.findEntry? x = some y ↔ y ∈ toList t ∧ cmp x y.1 = .eq := RBSet.findP?_some

theorem find?_some [@TransCmp α cmp] {t : RBMap α β cmp} :
    t.find? x = some v ↔ ∃ y, (y, v) ∈ toList t ∧ cmp x y = .eq := by
  simp [find?, findEntry?_some]; constructor
  · rintro ⟨_, h, rfl⟩; exact ⟨_, h⟩
  · rintro ⟨b, h⟩; exact ⟨_, h, rfl⟩

theorem contains_iff_findEntry? {t : RBMap α β cmp} :
    t.contains x ↔ ∃ v, t.findEntry? x = some v := Option.isSome_iff_exists

theorem contains_iff_find? {t : RBMap α β cmp} :
    t.contains x ↔ ∃ v, t.find? x = some v := by
  simp [contains_iff_findEntry?, find?, and_comm, exists_comm]

theorem size_eq (t : RBMap α β cmp) : t.size = t.toList.length := RBNode.size_eq

theorem mem_toList_insert_self (v) (t : RBMap α β cmp) : (k, v) ∈ toList (t.insert k v) :=
  RBSet.mem_toList_insert_self ..

theorem mem_toList_insert_of_mem (v) {t : RBMap α β cmp} (h : y ∈ toList t) :
    y ∈ toList (t.insert k v) ∨ cmp k y.1 = .eq := RBSet.mem_toList_insert_of_mem _ h

theorem mem_toList_insert [@TransCmp α cmp] {t : RBMap α β cmp} :
    y ∈ toList (t.insert k v) ↔ (y ∈ toList t ∧ t.findEntry? k ≠ some y) ∨ y = (k, v) :=
  RBSet.mem_toList_insert

theorem findEntry?_congr [@TransCmp α cmp] (t : RBMap α β cmp) (h : cmp k₁ k₂ = .eq) :
    t.findEntry? k₁ = t.findEntry? k₂ := by simp [findEntry?, TransCmp.cmp_congr_left' h]

theorem find?_congr [@TransCmp α cmp] (t : RBMap α β cmp) (h : cmp k₁ k₂ = .eq) :
    t.find? k₁ = t.find? k₂ := by simp [find?, findEntry?_congr _ h]

theorem findEntry?_insert_of_eq [@TransCmp α cmp] (t : RBMap α β cmp) (h : cmp k' k = .eq) :
    (t.insert k v).findEntry? k' = some (k, v) := RBSet.findP?_insert_of_eq _ h

theorem find?_insert_of_eq [@TransCmp α cmp] (t : RBMap α β cmp) (h : cmp k' k = .eq) :
    (t.insert k v).find? k' = some v := by rw [find?, findEntry?_insert_of_eq _ h]; rfl

theorem findEntry?_insert_of_ne [@TransCmp α cmp] (t : RBMap α β cmp) (h : cmp k' k ≠ .eq) :
    (t.insert k v).findEntry? k' = t.findEntry? k' := RBSet.findP?_insert_of_ne _ h

theorem find?_insert_of_ne [@TransCmp α cmp] (t : RBMap α β cmp) (h : cmp k' k ≠ .eq) :
    (t.insert k v).find? k' = t.find? k' := by simp [find?, findEntry?_insert_of_ne _ h]

theorem findEntry?_insert [@TransCmp α cmp] (t : RBMap α β cmp) (k v k') :
    (t.insert k v).findEntry? k' = if cmp k' k = .eq then some (k, v) else t.findEntry? k' :=
  RBSet.findP?_insert ..

theorem find?_insert [@TransCmp α cmp] (t : RBMap α β cmp) (k v k') :
    (t.insert k v).find? k' = if cmp k' k = .eq then some v else t.find? k' := by
  split <;> [exact find?_insert_of_eq t ‹_›; exact find?_insert_of_ne t ‹_›]

/- This section is not present in the original file and should not be deleted -/
section custom

variable {α β : Type _}

@[simp] theorem find?_insert_self [@TransCmp α cmp] (t : RBMap α β cmp) :
    (t.insert k v).find? k = some v := by rw [find?_insert_of_eq]; rw [OrientedCmp.cmp_refl (cmp := cmp)]

theorem findD_insert [@TransCmp α cmp] (t : RBMap α β cmp) (k v k') (d : β) :
    (t.insert k v).findD k' d = if cmp k' k = .eq then v else t.findD k' d := by
  simp only [findD, find?_insert]; split <;> rfl

@[simp] theorem findD_insert_self [@TransCmp α cmp] (t : RBMap α β cmp) (d : β) :
    (t.insert k v).findD k d = v := by simp [findD]

theorem findD_insert_of_ne [@TransCmp α cmp] (t : RBMap α β cmp) (h : cmp k' k ≠ .eq) (d : β) :
    (t.insert k v).findD k' d = t.findD k' d := by simp [findD_insert, h]

@[simp] theorem findEntry?_empty (k : α) : (∅ : RBMap α β cmp).findEntry? k = none := rfl

@[simp] theorem find?_empty (k : α) : (∅ : RBMap α β cmp).find? k = none := rfl

@[simp] theorem findD_empty (k : α) (d : β) : (∅ : RBMap α β cmp).findD k d = d := rfl

end custom


end RBMap

end Std
