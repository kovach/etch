import data.fintype.basic
import data.finset.basic

variables {α β : Type*} 

@[simp] lemma finset.bUnion_fin2 [decidable_eq α] (f : fin 2 → finset α) :
  finset.bUnion finset.univ f = (f 0) ∪ (f 1) :=
by { ext, simp [fin.exists_fin_two], }

lemma set.preimage_insert (f : α → β) (S : set β) (x : β) :
  f⁻¹' (insert x S) = f⁻¹' ({x} : set β) ∪ f⁻¹' S := by { ext, simp, } 