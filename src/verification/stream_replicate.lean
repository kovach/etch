import data.finsupp.basic
import verification.verify
import data.fintype.order

variables {ι α β σ : Type}
[add_zero_class α]
[linear_order ι]
[fintype ι]
[nonempty ι]

def replicate_stream (n : ℕ) (v : α) : StreamExec (fin n.succ) (fin n.succ) α :=
{ bound := n.succ,
  state := 0,
  stream := {
    valid := λ i, i.val < n,
    ready := λ _, true,
    next := λ ⟨i, _⟩ h, ⟨i+1, nat.succ_lt_succ h⟩,
    index := λ i _, i,
    value := λ _ _, v,
  },
}

noncomputable def finsupp.const (v : α) : ι →₀ α := finsupp.equiv_fun_on_fintype.inv_fun $ λ _, v

theorem replicate_spec (n) (v : α) : (replicate_stream n v).eval = finsupp.const v := sorry

-- todo: given any type ι with an order-preserving surjective map from fin n, prove above theorem

-- /- probably not needed: -/ noncomputable instance index.complete : complete_linear_order ι := fintype.to_complete_linear_order_of_nonempty  _.
