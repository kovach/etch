

structure BoundedStream (σ ι α : Type) :=
(next  : σ → σ)
(index : σ → ι)
(value : σ → α)
(ready : σ → bool)
(valid : σ → bool)
(state : σ)
(bound : ℕ)



