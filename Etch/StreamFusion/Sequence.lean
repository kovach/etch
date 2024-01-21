namespace SeqStream
inductive Step (σ α : Type) where
| done
| ready : σ → α → Step σ α
| skip  : σ → Step σ α

structure Stream (α : Type) where
  σ : Type
  next : (x : σ) → Step σ α
  q : σ

namespace Stream

@[inline] partial def fold (f : β → α → β) (s : Stream α) (q : s.σ) (acc : β) : β :=
  let rec @[specialize] go f (next : (x : s.σ) → Step s.σ α) (acc : β) q :=
    match next q with
    | .done => acc
    | .skip s => go f next acc s
    | .ready s v => go f next (f acc v) s
  go f s.next acc q
end Stream

def ofArray (arr : Array α) : Stream α where
  q := 0
  next q := if h : q < arr.size then .ready (q+1) arr[q] else .done

def eg1 (arr : Array Nat) :=
  let s := ofArray arr
  s.fold (fun a b => a+b) s.q 0

end SeqStream
