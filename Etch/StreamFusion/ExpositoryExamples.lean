import Etch.StreamFusion.Sublist

/-
  this file contains several expository stream definition
  with code samples for the paper
-/
import Mathlib.Tactic
import Mathlib.Data.Pi.Algebra

namespace one

inductive Step (σ α : Type)
| done
| skip (state : σ)
| emit (state : σ) (value : α)

structure Stream (α : Type) where
  σ : Type
  q : σ
  next : σ → Step σ α

namespace Stream

open Step
def map (f : α → β) (s : Stream α) : Stream β where
  q := s.q
  next state := match s.next state with
    | done             => done
    | skip state       => skip state
    | emit state value => emit state (f value)

partial def eval : Stream α → List α := fun {q, next} =>
  match next q with
  | done => []
  | skip q => eval {q, next}
  | emit q value => value :: eval {q, next}

partial def eval' : Stream α → Array α :=
  let rec go (acc : Array α) (s : Stream α) : Array α :=
    let {q, next} := s
    match next q with
    | done => acc
    | skip state => go acc {q := state, next}
    | emit state value => go (acc.push value) {q := state, next}
  go #[]

@[inline] partial def fold (f : β → α → β) (s : Stream α) (q : s.σ) (acc : β) : β :=
  let rec @[specialize] go f (next : (x : s.σ) → Step s.σ α) (acc : β) q :=
    match next q with
    | .done => acc
    | .skip s => go f next acc s
    | .emit s v => go f next (f acc v) s
  go f s.next acc q
end Stream

end one

variable {ι : Type} [DecidableEq ι]

def zero : ι → Option α := fun _ => none

def singleton (i : ι) (v : α) : ι → Option α :=
  fun x => if x = i then some v else none

namespace two
inductive Step (σ ι α : Type) where
  | done
  | skip (state : σ)
  | emit (state : σ) (index : ι) (value : α)
open Step

structure Stream (ι : Type) (α : Type) where
  σ : Type
  q : σ
  next : σ → Step σ ι α

def ofArray (arr : Array α) : Stream Nat α where
  q := 0
  next q := if h : q < arr.size then .emit (q+1) q arr[q] else .done

instance [Add α] : Add (Option α) where
  add a b := match a, b with
  | none, b => b
  | a, none => a
  | some a, some b => some (a + b)

variable [Ord ι] [Mul α]

def mul [Mul α] (a b : Stream ι α) : Stream ι α where
  q := (a.q, b.q)
  next q := match a.next q.fst, b.next q.snd with
    | done, _                     => done
    | _, done                     => done
    | skip q₁, _                  => skip (q₁, q.snd)
    | _, skip q₂                  => skip (q.fst, q₂)
    | emit q₁ i₁ v₁,
      emit q₂ i₂ v₂ =>
      match compare i₁ i₂ with
      | .lt                       => skip (q₁, q.snd)
      | .gt                       => skip (q.fst, q₂)
      | .eq                       => emit (q₁, q₂) i₁ (v₁ * v₂)

instance : Mul (Stream ι α) := ⟨mul⟩
variable  [Zero α] [Add α]

partial def eval [Add α] : Stream ι α → (ι → Option α) :=
  fun {q, next} =>
    match next q with
    | done => zero
    | skip q => eval {q, next}
    | emit q i v => (singleton i v) + eval {q, next}

#eval eval (ofArray #[1,3] * ofArray #[2,6]) 1

end two

namespace three

-- maybe
structure Stream' (ι : Type) (α : Type u) where
  σ : Type
  -- the `valid` states are those at which `next` and `index` are defined
  valid : σ → Bool
  -- the `ready` states are those states where additionally `value` is defined
  ready : σ → Bool
  -- the next function splits into three parts:
  next  : (q : σ) → valid q → σ
  index : (q : σ) → valid q → ι
  value : (q : σ) → ready q → α

structure Stream (ι α : Type) where
  (σ : Type) (q : σ)
  valid : σ → Bool               -- "done"
  ready : {x // valid x} → Bool  -- "skip"
  index : {x // valid x} → ι
  value : {x // ready x} → α
  next  : {x // valid x} → σ     -- "emit"


end three

namespace four
structure Stream (ι α : Type) where
  (σ : Type) (q : σ)
  valid : σ → Bool
  ready : {x // valid x} → Bool
  index : {x // valid x} → ι
  value : {x // ready x} → α
  seek  : {x // valid x} → ι → Bool → σ  -- replaces `next`:

partial def eval [Add α] (s : Stream ι α) : (ι → Option α) :=
  if valid : s.valid s.q then
    let q := ⟨s.q, valid⟩
    let ready := s.ready q
    let index := s.index q
    -- next state
    let q' := s.seek q index ready
    -- current value to emit
    let current :=
      if ready : ready
        then let value := (s.value ⟨q, ready⟩)
             singleton index value
        else zero
    -- evaluate the remaining stream
    let rest := eval {s with q := q'}
    -- end result:
    current + rest
  else zero

end four

namespace five

-- todo?
structure StreamI (ι : Type) : Type 1 where
  (σ : Type) (q : σ)
  valid : σ → Bool
  ready : {x // valid x} → Bool
  index : {x // valid x} → ι
  seek  : {x // valid x} → ι → Bool → σ  -- replaces `next`:

inductive Stream : List Type → Type → Type 1
| scalar : Stream [] v
| level {ι} (level : StreamI ι) (rest : Stream is v) : Stream (ι :: is) v
| fun {ι} (f : ι → Stream is v) : Stream (ι :: is) v

end five

#exit

inductive Step (σ ι α : Type) where
  | done
  | skip (state : σ)
  | emit (state : σ) (index : ι) (value : α)
open Step

structure Stream (ι : Type) (α : Type) where
  σ : Type
  q : σ
  seek : σ → ι → Bool → Step σ ι α

partial def eval [Add α] : Stream ι α → (ι → Option α) :=
  fun {q, seek} =>
    match seek q _ _ with
    | done => zero
    | skip q => eval {q, seek}
    | emit q i v => (singleton i v) + eval {q, seek}

end three

#exit

-- In analogy with streams representing sequences, we define the type of streams
-- representing sequences of (ι × α) pairs, ordered by ι,
-- which admit efficient `seek` up to or past a given index.

-- This pair of definitions is not used, but they are one logical step between "Stream Fusion" and Stream below

def ofArray (arr : Array α) : Stream α where
  q := 0
  next q := if h : q < arr.size then .emit (q+1) arr[q] else .done

def eg1 (arr : Array Nat) :=
  let s := ofArray arr
  s.fold (fun a b => a+b) s.q 0
