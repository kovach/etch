import algebra algebra.group algebra.group.defs logic.relation order.lexicographic
import data
universes u v variables (α β : Type*)
structure iter (σ I V : Type*) :=
  (δ : function.End σ) (ι : σ → I) (ν : σ → V) (ready : σ → bool)
structure stream (σ I V : Type*) := (iter : iter σ I V) (q : σ)
structure var    (σ I V : Type*) := (stream : stream σ I V) (value : V) (init : σ)
namespace iter
variables {σ I V : Type} (a : iter σ I V) (s t : σ) [linear_order I]
def reachable := relation.refl_trans_gen (λ s t, t = a.δ s)
def monotonic := ∀ (s t : σ), a.reachable s t → a.ι s ≤ a.ι t
end iter
namespace stream
variables {σ I V : Type} (s : stream σ I V)
@[simp] def δ (s : stream σ I V) : stream σ I V := { q := s.iter.δ s.q .. s}
@[simp] def ι := s.iter.ι s.q @[simp] def ν := s.iter.ν s.q
@[simp] def ready := s.iter.ready s.q
variables [decidable_eq I] [has_top I] variables [add_monoid V]
def elementary (i : I) (v : V) := λ j, if i = j then v else 0
@[simp] def semantics₁  : I → V := if s.ready && (s.ι ≠ ⊤) then elementary s.ι s.ν else 0
@[simp] def semantics : stream σ I V → ℕ → I → V | _ 0 := 0
| s (n+1) := s.semantics₁ + semantics s.δ n
notation `⟦` s, i `⟧` := s.semantics i
variables [linear_order I]
@[simp] def monotonic := s.iter.monotonic
end stream
namespace var -- stream with a mutable value; represents transient state of nested streams
variables {σ I V : Type} (s : var σ I V)
def δ : var σ I V := { s with stream := s.stream.δ, value := s.stream.δ.ν }
@[simp] def ι := s.stream.ι @[simp] def ν := s.value
def reset : var σ I V := { s with stream := { s.stream with q := s.init } }
end var
variable (v : var ℕ ℕ (var ℕ ℕ ℕ))
inductive E (γ : list Type) : Type → Type 1
| ident {i} : hmem i γ → E i
| value   {σ I V : Type} : E (var σ I V) → E V
| current {σ I V : Type} : E (var σ I V) → E I
-- lens:
def E.get {γ : list Type} (s : hlist γ) : Π {i}, E γ i → i
| _ (E.ident var) := s.get var
| _ (E.value e)   := e.get.ν
| _ (E.current e) := e.get.ι
def E.put {γ : list Type} (s : hlist γ) : Π {i}, E γ i → i → hlist γ
| _ (E.ident var) := λ v, s.update v var
| _ (E.value e) := λ v, e.put { e.get s with value := v }
| _ (E.current e) := λ _, s -- no
def label := string
inductive Prog (γ : list Type) : Type 1
| expr {i} (e : E γ i) : Prog
| accum {V} (f : V → V → V) (dst : E γ V) (val : E γ V) : Prog
| store {i} (dst : E γ i) (val : E γ i) : Prog
| next {σ I V : Type} (stream : E γ (var σ I V)) : Prog
| seq (a b : Prog) : Prog
| skip : Prog
| jump : label → Prog
infixr ` <;> `:1 := Prog.seq
namespace Prog
def blocks (γ : list Type) := label → Prog γ
def step (γ : list Type) (s : hlist γ) (b : blocks γ) : Prog γ → (Prog γ × hlist γ)
| (next e) := (skip, e.put s (e.get s).δ)
| (store dst src) := (skip, dst.put s (src.get s))
| (accum f dst src) := (skip, dst.put s $ f (dst.get s) (src.get s))
| (skip <;> b) := (b, s)
| (a <;> b) := let (a', s') := a.step in (a' <;> b, s')
| (jump l) := (b l, s)
| skip := (skip, s)
| (expr _) := (skip, s) -- todo?
end Prog
